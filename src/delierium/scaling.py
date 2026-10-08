"""Scaling symmetries by linear algebra on the exponents (#48).

A scaling x_i -> l**a_i x_i, u_j -> l**b_j u_j maps a derivative
d^alpha u_j to l**(b_j - alpha.a) d^alpha u_j, so every term of an
equation gets a weight, linear in (a, b). The equation is invariant when
all its terms have the same weight (it is multiplied by a power of l):
a linear system for the exponents, without the determining equations.
Dimensional analysis (Buckingham's Pi theorem) is the special case of
physical dimensions (Bluman-Kumei ch. 1; Bluman-Anco 1.4).

Inside a function other than a power (exp, sin, an arbitrary F, ...) the
arguments have to be invariant, weight 0; a power with an exponent that
depends on the variables needs base and exponent of weight 0. Symbolic
exponents (u**n) and coefficients are taken for generic values: special
values of them may allow more scalings.
"""

from collections.abc import Iterable
from functools import reduce
from typing import Any, cast

from sympy import (
    Abs,
    Add,
    Basic,
    Derivative,
    Expr,
    Function,
    Matrix,
    Mul,
    Pow,
    Symbol,
    cancel,
    denom,
    gcd_list,
    lcm_list,
    sympify,
    together,
)
from sympy.core.function import AppliedUndef

__all__ = ["scaling_symmetries"]


def scaling_symmetries(
    equations: Expr | Iterable[Expr],
    dependent: Basic | Iterable[Basic],
    independent: Basic | Iterable[Basic],
) -> list[tuple[Expr, ...]]:
    """A basis of the scaling symmetries of the equations (= 0) as
    generators: tuples of components, the independent variables first,
    then the dependent ones as plain symbols (u for u(x, t)), as for
    verify_symmetry.

    KdV u_t + u u_x + u_xxx = 0: x d/dx + 3 t d/dt - 2 u d/du.

    >>> from sympy import symbols
    >>> x, t = symbols("x t")
    >>> u = Function("u")(x, t)
    >>> scaling_symmetries(u.diff(t) + u * u.diff(x) + u.diff(x, 3), u, [x, t])
    [(x, 3*t, -2*u)]

    The porous medium equation u_t = (u**n u_x)_x for generic n: two scalings.

    >>> n = Symbol("n")
    >>> for g in scaling_symmetries(u.diff(t) - (u**n * u.diff(x)).diff(x), u, [x, t]):
    ...     print(g)
    (x, 2*t, 0)
    (n*x, 0, 2*u)
    """
    eqs: list[Expr] = (
        [sympify(equations)] if isinstance(equations, Basic) else [sympify(e) for e in equations]
    )
    dep = [dependent] if isinstance(dependent, Basic) else list(dependent)
    indep = [independent] if isinstance(independent, Basic) else list(independent)
    weights = _Weights(indep, dep)
    for eq in eqs:
        weights.of(eq.doit())  # the constraints of every subexpression, the sum homogeneous
    unknowns = len(indep) + len(dep)
    rows = [[form.get(k, 0) for k in range(unknowns)] for form in weights.constraints]
    basis = (
        Matrix(rows).nullspace() if rows else [Matrix.eye(unknowns)[:, k] for k in range(unknowns)]
    )
    coordinates = [*indep, *(Symbol(d.func.__name__) for d in dep)]
    result = []
    for vector in basis:
        vector = _primitive([cancel(v) for v in vector])
        result.append(tuple(v * z for v, z in zip(vector, coordinates, strict=True)))
    return result


class _Weights:
    """Weights (linear forms {unknown index: coefficient} in a_1..a_n,
    b_1..b_m) of expressions, collecting the constraints (forms that must
    vanish)."""

    def __init__(self, independent: list[Basic], dependent: list[Basic]) -> None:
        self.independent = independent
        self.dependent = dependent
        self.constraints: list[dict[int, Expr]] = []

    def of(self, e: Expr) -> dict[int, Expr]:
        variable = self._of_variable(e)
        if variable is not None:
            return variable
        if not e.has(*self.independent, *self.dependent):
            return {}  # numbers and parameters
        if isinstance(e, Add):
            forms = [self.of(t) for t in e.args]
            for form in forms[1:]:
                self._require(_add(form, _scale(forms[0], -1)))
            return forms[0]
        if isinstance(e, Mul):
            return reduce(_add, (self.of(factor) for factor in e.args), {})
        return self._of_power(e) if isinstance(e, Pow) else self._of_function(e)

    def _of_power(self, e: Pow) -> dict[int, Expr]:
        if not e.exp.has(*self.independent, *self.dependent):
            return _scale(self.of(e.base), e.exp)
        self._require(self.of(e.base))  # b**u, u**v: base and exponent invariant
        self._require(self.of(e.exp))
        return {}

    def _of_variable(self, e: Expr) -> dict[int, Expr] | None:
        """The weight of a variable or a derivative, else None."""
        if e in self.independent:
            return {self.independent.index(e): sympify(1)}
        if e in self.dependent:
            return {len(self.independent) + self.dependent.index(e): sympify(1)}
        if isinstance(e, Derivative) and e.expr in self.dependent:
            form = self.of(cast(Expr, e.expr))
            for z, count in cast(Any, e.variable_count):
                form = _add(form, _scale(self.of(z), -count))
            return form
        return None

    def _of_function(self, e: Expr) -> dict[int, Expr]:
        if isinstance(e, Abs):
            return self.of(cast(Expr, e.args[0]))  # for l > 0
        if isinstance(e, Derivative):  # k'(u) of an arbitrary k: like k(u)
            e = cast(Expr, e.expr)
        if isinstance(e, (Function, AppliedUndef)):
            for argument in e.args:
                self._require(self.of(cast(Expr, argument)))
            return {}
        raise NotImplementedError(f"weight of {e} under scalings")

    def _require(self, form: dict[int, Expr]) -> None:
        form = {k: v for k, v in form.items() if cancel(v) != 0}
        if form:
            self.constraints.append(form)


def _add(f: dict[int, Expr], g: dict[int, Expr]) -> dict[int, Expr]:
    result = dict(f)
    for k, v in g.items():
        result[k] = result.get(k, 0) + v
    return result


def _scale(f: dict[int, Expr], c: Any) -> dict[int, Expr]:
    return {k: c * v for k, v in f.items()}


def _primitive(vector: list[Expr]) -> list[Expr]:
    """vector times a common factor: no denominators, no common content,
    the first nonzero entry without a minus sign ((x, 0, 2u/n): (n x, 0, 2u))."""
    vector = [together(v) for v in vector]
    denominator = lcm_list([denom(v) for v in vector])
    numerators = [cancel(v * denominator) for v in vector]
    content = gcd_list([v for v in numerators if v != 0])
    numerators = [cancel(v / content) for v in numerators]
    first = next(v for v in numerators if v != 0)
    return [-v for v in numerators] if first.could_extract_minus_sign() else numerators
