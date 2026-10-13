"""Similarity reduction of a PDE by a given generator (#15).

The solutions invariant under X: n - 1 invariants of X, the similarity
variables zeta, are free of the dependent variables, the others w (one per
dependent variable) contain them. w = F(zeta) solved for the dependent
variables and substituted gives a PDE in one independent variable less, an
ODE for two independent variables (Hydon 9.1, Bluman-Anco 4.2.1, Olver 3.1).

The new equation comes out in the original variables first; the similarity
variables are then solved for all independent variables but one, and the
equation is divided by the factors free of F (and, if that does not remove
the last original variable, by the coefficient of the highest derivative of
F)."""

import random
from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from sympy import (
    Add,
    Basic,
    Derivative,
    Dummy,
    Eq,
    Expr,
    Function,
    Mul,
    Symbol,
    expand,
    expand_log,
    expand_power_base,
    factor,
    factor_terms,
    fraction,
    nan,
    powdenest,
    powsimp,
    simplify,
    solve,
    sympify,
    together,
    zoo,
)
from sympy.core.function import AppliedUndef

from delierium.helpers import plain_symbol
from delierium.invariants import Generator, invariants

__all__ = ["SimilarityReduction", "similarity_reduction"]


@dataclass(frozen=True)
class SimilarityReduction:
    """The result of similarity_reduction.

    equations: the reduced equations (= 0) for functions in variables
    functions: the new dependent functions F(zeta)
    variables: the new independent variables (symbols zeta)
    similarity_variables: zeta in the original independent variables
    ansatz: the invariant solutions, u = ... in F(zeta) and the original
        independent variables

    >>> from sympy import Function, symbols
    >>> x, t, c = symbols("x t c")
    >>> u = Function("u")(x, t)
    >>> kdv = u.diff(t) + u * u.diff(x) + u.diff(x, 3)
    >>> r = similarity_reduction(kdv, (c, 1, 0), u, [x, t])
    >>> r.variables, r.functions, r.similarity_variables
    ([zeta], [F(zeta)], [-c*t + x])
    """

    equations: list[Expr]
    functions: list[Expr]
    variables: list[Symbol]
    similarity_variables: list[Expr]
    ansatz: list[Eq]


def similarity_reduction(
    equations: Expr | Iterable[Expr],
    generator: Generator,
    dependent: Expr | Sequence[Expr],
    independent: Sequence[Symbol],
) -> SimilarityReduction:
    """Reduce the PDE (or system) equations = 0 by the generator, given by
    its components in the independent variables, then in the dependent ones
    (plain symbols named like the dependent functions), or as a VectorField
    in these coordinates.

    The heat equation by d/dx + u d/du: u = exp(x) F(t), F' = F:

    >>> from sympy import Function, symbols
    >>> x, t, u_ = symbols("x t u")
    >>> u = Function("u")(x, t)
    >>> r = similarity_reduction(u.diff(t) - u.diff(x, 2), (1, 0, u_), u, [x, t])
    >>> r.similarity_variables, r.ansatz
    ([t], [Eq(u(x, t), F(t)*exp(x))])
    >>> r.equations
    [-F(zeta) + Derivative(F(zeta), zeta)]
    """
    equations = [equations] if isinstance(equations, Basic) else list(equations)
    functions = [dependent] if isinstance(dependent, Expr) else list(dependent)
    variables = list(independent)
    if len(variables) < 2:
        raise ValueError("similarity reduction needs two or more independent variables")
    names = [plain_symbol(f) for f in functions]
    found = invariants(generator, [*variables, *names])
    zetas = [e for e in found if not e.has(*names)]
    ws = [e for e in found if e.has(*names)]
    if len(zetas) != len(variables) - 1 or len(ws) != len(functions):
        raise NotImplementedError(f"no similarity variables among the invariants {found}")
    return _Reduction(equations, functions, variables, names, zetas, ws).result()


class _Reduction:  # pylint: disable=too-few-public-methods,too-many-instance-attributes
    """The reduction of the equations by w = F(zeta): the variables
    replaced by positive ones (_x), the dependent functions by their values
    in F.

    >>> from sympy import Function, symbols
    >>> x, t, u_ = symbols("x t u")
    >>> u = Function("u")(x, t)
    >>> heat = _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t / x**2], [u_])
    >>> heat.variables, heat.zetas, heat.F
    ([_x, _t], [_t/_x**2], [F(zeta)])
    >>> heat.values
    {u(_x, _t): F(zeta)}
    """

    def __init__(  # pylint: disable=too-many-arguments,too-many-positional-arguments
        self,
        equations: list[Expr],
        functions: list[Expr],
        variables: list[Symbol],
        names: list[Symbol],
        zetas: list[Expr],
        ws: list[Expr],
    ) -> None:
        """The equations, the dependent functions and the variables; names:
        plain symbols for the functions, zetas and ws: the invariants free of
        them and containing them.

        >>> from sympy import Function, exp, symbols
        >>> x, t, u_ = symbols("x t u")
        >>> u = Function("u")(x, t)
        >>> _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t], [u_ * exp(-x)]).values
        {u(_x, _t): F(zeta)*exp(_x)}
        """
        # locally positive variables: x/sqrt(t) = zeta solved for t
        local: dict[Basic, Basic] = {v: Dummy(str(v), positive=True) for v in variables}
        self.back = {d: v for v, d in local.items()}
        self.variables = [local[v] for v in variables]
        self.zetas: list[Expr] = [z.xreplace(local) for z in zetas]
        # the new names differ from the symbols and functions of the equations
        taken = [
            *variables,
            *set().union(*(e.free_symbols for e in equations)),
            *{plain_symbol(f) for e in equations for f in e.atoms(AppliedUndef)},
        ]
        self.symbols = [Symbol(n) for n in _new_names("zeta", len(zetas), taken)]
        self.F: list[Expr] = [
            Function(n)(*self.symbols)  # pylint: disable=not-callable
            for n in _new_names("F", len(functions), taken)
        ]
        values = solve(
            [w.xreplace(local) - f for w, f in zip(ws, self.F, strict=True)], names, dict=True
        )
        if not values:
            raise NotImplementedError(f"the invariants {ws} not solved for {names}")
        self.functions: list[Expr] = [f.xreplace(local) for f in functions]
        self.values: dict[Expr, Expr] = {
            f: values[0][n] for f, n in zip(self.functions, names, strict=True)
        }
        # (u**2 u_x)_x: the outer derivative evaluated first
        self.equations: list[Expr] = [e.doit().xreplace(local) for e in equations]

    def _total(self, f: Expr, x: Basic) -> Expr:
        """D_x f for f in the variables, zeta and F(zeta).

        >>> from sympy import Function, symbols
        >>> x, t, u_ = symbols("x t u")
        >>> u = Function("u")(x, t)
        >>> heat = _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t / x**2], [u_])
        >>> _x = heat.variables[0]
        >>> heat._total(heat.F[0], _x)
        -2*_t*Derivative(F(zeta), zeta)/_x**3
        """
        return f.diff(x) + sum(
            (z.diff(x) * f.diff(s) for z, s in zip(self.zetas, self.symbols, strict=True)),
            start=0,
        )

    def _substituted(self, e: Expr) -> Expr:
        """e with the dependent functions and their derivatives replaced.

        >>> from sympy import Function, symbols
        >>> x, t, u_ = symbols("x t u")
        >>> u = Function("u")(x, t)
        >>> heat = _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t / x**2], [u_])
        >>> heat._substituted(heat.equations[0])  # doctest: +NORMALIZE_WHITESPACE
        -4*_t**2*Derivative(F(zeta), (zeta, 2))/_x**6 - 6*_t*Derivative(F(zeta), zeta)/_x**4 +
        Derivative(F(zeta), zeta)/_x**2
        """
        replacements: dict[Basic, Expr] = {}
        for d in e.atoms(Derivative):
            if d.expr not in self.values:
                continue
            value = self.values[d.expr]
            for v, n in d.variable_count:
                for _ in range(n):
                    value = self._total(value, v)
            replacements[d] = value
        return e.xreplace(replacements).xreplace(self.values)

    def result(self) -> SimilarityReduction:
        """The SimilarityReduction, in the original variables.

        >>> from sympy import Function, symbols
        >>> x, t, u_ = symbols("x t u")
        >>> u = Function("u")(x, t)
        >>> heat = _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t / x**2], [u_])
        >>> r = heat.result()
        >>> r.similarity_variables, r.ansatz
        ([t/x**2], [Eq(u(x, t), F(t/x**2))])
        """
        substituted = [self._substituted(e) for e in self.equations]
        for k in reversed(range(len(self.variables))):
            reduced = self._eliminate(substituted, k)
            if reduced is not None:
                break
        else:
            raise NotImplementedError("the equations do not reduce: not invariant under X?")
        on_zeta = dict(zip(self.symbols, self.zetas, strict=True))
        return SimilarityReduction(
            reduced,
            self.F,
            self.symbols,
            [z.xreplace(self.back) for z in self.zetas],
            [
                Eq(f.xreplace(self.back), simplify(v.subs(on_zeta)).xreplace(self.back))
                for f, v in self.values.items()
            ],
        )

    def _eliminate(self, substituted: list[Expr], k: int) -> list[Expr] | None:
        """The equations in zeta: all variables but the k-th solved from the
        similarity variables; None if the k-th one remains.

        >>> from sympy import Function, symbols
        >>> x, t, u_ = symbols("x t u")
        >>> u = Function("u")(x, t)
        >>> heat = _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t / x**2], [u_])
        >>> heat._eliminate(
        ...     [heat._substituted(heat.equations[0])], 1
        ... )  # doctest: +NORMALIZE_WHITESPACE
        [4*zeta**2*Derivative(F(zeta), (zeta, 2)) + 6*zeta*Derivative(F(zeta), zeta) -
        Derivative(F(zeta), zeta)]
        """
        others = [v for i, v in enumerate(self.variables) if i != k]
        solutions = solve(
            [z - s for z, s in zip(self.zetas, self.symbols, strict=True)], others, dict=True
        )
        for solution in solutions[:2]:
            reduced = []
            for q in substituted:
                e = q.subs(solution)
                r = _free_of(self.variables, _normalized(e, self.F))
                if r is None:
                    r = self._by_evaluation(e, self.variables[k])
                if r is None:
                    break
                reduced.append(r)
            else:
                return reduced
        return None

    def _by_evaluation(self, e: Expr, x: Basic) -> Expr | None:
        """e = g(x, zeta) R(zeta, F) when the powers of x do not cancel
        symbolically ((-(1 - zeta F')/x)**k next to ((zeta F' - 1)/x)**k):
        R = e at x = 1 (or 2), if e / R is free of F and its derivatives
        (checked at random points).

        >>> from sympy import Function, symbols
        >>> x, t, u_ = symbols("x t u")
        >>> u = Function("u")(x, t)
        >>> heat = _Reduction([u.diff(t) - u.diff(x, 2)], [u], [x, t], [u_], [t / x**2], [u_])
        >>> _x, _t = heat.variables
        >>> e = heat._substituted(heat.equations[0]).subs(_t, symbols("zeta") * _x**2)
        >>> heat._by_evaluation(e, _x)  # doctest: +NORMALIZE_WHITESPACE
        -4*zeta**2*Derivative(F(zeta), (zeta, 2)) - 6*zeta*Derivative(F(zeta), zeta) +
        Derivative(F(zeta), zeta)
        """
        jets = sorted(
            {a for a in e.atoms(Derivative, AppliedUndef) if a.has(*self.F)},
            key=str,
        )
        numbers = {j: Dummy(positive=True) for j in jets}
        for c in (1, 2):
            at_c = e.subs(x, c)
            if at_c == 0 or at_c.has(nan, zoo) or at_c.has(*self.variables):
                continue
            if _free_of_numerically((e / at_c).xreplace(numbers), list(numbers.values())):
                return _free_of(self.variables, _normalized(at_c, self.F))
        return None


def _free_of_numerically(e: Expr, symbols: list[Dummy]) -> bool:
    """e the same for two random values of the symbols at three random
    points (positive values, 1.1 to 9.7); False if it cannot be evaluated.

    >>> from sympy import Dummy, Symbol, log
    >>> a, x = Dummy(positive=True), Symbol("x")
    >>> _free_of_numerically(x**2 * a / a, [a]), _free_of_numerically(x + log(a), [a])
    (True, False)
    """
    rng = random.Random(0)
    others = sorted(e.free_symbols - set(symbols), key=str)
    for _ in range(3):
        point = {v: sympify(rng.randint(11, 97)) / 10 for v in others}
        values = []
        for _ in range(2):
            at = point | {v: sympify(rng.randint(11, 97)) / 10 for v in symbols}
            try:
                values.append(complex(e.xreplace(at).evalf(30)))
            except TypeError:  # not numeric: an arbitrary function
                return False
        if abs(values[0] - values[1]) > 1e-10 * max(1.0, abs(values[0])):
            return False
    return True


def _new_names(name: str, n: int, taken: Sequence[Symbol]) -> list[str]:
    """name, or name1, ..., namen, not among the taken symbols.

    >>> from sympy import symbols
    >>> x, t, F = symbols("x t F")
    >>> _new_names("zeta", 1, [x, t]), _new_names("zeta", 2, [x, t]), _new_names("F", 1, [F])
    (['zeta'], ['zeta1', 'zeta2'], ['F_'])
    """
    names = [name] if n == 1 else [f"{name}{i}" for i in range(1, n + 1)]
    while any(str(v) in names for v in taken):
        names = [f"{m}_" for m in names]
    return names


def _normalized(e: Expr, functions: list[Expr]) -> Expr:
    """e without its factors free of the functions and without powers of
    the functions themselves (F != 0): 0 if the ansatz solves the equations,
    1 if it cannot. Powers are split as for positive values
    ((F x**a)**b = F**b x**(a b), locally near u > 0).

    >>> from sympy import Function, exp, symbols
    >>> x, z, a, k = symbols("x zeta a k")
    >>> F = Function("F")(z)
    >>> _normalized(exp(x) * (F.diff(z) - F) / x, [F])
    -F(zeta) + Derivative(F(zeta), zeta)
    >>> _normalized((x**a * F) ** k - x ** (a * k) * F.diff(z), [F])
    -F(zeta)**k + Derivative(F(zeta), zeta)
    >>> _normalized(F**2 * F.diff(z) + F**3, [F])
    F(zeta) + Derivative(F(zeta), zeta)
    >>> _normalized(0 * F, [F]), _normalized(exp(x), [F])
    (0, 1)
    """
    # (x**a F + x**a F/n)**n: the base factored first
    e = e.replace(
        lambda a: a.is_Pow and not a.exp.is_Integer,
        lambda a: factor(powsimp(a.base, force=True)) ** a.exp,
    )
    e = powdenest(expand_power_base(e, force=True), force=True)
    # log(F exp(x)) = log(F) + x, exp(F + log(t)) = t exp(F)
    e = expand(expand_log(e, force=True), power_exp=True, mul=False, multinomial=False)
    numerator, _ = fraction(together(simplify(e)))
    numerator = factor(factor_terms(powsimp(expand(numerator), force=True)))
    if not numerator.has(*functions):
        return numerator if numerator == 0 else sympify(1)
    kept = [
        f
        for f in Mul.make_args(numerator)
        if f.has(*functions) and f not in functions and f.as_base_exp()[0] not in functions
    ]
    if not kept:
        return sympify(1)
    return _without_common_powers(Mul(*kept), functions)


def _without_common_powers(e: Expr, functions: list[Expr]) -> Expr:
    """e divided by the powers of the functions and of their arguments that
    all its terms share, also with symbolic exponents (zeta**(1 + 2/a)),
    which factor does not find.

    >>> from sympy import Function, symbols
    >>> z, a = symbols("zeta a")
    >>> F = Function("F")(z)
    >>> _without_common_powers(z ** (1 + 2 / a) * F.diff(z) + z ** (2 + 2 / a) * F, [F])
    zeta*F(zeta) + Derivative(F(zeta), zeta)
    """
    e = powsimp(powdenest(expand(e), force=True), force=True)
    terms = [t.as_powers_dict() for t in Add.make_args(e)]
    bases = set(functions).union(*(f.free_symbols for f in functions))
    divisor = sympify(1)
    for base in bases:
        exponents = [t.get(base, 0) for t in terms]
        if any(x == 0 for x in exponents):
            continue
        # the exponent that leaves the simplest ones
        costs = [sum((y - x).count_ops() for y in exponents) for x in exponents]
        best = exponents[costs.index(min(costs))]
        divisor *= base**best
    return powsimp(expand(e / divisor), force=True) if divisor != 1 else e


def _free_of(variables: list[Symbol], e: Expr) -> Expr | None:
    """e, or e divided by the coefficient of its highest derivative, free
    of the variables; None if neither is.

    >>> from sympy import Function, symbols
    >>> x, z = symbols("x zeta")
    >>> F = Function("F")(z)
    >>> _free_of([x], F.diff(z) - z)
    -zeta + Derivative(F(zeta), zeta)
    >>> _free_of([x], x * F.diff(z) - x * z * F)
    -zeta*F(zeta) + Derivative(F(zeta), zeta)
    >>> _free_of([x], x * F.diff(z) - F) is None
    True
    """
    if not e.has(*variables):
        return e
    derivatives = sorted(e.atoms(Derivative), key=lambda d: d.derivative_count)
    if derivatives:
        coefficient = e.diff(derivatives[-1])
        if coefficient != 0:
            quotient = simplify(e / coefficient)
            if not quotient.has(*variables):
                return quotient
    return None
