"""Invariants, canonical coordinates and differential invariants of a given
generator (#42).

A generator X = sum_i xi_i(z) d/dz_i is a tuple of its components, one per
coordinate (the independent variables first, as everywhere in delierium), or
a VectorField.

* invariants: n - 1 functionally independent solutions of X I = 0, the first
  integrals of the characteristic system dz_1/xi_1 = ... = dz_n/xi_n
* canonical_coordinates: the invariants r and s with X s = 1; in the
  coordinates (r, s) X is the translation d/ds
* differential_invariants: for a scalar ODE, r, ds/dr, d^2s/dr^2, ...: an
  ODE invariant under X is an ODE in them of one order less in ds/dr

The characteristic system is solved one equation dz_j/dz_k = xi_j/xi_k at a
time by dsolve, with the solutions found so far substituted; if no equation
can be solved that way, NotImplementedError."""

import random
from collections.abc import Iterator, Sequence
from contextlib import suppress
from itertools import combinations, islice, product
from typing import Any

from sympy import (
    Basic,
    Derivative,
    Dummy,
    Eq,
    Expr,
    Function,
    Integral,
    Matrix,
    Piecewise,
    Symbol,
    classify_ode,
    dsolve,
    integrate,
    simplify,
    solve,
    sympify,
)

from delierium.lie_algebra import VectorField

__all__ = ["canonical_coordinates", "differential_invariants", "invariants"]

type Generator = VectorField | Sequence[Any]

_FAST_HINTS = (
    "separable",
    "1st_linear",
    "Bernoulli",
    "1st_exact",
    "1st_homogeneous_coeff_best",
    "almost_linear",
    "Riccati_special_minus2",
)


def _local(field: VectorField) -> tuple[VectorField, dict[Basic, Basic]]:
    """The field in new symbols, the coordinates positive and the parameters
    real (locally, near a generic point: sqrt(y**2) = y, x**(b/a) without
    re and im), and the map back."""
    parameters = set().union(*(c.free_symbols for c in field.coefficients)) - set(field.coordinates)
    new: dict[Basic, Basic] = {z: Dummy(str(z), positive=True) for z in field.coordinates}
    new |= {p: Dummy(str(p), real=True) for p in parameters}
    local = VectorField(
        [c.xreplace(new) for c in field.coefficients], [new[z] for z in field.coordinates]
    )
    return local, {v: k for k, v in new.items()}


def _field(generator: Generator, coordinates: Sequence[Basic] | None) -> VectorField:
    if isinstance(generator, VectorField):
        if coordinates is not None and tuple(coordinates) != generator.coordinates:
            raise ValueError("coordinates differ from those of the VectorField")
        return generator
    if coordinates is None:
        raise ValueError("coordinates are needed for a generator given as components")
    field = VectorField(list(generator), list(coordinates))
    if all(c == 0 for c in field.coefficients):
        raise ValueError("the zero generator has no invariants")
    return field


def _is_zero(e: Expr) -> bool:
    """e == 0 on a region: by simplify, else at two or more of 24 random
    points with positive coordinates. A canonical coordinate may hold only
    on a region, asinh(x/sqrt(t**2 - x**2)) for t > x, or on a branch of a
    root; the wrong branch fails everywhere."""
    e = simplify(e)
    if e == 0:
        return True
    rng = random.Random(0)
    symbols = sorted(e.free_symbols, key=str)
    zeros = 0
    for _ in range(24):
        point = {s: sympify(rng.randint(11, 97)) / 10 for s in symbols}
        try:
            value = complex(e.xreplace(point).evalf(30))
        except TypeError:  # not numeric: an arbitrary function
            return False
        zeros += abs(value) < 1e-12
    return zeros >= 2


class _Characteristics:  # pylint: disable=too-few-public-methods
    """The characteristic system of X in the parameter z_k: for every other
    coordinate z_j with xi_j != 0 an invariant I_j and z_j = g_j(z_k, C_j)
    on its characteristics."""

    def __init__(self, field: VectorField) -> None:
        self.field = field
        self.coordinates = list(field.coordinates)
        xi = dict(zip(self.coordinates, field.coefficients, strict=True))
        active = [z for z in self.coordinates if xi[z] != 0]
        self.k = min(active, key=lambda z: (xi[z].free_symbols - {z} != set(), xi[z].count_ops()))
        self.fixed = {z for z in self.coordinates if xi[z] == 0}
        self.invariants: dict[Basic, Expr] = {z: z for z in self.fixed}
        self.on_curve: dict[Basic, Expr] = {}
        self.branches: dict[Basic, list[Expr]] = {}
        self.constants: dict[Symbol, Expr] = {}
        pending = [z for z in active if z != self.k]
        while pending:
            for z in pending:
                if self._solve(z, xi[z] / xi[self.k]):
                    pending.remove(z)
                    break
            else:
                raise NotImplementedError(
                    f"characteristic system of {field} not solved for {pending}"
                )

    def _solve(self, z: Basic, rate: Expr) -> bool:
        """dz/dz_k = rate, with the solved coordinates substituted: an
        invariant and z on the characteristics."""
        rate = rate.subs(self.on_curve)
        # coordinates with xi = 0 are constant on the characteristics
        others = (set(self.coordinates) - {z, self.k} - self.fixed) & rate.free_symbols
        if others:
            return False
        t = self.k
        g = Function("f")(t)  # pylint: disable=not-callable
        ode = Eq(Derivative(g, t), rate.subs(z, g))
        c1 = Symbol("C1")
        for solution in _solutions(ode, g):
            for s in solution:
                constant = [e for e in solve(s.subs(g, z), c1) if not e.has(Integral)]
                if not constant:
                    continue
                invariant = simplify(_generic(constant[0]).subs(self.constants))
                # dsolve may be wrong (its factorable hint): check X I = 0
                if not _is_zero(self.field(invariant)):
                    continue
                # z in z_k and the constants of the characteristics
                c = Dummy("C")
                explicit = solve(s.subs(c1, c).subs(g, z), z) or solve(Eq(constant[0], c), z)
                self.invariants[z] = invariant
                if explicit:
                    self.on_curve[z] = explicit[0]
                    self.branches[z] = explicit
                    self.constants[c] = invariant
                return True
        return False


def _solutions(ode: Eq, g: Expr) -> Iterator[list[Eq]]:
    """The solutions of ode by dsolve: by its default, then by each of the
    fast hints that apply (lie_group or the power series may not end, or
    take all memory)."""
    hints: list[str] = ["default"]
    with suppress(NotImplementedError, ValueError, RecursionError):
        hints += [h for h in classify_ode(ode, g) if h in _FAST_HINTS]
    for hint in dict.fromkeys(hints):
        try:
            solution = dsolve(ode, g, hint=hint)
        except (NotImplementedError, ValueError, RecursionError, TypeError):
            continue
        yield solution if isinstance(solution, list) else [solution]


def invariants(generator: Generator, coordinates: Sequence[Basic] | None = None) -> list[Expr]:
    """n - 1 functionally independent invariants of the generator, X I = 0,
    one per coordinate other than the one used as the parameter of the
    characteristics.

    >>> from sympy import symbols
    >>> x, y, u = symbols("x y u")
    >>> invariants((-y, x), [x, y])
    [x**2 + y**2]
    >>> invariants((x, 2 * y, 0), [x, y, u])
    [y/x**2, u]
    """
    local, back = _local(_field(generator, coordinates))
    characteristics = _Characteristics(local)
    return [
        characteristics.invariants[z].xreplace(back)
        for z in characteristics.coordinates
        if z != characteristics.k
    ]


def canonical_coordinates(
    generator: Generator, coordinates: Sequence[Basic] | None = None
) -> tuple[list[Expr], Expr]:
    """(r, s): the invariants r and s with X s = 1, so that X = d/ds in the
    coordinates (r, s): s is the integral of dz_k/xi_k along the
    characteristics.

    >>> from sympy import symbols
    >>> x, y = symbols("x y")
    >>> canonical_coordinates((x, y), [x, y])
    ([y/x], log(x))
    """
    field = _field(generator, coordinates)
    local, back = _local(field)
    characteristics = _Characteristics(local)
    k = characteristics.k
    xi_k = local.coefficients[characteristics.coordinates.index(k)]
    r = [characteristics.invariants[z] for z in characteristics.coordinates if z != k]
    # z on the characteristics: one branch of each (y = +-sqrt(C - x**2))
    solved = list(characteristics.branches)
    for branch in islice(product(*(characteristics.branches[z] for z in solved)), 16):
        try:
            integral = integrate(1 / xi_k.subs(dict(zip(solved, branch, strict=True))), k)
        except RecursionError:
            continue
        for s in _cases(integral.subs(characteristics.constants)):
            s = simplify(s)
            if _is_zero(local(s) - 1):
                return [e.xreplace(back) for e in r], s.xreplace(back)
    raise NotImplementedError(f"no canonical coordinate s found for {field}")


def _generic(e: Expr) -> Expr:
    """e with every Piecewise replaced by its first case: generic values of
    the parameters (A**2*B**2 != 0)."""
    return e.replace(lambda a: isinstance(a, Piecewise), lambda a: a.args[0].expr)


def _cases(e: Expr) -> list[Expr]:
    """e for generic parameters, then with each case of an outer Piecewise
    (asin, or -I*acosh where its argument exceeds 1)."""
    pieces = [a for a in e.atoms(Piecewise) if not any(a in b.args for b in e.atoms(Piecewise))]
    cases = [_generic(e)]
    for piece in pieces[:1]:
        cases += [_generic(e.xreplace({piece: case.expr})) for case in piece.args[1:]]
    return cases


def differential_invariants(
    generator: Generator,
    dependent: Expr | Sequence[Expr],
    independent: Symbol | Sequence[Symbol],
    order: int,
) -> list[Expr]:
    """Differential invariants of the generator up to order, as expressions
    in the independent variables, the dependent functions and their
    derivatives (the components of the generator in the independent
    variables and plain symbols named like the dependent functions).

    In canonical coordinates (r_1, ..., r_{N-1}, s), X = d/ds: p of them
    serve as new independent variables xi (with independent total
    derivatives), the others as new dependent variables w. X only shifts s,
    so the invariants are the xi and w other than s, and the derivatives of
    the w by the xi up to order, in this order, by increasing order.

    For ODEs the xi are among the r: for a scalar ODE r, ds/dr, ...,
    d^order s/dr^order, and an ODE of order n invariant under X is an ODE of
    order n - 1 for ds/dr as a function of r. For PDEs s may be a new
    independent variable as well, those free of the dependent functions
    first.

    >>> from sympy import Function, Symbol
    >>> x = Symbol("x")
    >>> y = Function("y")(x)
    >>> differential_invariants((0, Symbol("y")), y, x, 1)
    [x, Derivative(y(x), x)/y(x)]

    The heat equation's scaling x d/dx + 2 t d/dt: xi = t/x**2, s = log(x)
    as new independent variables; u, u_xi, u_s are invariant:

    >>> t = Symbol("t")
    >>> u = Function("u")(x, t)
    >>> for e in differential_invariants((x, 2 * t, 0), u, [x, t], 1):
    ...     print(e)
    t/x**2
    u(x, t)
    x**2*Derivative(u(x, t), t)
    2*t*Derivative(u(x, t), t) + x*Derivative(u(x, t), x)
    """
    if order < 0:
        raise ValueError("order must be >= 0")
    functions = [dependent] if isinstance(dependent, Expr) else list(dependent)
    variables = [independent] if isinstance(independent, Symbol) else list(independent)
    names = [Symbol(f.func.__name__) for f in functions]
    r, s = canonical_coordinates(generator, [*variables, *names])
    on_jets = dict(zip(names, functions, strict=True))
    r = [e.subs(on_jets) for e in r]
    s = s.subs(on_jets)
    # an ODE: r independent, the classical reduction of order (Hydon 4.1);
    # a PDE: s may be independent too (similarity variables)
    candidates = r if len(variables) == 1 else [*r, s]
    new, jacobian = _new_independent(candidates, variables, functions)
    w = [e for e in [*r, s] if e not in new]
    inverse = jacobian.inv()

    def derivative(f: Expr, j: int) -> Expr:
        """d f / d xi_j = sum_i (J^-1)_ji D_i f."""
        return simplify(sum(inverse[j, i] * f.diff(v) for i, v in enumerate(variables)))

    result = [e for e in [*new, *w] if e != s]
    previous: dict[tuple[int, ...], list[Expr]] = {(): w}
    for _ in range(order):
        current: dict[tuple[int, ...], list[Expr]] = {}
        for index, values in previous.items():
            for j in range(len(new)):
                if index and j < index[-1]:
                    continue
                current[(*index, j)] = [derivative(f, j) for f in values]
        result += [f for values in current.values() for f in values]
        previous = current
    return result


def _new_independent(
    candidates: Sequence[Expr], variables: Sequence[Symbol], functions: Sequence[Expr]
) -> tuple[list[Expr], Matrix]:
    """p of the candidates with independent total derivatives, those free of
    the dependent functions first, and their Jacobian J_ij = D_i xi_j."""
    choices = sorted(
        combinations(candidates, len(variables)),
        key=lambda chosen: sum(xi.has(*functions) for xi in chosen),
    )
    for chosen in choices:
        jacobian = Matrix([[xi.diff(v) for xi in chosen] for v in variables])
        if simplify(jacobian.det()) != 0:
            return list(chosen), jacobian
    raise NotImplementedError("no independent variables among the invariants")
