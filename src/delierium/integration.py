"""Integration of a scalar ODE by its point symmetries (#43), and reduction
of order by one known generator (#14).

How it works:

1. Reduction of order by one generator X (Hydon 4.1, Olver 2.5): in
   canonical coordinates (r, s) of X, X = d/ds, and an ODE of order n
   invariant under X is an ODE of order n - 1 for w = ds/dr as a function
   of r. The ODE is solved for its highest derivative, y^(n) = f; w, w',
   ..., w^(n-1) are computed with the total derivative d/dr = D_x / D_x r,
   each w^(k) linear in y^(k+1). Solving them for y', ..., y^(n-1) and
   substituting y^(n) = f gives w^(n-1) as a function of x, y, w, ...,
   w^(n-2), which depends on x and y only through r: r(x, y) = r is solved
   for y (or x), locally, with the variables positive.

2. The other symmetries: a generator Y with [X, Y] = lambda X maps the
   invariants of X to invariants of X, so it induces a symmetry of the
   reduced ODE, the prolongation of Y applied to r and w. If X spans a
   one-dimensional ideal of the algebra, all of them do; such an X is a
   common eigenvector of the ad matrices. A solvable algebra over the
   complex numbers always has one (Lie's theorem), over the reals not
   always (the Euclidean algebra e(2)): then only the normalizer of X goes
   down.

3. Integration (Olver, Theorem 2.60; Bluman-Anco 3.4.3): reduce as long as
   there are symmetries. A first order ODE w' = g(r, w) with a symmetry
   (xi, eta) is a quadrature in its canonical coordinates, unless eta = xi g:
   then the solutions are the orbits, an invariant equals a constant. A
   first order ODE without symmetries is left to dsolve's fast methods; an
   ODE of higher order without symmetries ends the integration
   (NotImplementedError). Going back up, a solution of the reduced ODE is
   solved for w = ds/dr, and s(x, y) = int w dr + C is a solution of the ODE
   one order higher: n symmetries of a solvable algebra give the general
   solution of an ODE of order n by n quadratures.

Which generator to reduce by first: one spanning an ideal, then one with
the largest normalizer; among those one with xi = 0 (x stays the independent
variable), then the simplest. If an integration fails, the next choice is
tried.
"""

import random
from cmath import isfinite
from collections.abc import Sequence
from dataclasses import dataclass
from itertools import count
from typing import Any

from sympy import (
    Add,
    Basic,
    Derivative,
    Dummy,
    Eq,
    Expr,
    Function,
    Integral,
    Matrix,
    Piecewise,
    Poly,
    S,
    Symbol,
    cancel,
    classify_ode,
    dsolve,
    exp,
    integrate,
    simplify,
    solve,
    symbols,
)

from delierium.helpers import numeric_value, plain_symbol, random_point
from delierium.invariants import _FAST_HINTS, canonical_coordinates
from delierium.lie_algebra import LieAlgebra, NotClosedError, VectorField

__all__ = ["OrderReduction", "integrate_ode", "reduce_order"]

type Generator = VectorField | Sequence[Any]

# reductions tried per integration, choices that fail included
_BUDGET = 12
# integrands small enough for all of integrate's methods, and too large
# for any (they may not end)
_SMALL = 30
_LARGE = 80


@dataclass
class _Level:
    """An ODE w_n = rhs(t, w_0, ..., w_{n-1}) in jet symbols, with symmetries
    (xi, eta) in (t, w_0)."""

    t: Symbol
    w: list[Symbol]
    rhs: Expr
    generators: list[tuple[Expr, Expr]]

    @property
    def order(self) -> int:
        """The order n.

        >>> from sympy import symbols
        >>> x, w0, w1, w2 = symbols("x w0 w1 w2")
        >>> _Level(x, [w0, w1, w2], w1, []).order
        2
        """
        return len(self.w) - 1


def _total(f: Expr, t: Symbol, w: Sequence[Symbol]) -> Expr:
    """The total derivative D_t f on the jet symbols w_0, w_1, ...

    >>> from sympy import symbols
    >>> x, w0, w1, w2 = symbols("x w0 w1 w2")
    >>> _total(x * w0 * w1, x, [w0, w1, w2])
    w0*w1 + w0*w2*x + w1**2*x
    """
    f = S(f)
    return f.diff(t) + sum(w[i + 1] * f.diff(w[i]) for i in range(len(w) - 1))


def _prolonged(
    generator: tuple[Expr, Expr], t: Symbol, w: Sequence[Symbol], f: Expr, order: int
) -> Expr:
    """The prolongation of the generator up to order applied to f.

    >>> from sympy import symbols
    >>> x, w0, w1 = symbols("x w0 w1")
    >>> _prolonged((x, w0), x, [w0, w1], w1, 1)  # a scaling leaves y' alone
    0
    """
    xi, eta = S(generator[0]), S(generator[1])
    f = S(f)
    result = xi * f.diff(t) + eta * f.diff(w[0])
    for k in range(1, order + 1):
        eta = cancel(_total(eta, t, w) - w[k] * _total(xi, t, w))
        result += eta * f.diff(w[k])
    return result


def _agrees(e: Expr, f: Expr) -> bool:
    """e == f at four random points (positive values).

    >>> from sympy import symbols, sqrt
    >>> x = symbols("x", positive=True)
    >>> _agrees(sqrt(x**2), x), _agrees(x, 2 * x)
    (True, False)
    """
    rng = random.Random(1)
    variables = sorted(e.free_symbols | f.free_symbols, key=str)
    for _ in range(4):
        point = random_point(variables, rng)
        a, b = numeric_value(e, point), numeric_value(f, point)
        if a is None or b is None or abs(a - b) > 1e-8 * (1 + abs(a)):
            return False
    return True


def _solve(e: Expr | Eq, z: Basic) -> list[Expr]:
    """The solutions of e = 0 for z by solve. For a polynomial numerator each
    is checked at random points: SymPy 1.14 solves z**3 - a*x*z + x**3 = 0
    wrongly (its preprocessing scales z by x), but not with symbols for the
    coefficients; NotImplementedError if that fails too. Other solutions may
    hold up to a branch (log, roots), which the constants absorb.

    >>> from sympy import symbols
    >>> x, z, a = symbols("x z a")
    >>> _solve(z**2 - x, z)
    [-sqrt(x), sqrt(x)]
    >>> len(_solve(z**3 - a * x * z + x**3, z))
    3
    """
    e = e.lhs - e.rhs if isinstance(e, Eq) else e
    solutions = solve(e, z)
    numerator = cancel(e).as_numer_denom()[0]
    if not numerator.is_polynomial(z) or all(_root(numerator, z, s) for s in solutions):
        return solutions
    coefficients = Poly(numerator, z).all_coeffs()
    k = symbols(f"k0:{len(coefficients)}", cls=Dummy)
    generic = sum(c * z**i for i, c in enumerate(reversed(k)))
    back = dict(zip(k, coefficients, strict=True))
    solutions = [s.xreplace(back) for s in solve(generic, z)]
    if all(_root(numerator, z, s) for s in solutions):
        return solutions
    raise NotImplementedError(f"solve failed for {e} = 0")


def _root(polynomial: Expr, z: Basic, value: Expr) -> bool:
    """Whether value is a root of the polynomial in z, at random points.

    >>> from sympy import symbols
    >>> x, z = symbols("x z")
    >>> _root(z**2 - x**2, z, x), _root(z**2 - x**2, z, 2 * x)
    (True, False)
    """
    rng = random.Random(4)
    variables = sorted(polynomial.free_symbols - {z}, key=str)
    terms = Add.make_args(polynomial.expand().subs(z, value))
    for _ in range(3):
        point = random_point(variables, rng)
        values = [v for term in terms if (v := numeric_value(term, point)) is not None]
        if len(values) < len(terms) or not all(isfinite(v) for v in values):
            continue
        if abs(sum(values)) > 1e-12 * (1 + max(abs(v) for v in values)):
            return False
    return True


def _in_invariant(e: Expr, t: Symbol, w0: Symbol, r: Expr, invariant: Symbol) -> Expr:
    """e(t, w0, ...), constant on the orbits of the generator, as a function
    of the invariant r(t, w0): r = invariant solved for w0 (or t), locally,
    with the variables positive; if t or w0 remain, they are given a value
    where e is checked not to depend on them.

    >>> from sympy import symbols
    >>> x, w0, r = symbols("x w0 r")
    >>> _in_invariant(w0**2 / x**2 + 1, x, w0, w0 / x, r)
    r**2 + 1
    """
    e = cancel(e)
    if not e.has(t, w0):
        return e
    local = {z: Dummy(str(z), positive=True) for z in (t, w0, invariant)}
    back = {v: k for k, v in local.items()}
    e_local, r_local, invariant_local = (z.xreplace(local) for z in (e, r, invariant))
    coordinates = {local[t], local[w0]}
    for z in (local[w0], local[t]):
        if not r_local.has(z):
            continue
        best = None
        for solution in _solve(r_local - invariant_local, z):
            g = simplify(e_local.subs(z, solution))
            rest = sorted(g.free_symbols & coordinates, key=str)
            if rest:
                for value in (1, 2, 3, S(1) / 2, 5):
                    h = simplify(g.subs(rest[0], value))
                    if h.is_finite is not False and not h.has(*coordinates) and _agrees(g, h):
                        g = h
                        break
                else:
                    continue
            if best is None or g.count_ops() < best.count_ops():
                best = g
        if best is not None:
            return best.xreplace(back)
    raise NotImplementedError(f"{e} not written as a function of {r}")


def _reduce(
    level: _Level, generator: tuple[Expr, Expr], others: Sequence[tuple[Expr, Expr]]
) -> tuple[_Level, Expr, Expr]:
    """The level reduced by the generator, with the others induced, and the
    canonical coordinates r, s (new variable r, w_0 = ds/dr).

    y'' = y'**2 / y by y d/dy: (log y)'' = 0, the translation of x stays:

    >>> from sympy import symbols
    >>> x, w0, w1, w2 = symbols("x w0 w1 w2")
    >>> new, r, s = _reduce(_Level(x, [w0, w1, w2], w1**2 / w0, []), (0, w0), [(1, 0)])
    >>> r, s, new.rhs, new.generators
    (x, log(w0), 0, [(1, 0)])
    """
    t, w, n = level.t, level.w, level.order
    (r,), s = canonical_coordinates(generator, [t, w[0]])
    new_t = Dummy("r")
    v = list(symbols(f"w0:{n}", cls=Dummy))
    dr = _total(r, t, w)
    # w_j in the jet of y, and y^(j+1) in terms of w_j
    derivatives = [cancel(_total(s, t, w) / dr)]
    for _ in range(1, n):
        derivatives.append(cancel(_total(derivatives[-1], t, w) / dr))
    solved: dict[Symbol, Expr] = {}
    for j in range(n - 1):
        solutions = _solve(derivatives[j].subs(solved) - v[j], w[j + 1])
        if not solutions:
            raise NotImplementedError(f"{derivatives[j]} not solved for {w[j + 1]}")
        solved[w[j + 1]] = solutions[0]
    highest = derivatives[-1].subs(w[n], level.rhs).subs(solved)
    rhs = simplify(_in_invariant(highest, t, w[0], r, new_t))
    induced = []
    if n > 1:
        for other in others:
            a = _in_invariant(_prolonged(other, t, w, r, 0), t, w[0], r, new_t)
            b = _prolonged(other, t, w, derivatives[0], 1).subs(w[1], solved[w[1]])
            b = _in_invariant(simplify(b), t, w[0], r, new_t)
            induced.append((simplify(a), simplify(b)))
    return _Level(new_t, v, rhs, _independent(induced, new_t, v[0])), r, s


def _independent(
    generators: Sequence[tuple[Expr, Expr]], t: Symbol, w0: Symbol
) -> list[tuple[Expr, Expr]]:
    """The generators without those that are linear combinations (over
    the numbers) of the ones before, checked at random points.

    >>> from sympy import symbols
    >>> x, y = symbols("x y")
    >>> _independent([(1, 0), (0, 0), (2, 0), (x, y)], x, y)
    [(1, 0), (x, y)]
    """
    rng = random.Random(2)
    points = [random_point([t, w0], rng) for _ in range(6)]
    chosen: list[tuple[Expr, Expr]] = []
    rows: list[list[Expr]] = []
    for g in generators:
        row = [S(c).xreplace(p) for p in points for c in g]
        if Matrix([*rows, row]).rank(simplify=True) > len(rows):
            chosen.append(g)
            rows.append(row)
    return chosen


def _common_eigenvectors(matrices: Sequence[Matrix], n: int) -> list[Matrix]:
    """Bases (columns) of the spaces of the vectors a with a^T M = lambda_M a^T
    for every matrix M, lambda_M real.

    >>> from sympy import Matrix
    >>> _common_eigenvectors([Matrix([[0, 0], [1, 0]]), Matrix([[-1, 0], [0, 0]])], 2)
    [Matrix([
    [1],
    [0]])]
    """
    spaces = [Matrix.eye(n)]
    for m in matrices:
        new = []
        for value, _, vectors in m.T.eigenvects():
            if value.is_real is False:
                continue
            eigenspace = Matrix.hstack(*vectors)
            for space in spaces:
                null = Matrix.hstack(space, -eigenspace).nullspace()
                columns = (
                    Matrix.hstack(*[space * u[: space.cols, :] for u in null]).columnspace()
                    if null
                    else []
                )
                if columns:
                    new.append(Matrix.hstack(*columns))
        spaces = new
        if not spaces:
            break
    return spaces


def _choices(
    generators: Sequence[tuple[Expr, Expr]], t: Symbol, w0: Symbol
) -> list[tuple[tuple[Expr, Expr], list[tuple[Expr, Expr]]]]:
    """(X, the generators inducing symmetries of the ODE reduced by X), best
    first (see the module docstring).

    >>> from sympy import symbols
    >>> x, y = symbols("x y")
    >>> _choices([(x, y), (1, 0)], x, y)[0]
    ((1, 0), [(x, y)])
    """
    n = len(generators)
    candidates: list[tuple[tuple[Expr, Expr], list[tuple[Expr, Expr]]]] = []
    try:
        c = LieAlgebra([list(g) for g in generators], [t, w0]).structure_constants
    except NotClosedError:
        c = None
    if c is not None:
        ads = [Matrix(n, n, lambda i, k, j=j: c[j][i][k]) for j in range(n)]
        for space in _common_eigenvectors(ads, n):
            for col in range(space.cols):
                a = space[:, col]
                X = (
                    simplify(sum(a[i] * S(generators[i][0]) for i in range(n))),
                    simplify(sum(a[i] * S(generators[i][1]) for i in range(n))),
                )
                candidates.append((X, _complement(a, generators)))
    if not candidates:
        for i, X in enumerate(generators):
            normalizer = [
                g
                for j, g in enumerate(generators)
                if j != i and c is not None and all(c[i][j][k] == 0 for k in range(n) if k != i)
            ]
            candidates.append((X, normalizer))
    return sorted(
        candidates,
        key=lambda cand: (
            -len(cand[1]),
            S(cand[0][0]) != 0,
            sum(S(e).count_ops() for e in cand[0]),
        ),
    )


def _complement(a: Matrix, generators: Sequence[tuple[Expr, Expr]]) -> list[tuple[Expr, Expr]]:
    """Generators that extend a to a basis.

    >>> from sympy import Matrix, symbols
    >>> x, y = symbols("x y")
    >>> _complement(Matrix([1, 1]), [(1, 0), (0, 1)])
    [(1, 0)]
    """
    n = len(generators)
    rows = [list(a)]
    chosen = []
    for i, g in enumerate(generators):
        unit = [int(i == j) for j in range(n)]
        if Matrix([*rows, unit]).rank() > len(rows):
            rows.append(unit)
            chosen.append(g)
    return chosen


class _Integration:
    """The integration of one ODE: constants C1, C2, ... and the budget of
    reductions."""

    def __init__(self) -> None:
        """Fresh constants and the full budget.

        >>> _Integration().constant()
        C1
        """
        self.constants = count(1)
        self.used: set[Symbol] = set()
        self.budget = _BUDGET

    def constant(self) -> Symbol:
        """The next constant.

        >>> integration = _Integration()
        >>> integration.constant(), integration.constant()
        (C1, C2)
        """
        c = Symbol(f"C{next(self.constants)}")
        self.used.add(c)
        return c

    def solve(self, level: _Level) -> list[Eq]:
        """The general solution of the level, relations between t and w_0
        with order constants."""
        if not level.generators:
            return self._without_symmetries(level)
        error: Exception = NotImplementedError("no reduction left")
        for generator, others in _choices(level.generators, level.t, level.w[0]):
            if self.budget <= 0:
                break
            self.budget -= 1
            try:
                return self._by(level, generator, others)
            except NotImplementedError as e:
                error = e
        raise error

    def _by(self, level: _Level, generator: tuple[Expr, Expr], others: list) -> list[Eq]:
        """The general solution, by reduction by the generator."""
        t, w = level.t, level.w
        if level.order == 1 and simplify(S(generator[1]) - S(generator[0]) * level.rhs) == 0:
            # the solutions are the orbits
            (r,), _ = canonical_coordinates(generator, [t, w[0]])
            return [Eq(r, self.constant())]
        reduced, r, s = _reduce(level, generator, others)
        v = reduced.w[0]
        relations = [Eq(v, reduced.rhs)] if level.order == 1 else self.solve(reduced)
        result = []
        for relation in relations:
            branches = (
                [relation.rhs]
                if relation.lhs == v and not relation.rhs.has(v)
                else _solve(relation, v)
            )
            if not branches:
                raise NotImplementedError(f"{relation} not solved for the derivative")
            for branch in branches:
                branch = _absorbed(branch, sorted(branch.free_symbols & self.used, key=str))
                quadrature = _quadrature(branch, reduced.t, r)
                # a branch with w = 0 or infinite
                if not quadrature.has(S.ComplexInfinity, S.NaN):
                    result.append(Eq(s, quadrature + self.constant()))
        return result

    def _without_symmetries(self, level: _Level) -> list[Eq]:
        """A first order ODE by dsolve's fast methods."""
        if level.order > 1:
            raise NotImplementedError(
                f"no symmetries left for an ODE of order {level.order}: {level.rhs}"
            )
        t, w0 = level.t, level.w[0]
        f = Function("f")(t)  # pylint: disable=not-callable
        ode = Eq(f.diff(t), level.rhs.subs(w0, f))
        for hint in [h for h in classify_ode(ode, f) if h in _FAST_HINTS]:
            try:
                solution = dsolve(ode, f, hint=hint)
            except (NotImplementedError, ValueError):
                continue
            c = self.constant()
            return [
                Eq(e.lhs.subs(f, w0), e.rhs.subs(f, w0)).subs(Symbol("C1"), c)
                for e in (solution if isinstance(solution, list) else [solution])
            ]
        raise NotImplementedError(f"first order ODE without symmetries not solved: {ode}")


def _quadrature(f: Expr, t: Symbol, upper: Expr) -> Expr:
    """int f dt at t = upper; an unevaluated integral if integrate fails.
    Rational functions by integrate, others by its manual and its risch
    method, all its methods only for small integrands, none for large ones
    (they may not end).

    >>> from sympy import symbols
    >>> r, x = symbols("r x")
    >>> _quadrature(1 / r, r, x**2)
    log(x**2)
    """
    local = Dummy(str(t), positive=True)
    g = f.subs(t, local)
    attempts: list[tuple[dict[str, bool], Expr]] = []
    if g.is_rational_function(local):
        attempts = [({}, g)]
    elif (g := simplify(g)).count_ops() <= _LARGE:
        attempts = [({"manual": True}, g), ({"risch": True}, g)]
        if g.count_ops() <= _SMALL:
            attempts.append(({}, g))
    for options, integrand in attempts:
        try:
            F = _generic(integrate(integrand, local, **options))
        except NotImplementedError:
            continue
        # integrate's manual method may return nan
        if not F.has(Integral, S.NaN, S.ComplexInfinity):
            return F.subs(local, upper)
    rho = Dummy("rho")
    return Integral(f.subs(t, rho), (rho, upper))


def _absorbed(e: Expr, constants: Sequence[Symbol]) -> Expr:
    """e with exp(k C + a) written C**k exp(a) for each constant C that
    occurs only in such exponentials (C for exp(C), another constant).

    >>> from sympy import exp, symbols
    >>> x, c1, c2 = symbols("x C1 C2")
    >>> _absorbed(exp(2 * c1 + x) + c2 * exp(c2), [c1, c2])
    C1**2*exp(x) + C2*exp(C2)
    """
    for c in constants:
        powers = [a for a in e.atoms(exp) if a.has(c)]
        if not powers or e.xreplace({a: Dummy() for a in powers}).has(c):
            continue
        replacement = {}
        for a in powers:
            k = a.args[0].diff(c)
            if not k.is_Rational or a.args[0].diff(c, 2) != 0:
                break
            replacement[a] = c**k * exp(cancel(a.args[0] - k * c))
        else:
            e = e.xreplace(replacement)
    return e


def _generic(e: Expr) -> Expr:
    """e with every Piecewise replaced by its first case that is not an
    equation: integrate puts the special values first (c = 0), dsolve the
    generic case (c != 0).

    >>> from sympy import Eq, Ne, Piecewise, log, symbols
    >>> x, c = symbols("x c")
    >>> _generic(Piecewise((log(x), Eq(c, 0)), (x**c / c, True)))
    x**c/c
    >>> _generic(Piecewise((x / c, Ne(c, 0)), (x, True)))
    x/c
    """

    def case(piecewise: Piecewise) -> Expr:
        for piece in piecewise.args:
            if not piece.cond.atoms(Eq):
                return piece.expr
        return piecewise.args[-1].expr

    return e.replace(lambda a: isinstance(a, Piecewise), case)


def _jets(ode: Expr, y: Expr, x: Symbol) -> tuple[list[Symbol], Expr]:
    """Jet symbols w_0, ..., w_n and the ODE in them.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> w, ode = _jets(y.diff(x, 2) + y, y, x)
    >>> ode == w[0] + w[2]
    True
    """
    order = max((d.derivative_count for d in ode.atoms(Derivative) if d.expr == y), default=0)
    w = list(symbols(f"w0:{order + 1}", cls=Dummy))
    for k in range(order, 0, -1):
        ode = ode.subs(Derivative(y, (x, k)), w[k])
    return w, ode.subs(y, w[0])


def _generators(generators: Sequence[Generator], y: Expr, w0: Symbol) -> list[tuple[Expr, Expr]]:
    """The generators as tuples (xi, eta), the plain symbol of y replaced by
    w0.

    >>> from sympy import Function, symbols
    >>> x, w0 = symbols("x w0")
    >>> y = Function("y")(x)
    >>> _generators([(x, symbols("y"))], y, w0)
    [(x, w0)]
    """
    name = plain_symbol(y)
    result = []
    for g in generators:
        components = g.coefficients if isinstance(g, VectorField) else g
        result.append(tuple(S(c).subs(name, w0) for c in components))
    return result


def _equation(ode: Expr | Eq) -> Expr:
    """ode = 0 as an expression.

    >>> from sympy import Eq, symbols
    >>> x = symbols("x")
    >>> _equation(Eq(x, 1))
    x - 1
    """
    return ode.lhs - ode.rhs if isinstance(ode, Eq) else S(ode)


@dataclass
class OrderReduction:
    """An ODE reduced by one generator X: equation is the ODE of order n - 1
    for function = w(r), solved for its highest derivative; r and s are the
    canonical coordinates of X in the independent and dependent variable
    (X s = 1, w = ds/dr); generators are the symmetries of the reduced ODE
    induced by the other generators given, in the plain symbols of r and
    w."""

    equation: Eq
    function: Expr
    r: Expr
    s: Expr
    generators: list[tuple[Expr, Expr]]


def reduce_order(
    ode: Expr | Eq,
    generator: Generator,
    dependent: Expr,
    independent: Symbol,
    others: Sequence[Generator] = (),
) -> OrderReduction:
    """The ODE (= 0, or an Eq) reduced by a symmetry: an ODE of one order
    less for w = ds/dr in the canonical coordinates (r, s) of the generator.
    Generators among the others whose commutator with it is a multiple of
    it induce symmetries of the reduced ODE.

    y'' = y'**2/y + y'/x (Hydon, Example 4.4 without the parameter) by the
    scaling y d/dy: r = x, w = y'/y, and the scaling of x remains:

    >>> from sympy import Function, symbols
    >>> x, y_ = symbols("x y")
    >>> y = Function("y")(x)
    >>> ode = y.diff(x, 2) - y.diff(x) ** 2 / y - y.diff(x) / x
    >>> red = reduce_order(ode, (0, y_), y, x, [(x, 0)])
    >>> red.equation, red.r, red.s, red.generators
    (Eq(Derivative(w(r), r), w(r)/r), x, log(y), [(r, -w)])
    """
    expression, w, branches = _solved(ode, dependent, independent)
    (X, *rest) = _generators([generator, *others], dependent, w[0])
    normalizing = [g for g in rest if _normalizes(g, X, independent, w[0])]
    reduced, r, s = _reduce(_Level(independent, w, branches[0], []), X, normalizing)
    r_name, w_name = (Symbol(name) for name in _fresh(expression, ["r", "w"]))
    fun = Function(str(w_name))(r_name)  # pylint: disable=not-callable
    to_function = {v: fun.diff(r_name, k) for k, v in enumerate(reduced.w)}
    to_function[reduced.t] = r_name
    plain = {w[0]: plain_symbol(dependent)}
    induced = {reduced.t: r_name, reduced.w[0]: w_name}
    return OrderReduction(
        Eq(fun.diff(r_name, len(w) - 2), reduced.rhs.xreplace(to_function)),
        fun,
        r.xreplace(plain),
        s.xreplace(plain),
        [(a.xreplace(induced), b.xreplace(induced)) for a, b in reduced.generators],
    )


def _solved(
    ode: Expr | Eq, dependent: Expr, independent: Symbol
) -> tuple[Expr, list[Symbol], list[Expr]]:
    """The ODE as an expression, its jet symbols w_0, ..., w_n and the
    solutions for w_n.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> _, w, branches = _solved(y.diff(x) ** 2 - y, y, x)
    >>> len(w), len(branches)
    (2, 2)
    """
    expression = _equation(ode)
    w, jets = _jets(expression, dependent, independent)
    if len(w) < 2:
        raise ValueError("not a differential equation")
    branches = _solve(jets, w[-1])
    if not branches:
        raise NotImplementedError(f"{ode} not solved for its highest derivative")
    return expression, w, branches


def _normalizes(g: tuple[Expr, Expr], X: tuple[Expr, Expr], t: Symbol, w0: Symbol) -> bool:
    """Whether [X, g] is a constant multiple of X.

    >>> from sympy import symbols
    >>> x, y = symbols("x y")
    >>> _normalizes((x, y), (1, 0), x, y), _normalizes((x**2, 0), (1, 0), x, y)
    (True, False)
    """
    bracket = VectorField(list(X), [t, w0]).commutator(VectorField(list(g), [t, w0]))
    ratios = {simplify(b / S(a)) for a, b in zip(X, bracket.coefficients, strict=True) if S(a) != 0}
    zero_outside = all(
        simplify(b) == 0 for a, b in zip(X, bracket.coefficients, strict=True) if S(a) == 0
    )
    return zero_outside and len(ratios) == 1 and not ratios.pop().has(t, w0)


def _fresh(expression: Expr, names: Sequence[str]) -> list[str]:
    """The names, with a number appended where they occur in expression.

    >>> from sympy import symbols
    >>> r = symbols("r")
    >>> _fresh(r + 1, ["r", "w"])
    ['r1', 'w']
    """
    used = {str(s) for s in expression.free_symbols} | {
        f.func.__name__ for f in expression.atoms(Function)
    }
    result = []
    for name in names:
        candidate, k = name, 0
        while candidate in used:
            k += 1
            candidate = f"{name}{k}"
        result.append(candidate)
    return result


def integrate_ode(
    ode: Expr | Eq,
    dependent: Expr,
    independent: Symbol,
    generators: Sequence[Generator] | None = None,
) -> list[Eq]:
    """The general solution of a scalar ODE (= 0, or an Eq) by its point
    symmetries, as equations between the independent variable and the
    dependent function with constants C1, C2, ... (implicit where solving for
    the function fails). Generators are tuples in the plain symbols of the
    variables, or VectorFields; by default those of lie_symmetries.
    NotImplementedError if the symmetries do not suffice (an ODE of order
    two or more without symmetries remains) or a step fails.

    y'' = y'**2/y by the translation d/dx and the scaling y d/dy:

    >>> from sympy import Function, symbols
    >>> x, y_ = symbols("x y")
    >>> y = Function("y")(x)
    >>> integrate_ode(y.diff(x, 2) - y.diff(x) ** 2 / y, y, x, [(1, 0), (0, y_)])
    [Eq(y(x), C2*exp(C1*x))]
    """
    expression, w, branches = _solved(ode, dependent, independent)
    if generators is None:
        from delierium.symmetries import lie_symmetries  # pylint: disable=import-outside-toplevel

        generators = lie_symmetries(expression, dependent, independent).generators()
    gens = _independent(_generators(generators, dependent, w[0]), independent, w[0])
    result = []
    for rhs in branches:
        integration = _Integration()
        for relation in integration.solve(_Level(independent, w, rhs, gens)):
            relation = _explicit(relation.subs(w[0], dependent), dependent)
            constants = sorted(integration.used, key=str)
            result.append(
                _renumbered(Eq(relation.lhs, _absorbed(relation.rhs, constants)), constants)
            )
    return result


def _renumbered(relation: Eq, constants: Sequence[Symbol]) -> Eq:
    """The constants of relation renamed C1, C2, ... in their order.

    >>> from sympy import Eq, symbols
    >>> x, c1, c3 = symbols("x C1 C3")
    >>> _renumbered(Eq(x, c1 + c3), [c1, c3])
    Eq(x, C1 + C2)
    """
    present = sorted((c for c in constants if relation.has(c)), key=lambda c: int(c.name[1:]))
    return relation.xreplace({c: Symbol(f"C{k + 1}") for k, c in enumerate(present)})


def _explicit(relation: Eq, y: Expr) -> Eq:
    """y = ... if relation has a single solution for y, else relation.

    >>> from sympy import Eq, Function, log, symbols
    >>> x, c = symbols("x c")
    >>> y = Function("y")(x)
    >>> _explicit(Eq(log(y), c * x), y)
    Eq(y(x), exp(c*x))
    """
    try:
        solutions = solve(relation, y)
    except NotImplementedError:
        return relation
    if len(solutions) == 1 and not solutions[0].has(Integral):
        return Eq(y, solutions[0])
    return relation
