"""Generators of the symmetry algebra from the determining equations by an
ansatz (#9): the infinitesimals as linear combinations of monomials in the
coordinates and in some functions of them (log x, sqrt(t), exp(t), ...); the
determining equations, linear, become a linear system for the coefficients,
whose nullspace gives the generators.

This finds the generators of polynomial (or elementary, with the functions)
type; the rank of the Janet basis tells whether all are found."""

import random
import time
from collections import Counter
from collections.abc import Callable, Sequence
from dataclasses import dataclass, field
from itertools import combinations_with_replacement
from typing import Any

from sympy import (
    Add,
    Basic,
    Derivative,
    Dummy,
    Expr,
    Function,
    Integral,
    Lambda,
    Matrix,
    Mul,
    Poly,
    PolynomialError,
    Pow,
    Rational,
    S,
    Subs,
    Symbol,
    classify_ode,
    dsolve,
    exp,
    expand,
    expand_power_exp,
    ilcm,
    log,
    numer,
    oo,
    powsimp,
    simplify,
    sqrt,
    sympify,
    together,
)
from sympy.core.function import AppliedUndef

from delierium.infinitesimals import _simplified_residue

__all__ = [
    "Reduced",
    "ansatz_generators",
    "candidate_functions",
    "generators_by_ansatz",
    "reduce_determining_equations",
]


def _monomials(variables: Sequence[Basic], degree: int) -> list[Expr]:
    """The distinct products of at most degree of the variables; with
    functions among them some coincide (sqrt(t)**2 = t, exp(t)*exp(-t) = 1)."""
    result: list[Expr] = [S.One]
    for d in range(1, degree + 1):
        for c in combinations_with_replacement(variables, d):
            m = expand(powsimp(Mul(*c)))
            if m not in result:
                result.append(m)
    return result


def _identity_coefficients(
    e: Expr, coordinates: Sequence[Basic], unknowns: Sequence[Basic]
) -> tuple[list[Expr], str]:
    """The conditions for e = 0 identically in the coordinates: e as a
    polynomial in the coordinates and in the other functions of them (each
    replaced by a new symbol), its coefficients. Roots of a coordinate v are
    written with one new variable (v = s**L), exponentials exp(c*v) as
    powers of exp(v), so that they are not taken as independent. Treating
    related functions (log(v), u**a) as independent can only give more
    conditions, so the solutions remain solutions. Where e is no
    polynomial in them, its values at random points."""
    e = sympify(expand_power_exp(expand(e)))
    variables: list[Basic] = []
    for v in coordinates:
        exponents = [p.exp for p in e.atoms(Pow) if p.base == v and p.exp.is_Rational]
        lcm = ilcm(1, 1, *[r.q for r in exponents])
        if lcm > 1:
            w = Dummy(positive=True)
            e = powsimp(e.xreplace({v: w**lcm}), force=True)
            v = w
        e_v = Dummy(positive=True)
        replaced: Basic = e.replace(
            lambda a, v=v: isinstance(a, exp) and (a.args[0] / v).is_Rational,
            lambda a, v=v, e_v=e_v: e_v ** (a.args[0] / v),
        )
        variables.append(v)
        if replaced != e:
            variables.append(e_v)
            e = replaced
    numerator: Basic = numer(together(e))
    if numerator == 0:
        return [], "vanishes"
    atoms = [
        a
        for a in numerator.atoms(Function, Pow, Derivative, Subs)
        if a.has(*variables)
        and not (isinstance(a, Pow) and a.exp.is_Integer and a.base in variables)
    ]
    replacements = {a: Dummy() for a in sorted(atoms, key=lambda a: -a.count_ops())}
    polynomial = expand(numerator.xreplace(replacements))
    generators = [*variables, *replacements.values()]
    try:
        coefficients = Poly(polynomial, *generators).coeffs()
        if not any(c.has(*generators) for c in coefficients):
            return coefficients, "split"
    except PolynomialError:
        pass
    # not a polynomial in them: e is linear in the unknowns, so its values at
    # random points are linear conditions (the result is verified at the end)
    rng = random.Random(len(unknowns))
    samples = []
    for _ in range(len(unknowns) + 3):
        point = {g: Rational(rng.randint(1, 97), rng.randint(1, 13)) for g in generators}
        samples.append(expand(polynomial.xreplace(point)))
    return [c for c in samples if c != 0 and not c.has(*generators)], "sampled"


def _tracer(trace: bool | int) -> Callable[..., None]:
    """A function printing its arguments if trace is at least its level."""
    level = int(trace)

    def out(message: str, at: int = 1) -> None:
        if level >= at:
            print(message, flush=True)

    return out


def ansatz_generators(  # pylint: disable=too-many-arguments,too-many-locals
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    degree: int,
    functions: Sequence[Expr] = (),
    function_degree: int = 2,
    trace: bool | int = False,
    *,
    constants: Sequence[Symbol] = (),
    result: Sequence[Expr] | None = None,
) -> list[tuple[Expr, ...]]:
    """The solutions of the linear determining equations system in the
    unknown functions infinitesimals (each of some of the coordinates) of
    the form: linear combinations of the monomials of degree <= degree in
    their variables times the monomials of degree <= function_degree in the
    functions of them. A basis of them, each a tuple with one component per
    infinitesimal; or, with result given (expressions in the unknown
    functions and the unknown constants), per expression of result.

    trace (1 or True): print the size of the ansatz and of the linear
    system, its rank and the number of solutions; 2: also every determining
    equation with its conditions and the solutions.

    >>> from sympy import Function, symbols, diff
    >>> x, y = symbols("x y")
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> ansatz_generators([diff(X, y), diff(Y, y), diff(X, x)], [X, Y], [x, y], 1)
    [(1, 0), (0, 1), (0, x)]
    >>> _ = ansatz_generators([diff(X, y), diff(Y, y), diff(X, x)], [X, Y], [x, y], 1, trace=True)
    ansatz: degree 1, functions [], 3 monomials, 6 unknowns
      3 equations -> 3 conditions (split 3); rank 3 -> 3 solutions (0.0 s)
    """
    out = _tracer(trace)
    start = time.time()
    bases: dict[Expr, list[Expr]] = {}
    for f in infinitesimals:
        variables = [v for v in coordinates if v in f.args]
        own = [g for g in functions if g.free_symbols <= set(variables)]
        basis: list[Expr] = []
        for g in _monomials(own, function_degree):
            for m in _monomials(variables, degree):
                gm = expand(powsimp(g * m))
                if gm != 0 and gm not in basis:
                    basis.append(gm)
        bases[f] = basis
    unknowns = {f: [Dummy() for _ in bases[f]] for f in infinitesimals}
    components = {
        f: sum(c * m for c, m in zip(unknowns[f], bases[f], strict=True)) for f in infinitesimals
    }
    substitution = {f.func: Lambda(f.args, components[f]) for f in infinitesimals}
    flat = [c for f in infinitesimals for c in unknowns[f]] + list(constants)
    sizes = sorted({len(b) for b in bases.values()})
    out(
        f"ansatz: degree {degree}, functions {list(functions)}, "
        f"{sizes[0] if len(sizes) == 1 else sizes} monomials, {len(flat)} unknowns"
    )
    rows = []
    how: Counter[str] = Counter()
    for k, e in enumerate(system):
        conditions, method = _identity_coefficients(e.subs(substitution).doit(), coordinates, flat)
        how[method] += 1
        rows += [expand(r) for r in conditions]
        out(f"    equation {k}: {e}  ->  {len(conditions)} conditions ({method})", 2)
    matrix = (
        Matrix([[r.coeff(c) for c in flat] for r in rows]) if rows else Matrix.zeros(1, len(flat))
    )
    targets = (
        [components[f] for f in infinitesimals]
        if result is None
        else [r.subs(substitution).doit() for r in result]
    )
    solutions: list[tuple[Expr, ...]] = []
    for vector in matrix.nullspace(simplify=True):
        values = dict(zip(flat, vector, strict=True))
        solutions.append(tuple(simplify(sympify(c).xreplace(values)) for c in targets))
    methods = ", ".join(f"{m} {n}" for m, n in sorted(how.items()))
    out(
        f"  {len(system)} equations -> {len(rows)} conditions ({methods}); "
        f"rank {len(flat) - len(solutions)} -> {len(solutions)} solutions "
        f"({time.time() - start:.1f} s)"
    )
    for g in solutions:
        out(f"    {g}", 2)
    return solutions


def candidate_functions(
    coordinates: Sequence[Basic], system: Sequence[Expr] = ()
) -> list[list[Expr]]:
    """Families of functions that often occur in generators, for each
    coordinate v: [log v], [sqrt v, 1/v], [exp v, exp(-v)]; with
    function_degree 2 also their squares and products (log(v)**2,
    1/sqrt(v), exp(2v), ...). Those the system points to come first: a
    negative or fractional power of v ([sqrt v, 1/v], and [log v], which
    integrates 1/v), log(v), exp(c v). Denominators are cleared in the
    determining equations: 1/v shows as a power of v in some terms of an
    equation but not in others."""
    families: list[tuple[int, list[Expr]]] = []
    atoms: set[Basic] = set().union(*(e.atoms(Pow, log, exp) for e in system))
    for v in coordinates:
        w = sympify(v)
        powers = _divides_unevenly(w, system) or any(
            isinstance(a, Pow) and a.base == w and not (a.exp.is_Integer and a.exp > 0)
            for a in atoms
        )
        logs = any(isinstance(a, log) and a.has(w) for a in atoms)
        exps = any(isinstance(a, exp) and a.has(w) for a in atoms)
        families += [
            (0 if powers or logs else 1, [log(w)]),
            (0 if powers else 1, [sqrt(w), 1 / w]),
            (0 if exps else 1, [exp(w), exp(-w)]),
        ]
    return [family for _, family in sorted(families, key=lambda f: f[0])]


def _divides_unevenly(v: Basic, system: Sequence[Expr]) -> bool:
    """Whether in an equation of the system v divides some terms but not all:
    the equation divided by v has a pole at v = 0."""
    for e in system:
        powers = set()
        for term in Add.make_args(expand(e)):
            power = 0
            for factor in Mul.make_args(term):
                base, exponent = factor.as_base_exp()
                if base == v and exponent.is_Integer:
                    power += int(exponent)
            powers.add(power)
        if len(powers) > 1:
            return True
    return False


def generators_by_ansatz(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any = oo,
    max_degree: int = 3,
    functions: Sequence[Expr] | None = None,
    trace: bool | int = False,
    reduce: bool = True,
    reduction_system: Sequence[Expr] | None = None,
) -> list[tuple[Expr, ...]]:
    """Generators of the solutions of the determining equations system.

    With reduce (the default), reduce_determining_equations first (of
    reduction_system if given, e.g. the Janet basis of system): equations of
    one term are integrated, simple ODEs solved. Then the remaining unknown
    functions by ansatz_generators with increasing degree up to max_degree,
    until dimension many are found. Without functions given, monomials
    first, then the families of candidate_functions one by one, and finally
    those that helped, together. Every generator is checked against the
    system; the simplest come first.

    trace (1 or True): print every step and decision; 2: also the
    determining equations with their conditions and the solutions of every
    attempt (see ansatz_generators)."""
    out = _tracer(trace)
    out(
        f"solving {len(system)} determining equations for {list(infinitesimals)} "
        f"in {list(coordinates)}, dimension {dimension}"
    )
    if reduce:
        r = reduce_determining_equations(
            reduction_system if reduction_system is not None else system,
            infinitesimals,
            coordinates,
            trace,
        )

        def attempt(degree: int, extra: Sequence[Expr]) -> list[tuple[Expr, ...]]:
            return ansatz_generators(
                r.system,
                r.functions,
                coordinates,
                degree,
                extra,
                trace=trace,
                constants=r.constants,
                result=r.infinitesimals,
            )

        remaining = r.system
        degrees = max_degree if r.functions else 1
    else:

        def attempt(degree: int, extra: Sequence[Expr]) -> list[tuple[Expr, ...]]:
            return ansatz_generators(
                system, infinitesimals, coordinates, degree, extra, trace=trace
            )

        remaining = list(system)
        degrees = max_degree
    found = _search(attempt, remaining, coordinates, dimension, degrees, functions, trace)
    result = sorted(
        (g for g in found if _satisfies(system, infinitesimals, g)),
        key=lambda g: (sum(sympify(c).count_ops() for c in g), str(g)),
    )
    for g in found:
        if g not in result:
            out(f"dropped, does not satisfy the determining equations: {g}")
    complete = "complete" if len(result) == dimension else "incomplete"
    out(f"result: {len(result)} generators of dimension {dimension}, {complete}")
    return result


def _satisfies(
    system: Sequence[Expr], infinitesimals: Sequence[Expr], generator: Sequence[Expr]
) -> bool:
    substitution = {
        f.func: Lambda(f.args, c) for f, c in zip(infinitesimals, generator, strict=True)
    }
    return all(_simplified_residue(e.subs(substitution).doit()) == 0 for e in system)


type _Attempt = Callable[[int, Sequence[Expr]], list[tuple[Expr, ...]]]


def _search(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    attempt: _Attempt,
    system: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any,
    max_degree: int,
    functions: Sequence[Expr] | None,
    trace: bool | int,
) -> list[tuple[Expr, ...]]:
    """attempt (an ansatz of a degree, with functions) with increasing degree
    up to max_degree, until dimension many are found. Without functions
    given, monomials first, then the families of candidate_functions one by
    one (those the system points to first, each with increasing degree),
    and finally those that helped, together."""
    out = _tracer(trace)
    found: list[tuple[Expr, ...]] = []
    extra = list(functions) if functions is not None else []
    for degree in range(1, max_degree + 1):
        found = attempt(degree, extra)
        if len(found) >= dimension:
            out(f"-> {len(found)} = dimension: done")
            return found
    if functions is not None:
        out("-> functions given: no further search")
        return found
    if not system:
        return found
    out(f"-> {len(found)} < dimension {dimension}: trying functions of the coordinates")
    return _search_functions(attempt, system, coordinates, dimension, max_degree, found, trace)


def _search_functions(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    attempt: _Attempt,
    system: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any,
    max_degree: int,
    found: list[tuple[Expr, ...]],
    trace: bool | int,
) -> list[tuple[Expr, ...]]:
    """The families of candidate_functions one by one, each with increasing
    degree, then those that helped together."""
    out = _tracer(trace)
    helpful: list[Expr] = []
    for family in candidate_functions(coordinates, system):
        more = found
        # an infinite algebra never stops early: only the highest degree
        for degree in range(1 if dimension != oo else max_degree, max_degree + 1):
            result = attempt(degree, family)
            if len(result) > len(more):
                more = result
            if len(more) >= dimension:
                break
        if len(more) > len(found):
            helpful += family
            out(f"-> {family} helps: {len(more)} > {len(found)}")
            if len(more) >= dimension:
                out(f"-> {len(more)} = dimension: done")
                return more
    if not helpful:
        out("-> no family of functions helps")
        return found
    out(f"-> combining the families that helped: {helpful}")
    more = attempt(max_degree, helpful)
    return more if len(more) > len(found) else found


# --------------------------------------------------------------------------
# Reduction before the ansatz: integrate the equations with one term,
# substitute, split, solve simple ODEs.

_FAST_HINTS = (
    "1st_linear",
    "nth_linear_constant_coeff_homogeneous",
    "nth_linear_constant_coeff_undetermined_coefficients",
    "nth_linear_euler_eq_homogeneous",
    "nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients",
    "separable",
    "nth_algebraic",
)


@dataclass
class Reduced:
    """The determining equations after the reduction: the remaining
    equations in the remaining unknowns (functions of some of the
    coordinates, and constants), and the infinitesimals in terms of them."""

    system: list[Expr]
    functions: list[Expr]
    constants: list[Symbol]
    infinitesimals: list[Expr]  # the original ones, expressed in the new unknowns
    steps: list[str] = field(default_factory=list)


class _Names:
    """Fresh names for the new unknown functions F1, F2, ... and constants
    c1, c2, ..., not used in the system."""

    def __init__(self, system: Sequence[Expr]) -> None:
        self.used = {str(s) for e in system for s in e.free_symbols} | {
            a.func.__name__ for e in system for a in e.atoms(AppliedUndef)
        }
        self.count = 0

    def fresh(self, prefix: str) -> str:
        while True:
            self.count += 1
            name = f"{prefix}{self.count}"
            if name not in self.used:
                self.used.add(name)
                return name


def _one_term(
    e: Expr, functions: Sequence[Expr], constants: Sequence[Symbol] = ()
) -> tuple[Expr, dict[Basic, int]] | None:
    """(g, orders) if e is c * (a derivative of the unknown g) with c free of
    the unknowns (functions and constants: c3 * g' = 0 does not give g' = 0),
    orders the derivative's order per variable (empty for g itself); None
    otherwise."""
    terms = Add.make_args(expand(e))
    if len(terms) != 1 or terms[0].has(*constants):
        return None
    unknown_parts = [f for f in Mul.make_args(terms[0]) if any(f.has(g) for g in functions)]
    if len(unknown_parts) != 1:
        return None
    part = unknown_parts[0]
    if part in functions:
        return part, {}
    if isinstance(part, Derivative) and part.expr in functions:
        orders: dict[Basic, int] = {}
        for v, n in part.variable_count:
            orders[v] = orders.get(v, 0) + int(n)
        return part.expr, orders
    return None


def _integration(g: Expr, orders: dict[Basic, int], names: _Names) -> tuple[Expr, list[Expr]]:
    """The general solution of d^orders g = 0: the sum over the variables v
    of polynomials of degree < orders[v] in v with coefficients new functions
    of the other arguments of g (constants if there are none)."""
    args = list(g.args)
    new: list[Expr] = []
    solution: Expr = S.Zero
    for v, n in orders.items():
        rest = [a for a in args if a != v]
        for p in range(n):
            h = Function(names.fresh("F"))(*rest) if rest else Symbol(names.fresh("c"))
            new.append(h)
            solution += v**p * h
    return solution, new


def _split_free(e: Expr, functions: Sequence[Expr], coordinates: Sequence[Basic]) -> list[Expr]:
    """e = 0 split by the coordinates none of its unknowns depends on (as
    polynomial coefficients, functions of them taken as independent); [e]
    if it cannot be split."""
    unknowns = [f for f in functions if e.has(f.func)]
    occurring = set()
    for a in e.atoms(AppliedUndef):
        if a.func in {f.func for f in unknowns}:
            occurring |= a.free_symbols
    free = [v for v in coordinates if v not in occurring and e.has(v)]
    if not free:
        return [e]
    numerator = numer(together(e))
    atoms = [
        a
        for a in numerator.atoms(Function, Pow)
        if a.has(*free)
        and not a.has(*[f.func for f in unknowns])
        and not (isinstance(a, Pow) and a.exp.is_Integer and a.base in free)
    ]
    replacements = {a: Dummy() for a in sorted(atoms, key=lambda a: -a.count_ops())}
    polynomial = expand(numerator.xreplace(replacements))
    gens = [*free, *replacements.values()]
    try:
        coefficients = Poly(polynomial, *gens).coeffs()
    except PolynomialError:
        return [e]
    if any(c.has(*gens) for c in coefficients):
        return [e]
    return [c for c in coefficients if c != 0]


def _substitute(e: Expr, substitution: dict[Any, Lambda]) -> Expr:
    return expand(numer(together(e.subs(substitution).doit())))


def _cleaned(system: Sequence[Expr]) -> list[Expr]:
    result: list[Expr] = []
    for e in system:
        e = expand(numer(together(e)))
        if e != 0 and e not in result and -e not in result:
            result.append(e)
    return result


def _ode_solution(
    e: Expr, functions: Sequence[Expr], names: _Names
) -> tuple[Expr, Expr, list[Symbol]] | None:
    """(g, solution, new constants) if e is a linear ODE in a single unknown
    g of one variable (constants may occur) that a fast dsolve method
    solves without integrals; None otherwise."""
    present = [f for f in functions if e.has(f.func)]
    if len(present) != 1 or len(present[0].args) != 1:
        return None
    g = present[0]
    try:
        hints = classify_ode(e, g)
    except (NotImplementedError, ValueError, TypeError):
        return None
    for hint in hints:
        if hint not in _FAST_HINTS:
            continue
        try:
            solution = dsolve(e, g, hint=hint)
        except (NotImplementedError, ValueError, TypeError):
            continue
        if isinstance(solution, list) or solution.rhs.has(Integral):
            continue
        rhs = solution.rhs
        constants = sorted(
            (s for s in rhs.free_symbols if s.name.startswith("C") and s not in e.free_symbols),
            key=str,
        )
        new = [Symbol(names.fresh("c")) for _ in constants]
        return g, rhs.xreplace(dict(zip(constants, new, strict=True))), new
    return None


def reduce_determining_equations(  # pylint: disable=too-many-locals
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    trace: bool | int = False,
) -> Reduced:
    """Integrate the equations of one term (c * d^alpha g = 0), substitute
    the result in all others and split them by the coordinates their
    unknowns no longer depend on; repeat, then solve the linear ODEs in one
    unknown of one variable. Of the equations with one term, those with a
    derivative in one variable come first, the lowest order first (g_xx = 0
    before g_xxx = 0, which then vanishes).

    >>> from sympy import Function, symbols, diff
    >>> x, y = symbols("x y")
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> r = reduce_determining_equations([diff(X, y), diff(Y, y, 2), diff(Y, y, 3)], [X, Y], [x, y])
    >>> r.infinitesimals, r.system
    ([F1(x), y*F3(x) + F2(x)], [])
    """
    out = _tracer(trace)
    names = _Names(system)
    functions: list[Expr] = list(infinitesimals)
    constants: list[Symbol] = []
    representation: list[Expr] = list(infinitesimals)
    equations = _cleaned(system)
    steps: list[str] = []

    def apply(g: Expr, solution: Expr, new: Sequence[Expr]) -> None:
        nonlocal equations, representation
        substitution = {g.func: Lambda(g.args, solution)}
        functions.remove(g)
        functions.extend(f for f in new if not isinstance(f, Symbol))
        constants.extend(f for f in new if isinstance(f, Symbol))
        representation = [
            expand(r.subs(substitution).doit()) if r.has(g.func) else r for r in representation
        ]
        split: list[Expr] = []
        for e in equations:
            e = _substitute(e, substitution) if e.has(g.func) else e
            split += _split_free(e, functions, coordinates)
        equations = _cleaned(split)

    while True:
        candidates = []
        for e in equations:
            found = _one_term(e, functions, constants)
            if found is not None:
                g, orders = found
                candidates.append((len(orders), sum(orders.values()), str(e), e, g, orders))
        if candidates:
            _, _, _, e, g, orders = min(candidates, key=lambda c: c[:3])
            if orders:
                solution, new = _integration(g, orders, names)
            else:
                solution, new = S.Zero, []
            steps.append(f"{e} = 0  ->  {g} = {solution}")
            out(f"  integrate: {steps[-1]}")
            apply(g, solution, new)
            out(f"    {len(equations)} equations left, unknowns {functions + constants}", 2)
            continue
        for e in equations:
            ode = _ode_solution(e, functions, names)
            if ode is not None:
                g, solution, new = ode
                steps.append(f"{e} = 0  ->  {g} = {solution}  (dsolve)")
                out(f"  solve: {steps[-1]}")
                apply(g, solution, new)
                break
        else:
            break
    out(
        f"reduced: {len(equations)} equations in {functions + constants}; "
        f"infinitesimals {representation}"
    )
    return Reduced(equations, functions, constants, representation, steps)
