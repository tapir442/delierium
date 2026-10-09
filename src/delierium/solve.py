"""Generators of the symmetry algebra from the determining equations (#9).

solve_determining_equations applies a list of steps to a SolverState (the
remaining equations, the unknown functions and constants, the
infinitesimals in terms of them), each step a function of the state; write
your own and add it to the list. The default steps:

* integrate_one_term: an equation c * d^alpha g = 0 is integrated, the
  result substituted, the equations split again;
* solve_linear_ode: a linear ODE in one unknown of one variable by dsolve;
* ansatz: the remaining unknowns as linear combinations of monomials in
  their variables and in some functions of them (log x, sqrt(t), exp(t),
  ...): the equations become a linear system for the coefficients, whose
  nullspace gives the generators.

This finds generators of elementary type; the rank of the Janet basis tells
whether all are found."""

import random
import time
from collections import Counter
from collections.abc import Callable, Sequence
from itertools import combinations_with_replacement
from typing import Any, cast

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
    "SolverState",
    "Step",
    "ansatz",
    "ansatz_generators",
    "candidate_functions",
    "default_steps",
    "integrate_one_term",
    "reduce_determining_equations",
    "run_steps",
    "solve_determining_equations",
    "solve_linear_ode",
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
    # functions of the coordinates that are no unknowns (an arbitrary f(x) of
    # the equation, its derivatives) first, so that v = s**L does not reach
    # into them
    opaque = {
        a: Dummy()
        for a in sorted(
            (a for a in e.atoms(AppliedUndef, Derivative, Subs) if a.has(*coordinates)),
            key=lambda a: -a.count_ops(),
        )
    }
    e = e.xreplace(opaque)
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
    generators = [*variables, *opaque.values(), *replacements.values()]
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
# Helpers of the steps

_FAST_HINTS = (
    "1st_linear",
    "nth_linear_constant_coeff_homogeneous",
    "nth_linear_constant_coeff_undetermined_coefficients",
    "nth_linear_euler_eq_homogeneous",
    "nth_linear_euler_eq_nonhomogeneous_undetermined_coefficients",
    "separable",
    "nth_algebraic",
)


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


def _integration(
    g: Expr, orders: dict[Basic, int], state: "SolverState"
) -> tuple[Expr, list[Expr]]:
    """The general solution of d^orders g = 0: the sum over the variables v
    of polynomials of degree < orders[v] in v with coefficients new functions
    of the other arguments of g (constants if there are none)."""
    args = list(g.args)
    new: list[Expr] = []
    solution: Expr = S.Zero
    for v, n in orders.items():
        rest = [a for a in args if a != v]
        for p in range(n):
            h = state.fresh_function(rest)
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
    e: Expr, functions: Sequence[Expr], state: "SolverState"
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
    except (NotImplementedError, ValueError, TypeError, IndexError):
        return None
    for hint in hints:
        if hint not in _FAST_HINTS:
            continue
        try:
            solution = dsolve(e, g, hint=hint)
        except (NotImplementedError, ValueError, TypeError, IndexError):
            continue
        if isinstance(solution, list) or solution.rhs.has(Integral):
            continue
        rhs = solution.rhs
        constants = sorted(
            (s for s in rhs.free_symbols if s.name.startswith("C") and s not in e.free_symbols),
            key=str,
        )
        new = [state.fresh_constant() for _ in constants]
        return g, rhs.xreplace(dict(zip(constants, new, strict=True))), new
    return None


# --------------------------------------------------------------------------
# The solver: a list of steps, applied to a SolverState one after the other.


class SolverState:  # pylint: disable=too-many-instance-attributes
    """What a step of the solver works on.

    system: the remaining linear equations (each = 0)
    functions: the remaining unknown functions, each of some coordinates
    constants: the remaining unknown constants
    infinitesimals: the infinitesimals in terms of these unknowns
    coordinates, dimension: of the symmetry algebra (dimension oo if
        infinite or unknown)
    generators: None until a step finds them; setting it ends the solver
    history: what the steps did, one line each

    Steps change the state by substitute() (an unknown by an expression in
    new unknowns from fresh_function, fresh_constant) or by setting
    generators, and report with log()."""

    def __init__(
        self,
        system: Sequence[Expr],
        infinitesimals: Sequence[Expr],
        coordinates: Sequence[Basic],
        dimension: Any = oo,
        trace: bool | int = False,
    ) -> None:
        self.system: list[Expr] = _cleaned(system)
        self.functions: list[Expr] = list(infinitesimals)
        self.constants: list[Symbol] = []
        self.infinitesimals: list[Expr] = list(infinitesimals)
        self.coordinates: list[Basic] = list(coordinates)
        self.dimension = dimension
        self.generators: list[tuple[Expr, ...]] | None = None
        self.history: list[str] = []
        self.trace = trace
        self._out = _tracer(trace)
        self._names = _Names(system)

    def log(self, message: str, level: int = 1) -> None:
        """Record message (level 1) and print it if trace is at least level."""
        if level <= 1:
            self.history.append(message)
        self._out(message, level)

    def fresh_function(self, arguments: Sequence[Basic]) -> Expr:
        """A new unknown function of arguments (a new constant if there are
        none); substitute() adds it to the unknowns."""
        if not arguments:
            return self.fresh_constant()
        return Function(self._names.fresh("F"))(*arguments)  # pylint: disable=not-callable

    def fresh_constant(self) -> Symbol:
        return Symbol(self._names.fresh("c"))

    def substitute(self, unknown: Expr, solution: Expr, new: Sequence[Expr] = ()) -> None:
        """Replace the unknown (a function or a constant) by solution, an
        expression in the new unknowns new (from fresh_function,
        fresh_constant), in the equations and the infinitesimals; split the
        equations again by the coordinates their unknowns do not depend on."""
        if unknown in self.functions:
            self.functions.remove(unknown)
            substitution: dict[Any, Any] = {unknown.func: Lambda(unknown.args, solution)}
        else:
            self.constants.remove(cast(Symbol, unknown))
            substitution = {unknown: solution}
        self.functions += [f for f in new if not isinstance(f, Symbol)]
        self.constants += [f for f in new if isinstance(f, Symbol)]
        self.infinitesimals = [
            expand(r.subs(substitution).doit()) if r.has(*substitution) else r
            for r in self.infinitesimals
        ]
        split: list[Expr] = []
        for e in self.system:
            e = _substitute(e, substitution) if e.has(*substitution) else e
            split += _split_free(e, self.functions, self.coordinates)
        self.system = _cleaned(split)


type Step = Callable[[SolverState], bool]


def integrate_one_term(state: SolverState) -> bool:
    """A step: integrate an equation of one term, c * d^alpha g = 0 (c free
    of the unknowns): g is a polynomial of degree < alpha_v in each variable
    v of alpha with new unknown functions of the other arguments as
    coefficients. Derivatives in one variable come before mixed ones, the
    lowest order first (g_xx = 0 before g_xxx = 0, which then vanishes)."""
    candidates = []
    for e in state.system:
        found = _one_term(e, state.functions, state.constants)
        if found is not None:
            g, orders = found
            candidates.append((len(orders), sum(orders.values()), str(e), e, g, orders))
    if not candidates:
        return False
    _, _, _, e, g, orders = min(candidates, key=lambda c: c[:3])
    solution, new = _integration(g, orders, state) if orders else (S.Zero, [])
    state.log(f"  integrate: {e} = 0  ->  {g} = {solution}")
    state.substitute(g, solution, new)
    unknowns = state.functions + state.constants
    state.log(f"    {len(state.system)} equations left, unknowns {unknowns}", 2)
    return True


def solve_linear_ode(state: SolverState) -> bool:
    """A step: an equation that is a linear ODE in a single unknown function
    of one variable (constants may occur), solved by a fast method of dsolve
    without integrals; its constants of integration become new unknown
    constants."""
    for e in state.system:
        ode = _ode_solution(e, state.functions, state)
        if ode is not None:
            g, solution, new = ode
            state.log(f"  solve: {e} = 0  ->  {g} = {solution}  (dsolve)")
            state.substitute(g, solution, new)
            return True
    return False


def ansatz(max_degree: int = 3, functions: Sequence[Expr] | None = None) -> Step:
    """A step that ends the solver: the remaining unknown functions as linear
    combinations of monomials in their variables (and functions of them,
    see candidate_functions) by ansatz_generators, with increasing degree up
    to max_degree until dimension many generators are found."""

    def step(state: SolverState) -> bool:
        def attempt(degree: int, extra: Sequence[Expr]) -> list[tuple[Expr, ...]]:
            return ansatz_generators(
                state.system,
                state.functions,
                state.coordinates,
                degree,
                extra,
                trace=state.trace,
                constants=state.constants,
                result=state.infinitesimals,
            )

        state.generators = _search(
            attempt,
            state.system,
            state.coordinates,
            state.dimension,
            max_degree if state.functions else 1,
            functions,
            state.trace,
        )
        return True

    step.__name__ = f"ansatz(max_degree={max_degree})"
    return step


def default_steps(max_degree: int = 3, functions: Sequence[Expr] | None = None) -> list[Step]:
    """integrate_one_term, solve_linear_ode, ansatz(max_degree, functions)."""
    return [integrate_one_term, solve_linear_ode, ansatz(max_degree, functions)]


def run_steps(state: SolverState, steps: Sequence[Step], max_iterations: int = 1000) -> None:
    """Apply the steps: the first one that changes the state, then again from
    the first one; until a step sets the generators or none changes the
    state."""
    for _ in range(max_iterations):
        if state.generators is not None:
            return
        if not any(step(state) for step in steps):
            return
    state.log(f"stopped after {max_iterations} steps")


def solve_determining_equations(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any = oo,
    steps: Sequence[Step] | None = None,
    trace: bool | int = False,
    reduction_system: Sequence[Expr] | None = None,
) -> list[tuple[Expr, ...]]:
    """Generators of the solutions of the linear determining equations system
    in the unknown functions infinitesimals (of the coordinates), each a
    tuple with one component per infinitesimal.

    The steps (default: default_steps(): integrate_one_term,
    solve_linear_ode, ansatz()) are applied to a SolverState of
    reduction_system (if given, e.g. the Janet basis of system) by
    run_steps. A step is a function of the state that returns whether it
    changed it; write your own and put it into the list. If the steps end
    without generators and no equations and unknown functions are left, the
    generators are those of the remaining constants. Every generator is
    checked against system; the simplest come first.

    trace (1 or True): print every step and decision; 2: also the details of
    the steps (see ansatz_generators).

    >>> from sympy import Function, symbols, diff
    >>> x, y = symbols("x y")
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> system = [diff(X, y), diff(Y, x), diff(X, x) + Y / y, diff(Y, y) - Y / y]
    >>> solve_determining_equations(system, [X, Y], [x, y], 2)
    [(1, 0), (-x, y)]

    A step of your own, here one that only reports, before the default ones:

    >>> def report(state):
    ...     print(len(state.system), "equations")
    ...     return False
    >>> generators = solve_determining_equations(
    ...     system, [X, Y], [x, y], 2, steps=[report, *default_steps()]
    ... )
    4 equations
    3 equations
    2 equations
    1 equations
    0 equations
    """
    state = SolverState(
        reduction_system if reduction_system is not None else system,
        infinitesimals,
        coordinates,
        dimension,
        trace,
    )
    state.log(
        f"solving {len(state.system)} determining equations for {list(infinitesimals)} "
        f"in {list(coordinates)}, dimension {dimension}"
    )
    run_steps(state, default_steps() if steps is None else steps)
    found = state.generators
    if found is None:
        found = _from_constants(state)
    result = sorted(
        (g for g in found if _satisfies(system, infinitesimals, g)),
        key=lambda g: (sum(sympify(c).count_ops() for c in g), str(g)),
    )
    for g in found:
        if g not in result:
            state.log(f"dropped, does not satisfy the determining equations: {g}")
    complete = "complete" if len(result) == dimension else "incomplete"
    state.log(f"result: {len(result)} generators of dimension {dimension}, {complete}")
    return result


def _from_constants(state: SolverState) -> list[tuple[Expr, ...]]:
    """Without equations and unknown functions left: one generator per
    remaining constant."""
    if state.system or state.functions:
        state.log("no generators: equations or unknown functions left")
        return []
    return [
        tuple(
            expand(r.xreplace({d: int(d == c) for d in state.constants}))
            for r in state.infinitesimals
        )
        for c in state.constants
    ]


def reduce_determining_equations(
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    trace: bool | int = False,
) -> SolverState:
    """The state after integrate_one_term and solve_linear_ode, without the
    ansatz: what remains to be solved.

    >>> from sympy import Function, symbols, diff
    >>> x, y = symbols("x y")
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> r = reduce_determining_equations([diff(X, y), diff(Y, y, 2), diff(Y, y, 3)], [X, Y], [x, y])
    >>> r.infinitesimals, r.system
    ([F1(x), y*F3(x) + F2(x)], [])
    """
    state = SolverState(system, infinitesimals, coordinates, trace=trace)
    run_steps(state, [integrate_one_term, solve_linear_ode])
    state.log(
        f"reduced: {len(state.system)} equations in {state.functions + state.constants}; "
        f"infinitesimals {state.infinitesimals}"
    )
    return state
