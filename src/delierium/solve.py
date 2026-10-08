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
from itertools import combinations_with_replacement
from typing import Any

from sympy import (
    Basic,
    Derivative,
    Dummy,
    Expr,
    Function,
    Lambda,
    Matrix,
    Mul,
    Poly,
    PolynomialError,
    Pow,
    Rational,
    S,
    Subs,
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

from delierium.infinitesimals import _simplified_residue

__all__ = ["ansatz_generators", "candidate_functions", "generators_by_ansatz"]


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


def ansatz_generators(  # pylint: disable=too-many-arguments,too-many-positional-arguments,too-many-locals
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    degree: int,
    functions: Sequence[Expr] = (),
    function_degree: int = 2,
    trace: bool | int = False,
) -> list[tuple[Expr, ...]]:
    """The solutions of the linear determining equations system in the
    unknown functions infinitesimals (of the coordinates) of the form: linear
    combinations of the monomials of degree <= degree in the coordinates
    times the monomials of degree <= function_degree in the functions. A
    basis of them, each a tuple with one component per infinitesimal.

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
    basis: list[Expr] = []
    for g in _monomials(functions, function_degree):
        for m in _monomials(coordinates, degree):
            gm = expand(powsimp(g * m))
            if gm != 0 and gm not in basis:
                basis.append(gm)
    unknowns = [[Dummy() for _ in basis] for _ in infinitesimals]
    components = [sum(c * m for c, m in zip(cs, basis, strict=True)) for cs in unknowns]
    substitution = {
        f.func: Lambda(f.args, c) for f, c in zip(infinitesimals, components, strict=True)
    }
    flat = [c for cs in unknowns for c in cs]
    out(
        f"ansatz: degree {degree}, functions {list(functions)}, {len(basis)} monomials, "
        f"{len(flat)} unknowns"
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
    result: list[tuple[Expr, ...]] = []
    for vector in matrix.nullspace(simplify=True):
        values = dict(zip(flat, vector, strict=True))
        result.append(tuple(simplify(sympify(c).xreplace(values)) for c in components))
    methods = ", ".join(f"{m} {n}" for m, n in sorted(how.items()))
    out(
        f"  {len(system)} equations -> {len(rows)} conditions ({methods}); "
        f"rank {len(flat) - len(result)} -> {len(result)} solutions ({time.time() - start:.1f} s)"
    )
    for g in result:
        out(f"    {g}", 2)
    return result


def candidate_functions(coordinates: Sequence[Basic]) -> list[list[Expr]]:
    """Families of functions that often occur in generators, for each
    coordinate v: [log v], [sqrt v, 1/v], [exp v, exp(-v)]; with
    function_degree 2 also their squares and products (log(v)**2,
    1/sqrt(v), exp(2v), ...)."""
    result: list[list[Expr]] = []
    for v in coordinates:
        w = sympify(v)
        result += [[log(w)], [sqrt(w), 1 / w], [exp(w), exp(-w)]]
    return result


def generators_by_ansatz(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any = oo,
    max_degree: int = 3,
    functions: Sequence[Expr] | None = None,
    trace: bool | int = False,
) -> list[tuple[Expr, ...]]:
    """generators by ansatz_generators with increasing degree up to
    max_degree, until dimension many are found. Without functions given,
    monomials in the coordinates first, then the families of
    candidate_functions one by one, and finally those that helped,
    together. Every generator is checked against the system.

    trace (1 or True): print every attempt and decision; 2: also the
    determining equations with their conditions and the solutions of every
    attempt (see ansatz_generators)."""
    out = _tracer(trace)
    out(
        f"solving {len(system)} determining equations for {list(infinitesimals)} "
        f"in {list(coordinates)}, dimension {dimension}"
    )
    found = _search(system, infinitesimals, coordinates, dimension, max_degree, functions, trace)
    result = [g for g in found if _satisfies(system, infinitesimals, g)]
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


def _search(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any = oo,
    max_degree: int = 3,
    functions: Sequence[Expr] | None = None,
    trace: bool | int = False,
) -> list[tuple[Expr, ...]]:
    """generators by ansatz_generators with increasing degree up to
    max_degree, until dimension many are found. Without functions given,
    monomials in the coordinates first, then the families of
    candidate_functions one by one, and finally those that helped,
    together."""
    out = _tracer(trace)
    found: list[tuple[Expr, ...]] = []
    extra = list(functions) if functions is not None else []
    for degree in range(1, max_degree + 1):
        found = ansatz_generators(system, infinitesimals, coordinates, degree, extra, trace=trace)
        if len(found) >= dimension:
            out(f"-> {len(found)} = dimension: done")
            return found
    if functions is not None:
        out("-> functions given: no further search")
        return found
    out(f"-> {len(found)} < dimension {dimension}: trying functions of the coordinates")
    helpful: list[Expr] = []
    for family in candidate_functions(coordinates):
        more = ansatz_generators(
            system, infinitesimals, coordinates, max_degree, family, trace=trace
        )
        if len(more) > len(found):
            helpful += family
            out(f"-> {family} helps: {len(more)} > {len(found)}")
            if len(more) >= dimension:
                out(f"-> {len(more)} = dimension: done")
                return more
    if helpful:
        out(f"-> combining the families that helped: {helpful}")
        more = ansatz_generators(
            system, infinitesimals, coordinates, max_degree, helpful, trace=trace
        )
        if len(more) > len(found):
            found = more
    else:
        out("-> no family of functions helps")
    return found
