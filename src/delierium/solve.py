"""Generators of the symmetry algebra from the determining equations by an
ansatz (#9): the infinitesimals as linear combinations of monomials in the
coordinates and in some functions of them (log x, sqrt(t), exp(t), ...); the
determining equations, linear, become a linear system for the coefficients,
whose nullspace gives the generators.

This finds the generators of polynomial (or elementary, with the functions)
type; the rank of the Janet basis tells whether all are found."""

import random
from collections.abc import Sequence
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
) -> list[Expr]:
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
        return []
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
            return coefficients
    except PolynomialError:
        pass
    # not a polynomial in them: e is linear in the unknowns, so its values at
    # random points are linear conditions (the result is verified at the end)
    rng = random.Random(len(unknowns))
    samples = []
    for _ in range(len(unknowns) + 3):
        point = {g: Rational(rng.randint(1, 97), rng.randint(1, 13)) for g in generators}
        samples.append(expand(polynomial.xreplace(point)))
    return [c for c in samples if c != 0 and not c.has(*generators)]


def ansatz_generators(
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    degree: int,
    functions: Sequence[Expr] = (),
    function_degree: int = 2,
) -> list[tuple[Expr, ...]]:
    """The solutions of the linear determining equations system in the
    unknown functions infinitesimals (of the coordinates) of the form: linear
    combinations of the monomials of degree <= degree in the coordinates
    times the monomials of degree <= function_degree in the functions. A
    basis of them, each a tuple with one component per infinitesimal.

    >>> from sympy import Function, symbols, diff
    >>> x, y = symbols("x y")
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> ansatz_generators([diff(X, y), diff(Y, y), diff(X, x)], [X, Y], [x, y], 1)
    [(1, 0), (0, 1), (0, x)]
    """
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
    rows = []
    for e in system:
        rows += [
            expand(r)
            for r in _identity_coefficients(e.subs(substitution).doit(), coordinates, flat)
        ]
    matrix = (
        Matrix([[r.coeff(c) for c in flat] for r in rows]) if rows else Matrix.zeros(1, len(flat))
    )
    result: list[tuple[Expr, ...]] = []
    for vector in matrix.nullspace(simplify=True):
        values = dict(zip(flat, vector, strict=True))
        result.append(tuple(simplify(sympify(c).xreplace(values)) for c in components))
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


def generators_by_ansatz(
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any = oo,
    max_degree: int = 3,
    functions: Sequence[Expr] | None = None,
) -> list[tuple[Expr, ...]]:
    """generators by ansatz_generators with increasing degree up to
    max_degree, until dimension many are found. Without functions given,
    monomials in the coordinates first, then the families of
    candidate_functions one by one, and finally those that helped,
    together. Every generator is checked against the system."""
    found = _search(system, infinitesimals, coordinates, dimension, max_degree, functions)
    return [g for g in found if _satisfies(system, infinitesimals, g)]


def _satisfies(
    system: Sequence[Expr], infinitesimals: Sequence[Expr], generator: Sequence[Expr]
) -> bool:
    substitution = {
        f.func: Lambda(f.args, c) for f, c in zip(infinitesimals, generator, strict=True)
    }
    return all(_simplified_residue(e.subs(substitution).doit()) == 0 for e in system)


def _search(
    system: Sequence[Expr],
    infinitesimals: Sequence[Expr],
    coordinates: Sequence[Basic],
    dimension: Any = oo,
    max_degree: int = 3,
    functions: Sequence[Expr] | None = None,
) -> list[tuple[Expr, ...]]:
    """generators by ansatz_generators with increasing degree up to
    max_degree, until dimension many are found. Without functions given,
    monomials in the coordinates first, then the families of
    candidate_functions one by one, and finally those that helped,
    together."""
    found: list[tuple[Expr, ...]] = []
    extra = list(functions) if functions is not None else []
    for degree in range(1, max_degree + 1):
        found = ansatz_generators(system, infinitesimals, coordinates, degree, extra)
        if len(found) >= dimension:
            return found
    if functions is not None:
        return found
    helpful: list[Expr] = []
    for family in candidate_functions(coordinates):
        more = ansatz_generators(system, infinitesimals, coordinates, max_degree, family)
        if len(more) > len(found):
            helpful += family
            if len(more) >= dimension:
                return more
    if helpful:
        more = ansatz_generators(system, infinitesimals, coordinates, max_degree, helpful)
        if len(more) > len(found):
            found = more
    return found
