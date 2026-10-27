"""Check delierium against the catalogue of equations with known symmetries.

For every entry of tests/symmetry_catalog.py: each listed generator solves the
determining equations, and the Janet basis of the determining equations has
the expected dimension of the symmetry algebra. A complete list of generators
of a finite algebra is closed under commutators.

Slow (the whole catalogue takes over a minute, 15 s with -n auto), so
deselected by default; run with

    uv run pytest -m slow -n auto tests/test_symmetry_catalog.py
"""

import random

import pytest
from sympy import (
    Derivative,
    Matrix,
    Poly,
    Rational,
    Symbol,
    cancel,
    expand,
    numer,
    oo,
    symbols,
    together,
)
from sympy.polys.matrices import DomainMatrix

from delierium import (
    LieAlgebra,
    determining_janet_basis,
    scaling_symmetries,
    verify_symmetries,
)

from .symmetry_catalog import CATALOG, INFINITE, KAMKE_FIRST_ORDER

pytestmark = pytest.mark.slow

# Known problems, by entry name. An xfail that starts passing fails the run
# (xfail_strict), so remove the entry here when the problem is fixed.
XFAIL: dict[str, str] = {}
# Known problems of the dimension check only (the generators are confirmed)
XFAIL_DIMENSION: dict[str, str] = {}
# Dimension checks too slow for the catalogue run; the dimension was computed once.
SLOW_DIMENSION: dict[str, str] = {}
# Algebra checks too slow for the catalogue run (over 45 s each); the dimension
# check of the entry stays
SLOW_ALGEBRA: set[str] = {
    "EqWorld ODE 3.32: x y'' = f(x**n exp(a y)) y'",
    "Painlevé V: y'' = (1/(2 y) + 1/(y - 1)) y'**2 - y'/x + (y - 1)**2 (a y + b/y)/x**2"
    " + c y/x + d y (y + 1)/(y - 1)",
}


def entry_param(entry, check):
    marks = []
    if entry.name in XFAIL:
        marks.append(pytest.mark.xfail(reason=XFAIL[entry.name]))
    elif check == "dimension" and entry.name in XFAIL_DIMENSION:
        marks.append(pytest.mark.xfail(reason=XFAIL_DIMENSION[entry.name]))
    elif check == "dimension" and entry.name in SLOW_DIMENSION:
        marks.append(pytest.mark.skip(reason=SLOW_DIMENSION[entry.name]))
    elif check == "janet algebra" and entry.name in SLOW_ALGEBRA:
        marks.append(pytest.mark.too_slow)
    elif check == "dimension" and entry.dimension is None:
        marks.append(pytest.mark.skip(reason="the sources disagree on the dimension"))
    return pytest.param(entry, marks=marks, id=entry.name)


def janet_basis(entry):
    indep, dep = entry.variables()
    return determining_janet_basis(entry.parsed_equations(), dep, indep)


@pytest.mark.parametrize("entry", [entry_param(e, "generators") for e in CATALOG if e.generators])
def test_generators(entry):
    """Every listed generator solves the determining equations."""
    indep, dep = entry.variables()
    eqs = entry.parsed_equations()
    for result in verify_symmetries(eqs, dep, indep, entry.parsed_generators()):
        assert result, (result.generator, result.nonzero_residues())


@pytest.mark.parametrize("entry", [entry_param(e, "dimension") for e in CATALOG])
def test_dimension(entry):
    """The Janet basis has the expected dimension of the symmetry algebra."""
    check_dimension(entry)


def check_dimension(entry):
    dimension = janet_basis(entry).rank()  # the dimension of the symmetry algebra
    assert (INFINITE if dimension == oo else dimension) == entry.dimension


@pytest.mark.parametrize(
    "entry",
    [
        entry_param(e, "algebra")
        for e in CATALOG
        if e.dimension not in (INFINITE, None) and len(e.generators) == e.dimension
    ],
)
def test_closed_under_commutators(entry):
    """The generators of a complete list span a Lie algebra: every commutator
    is a constant linear combination of them (NotClosedError otherwise)."""
    coordinates = [Symbol(v) for v in entry.independent + entry.dependent]
    algebra = LieAlgebra(entry.parsed_generators(), coordinates)
    assert len(algebra.structure_constants) == entry.dimension


@pytest.mark.parametrize(
    "entry",
    [
        entry_param(e, "janet algebra")
        for e in CATALOG
        if e.dimension not in (INFINITE, None) and len(e.generators) == e.dimension
    ],
)
def test_algebra_of_the_janet_basis(entry):
    """The Lie algebra from the Janet basis of the determining equations,
    without generators (LieAlgebra.from_janet_basis), is that of the
    complete list of generators: the same derived and lower central series,
    center, rank of the Killing form and, up to dimension 4, type."""
    coordinates = [Symbol(v) for v in entry.independent + entry.dependent]

    def invariants(algebra):
        return (
            algebra.dimension,
            algebra.derived_series(),
            algebra.lower_central_series(),
            algebra.center().rows,
            algebra.killing_form().rank(simplify=True),
            str(algebra.type()),
        )

    given = LieAlgebra(entry.parsed_generators(), coordinates)
    assert invariants(LieAlgebra.from_janet_basis(janet_basis(entry))) == invariants(given)


def pure_scaling(generator, coordinates):
    """The constants c with generator = sum c_i z_i d/dz_i, or None."""
    factors = [cancel(g / z) for g, z in zip(generator, coordinates, strict=True)]
    return None if any(f.has(*coordinates) for f in factors) else factors


@pytest.mark.parametrize("entry", [entry_param(e, "scalings") for e in CATALOG])
def test_scaling_symmetries(entry):
    """#48: the scalings found by linear algebra on the exponents are
    symmetries, and every listed generator that is a pure scaling lies in
    their span."""
    indep, dep = entry.variables()
    eqs = entry.parsed_equations()
    scalings = scaling_symmetries(eqs, dep, indep)
    for result in verify_symmetries(eqs, dep, indep, scalings):
        assert result, (result.generator, result.nonzero_residues())
    coordinates = [Symbol(v) for v in entry.independent + entry.dependent]
    span = Matrix([pure_scaling(g, coordinates) for g in scalings]) if scalings else None
    for generator in entry.parsed_generators():
        factors = pure_scaling(generator, coordinates)
        if factors is None or all(f == 0 for f in factors):
            continue
        assert span is not None, generator
        rank = span.rank(simplify=True)
        assert span.col_join(Matrix([factors])).rank(simplify=True) == rank, generator


def series_dimensions(F, x, y, p, orders, seed=0):
    """Dimensions of the truncated power series solutions (xi, eta of degree
    N around a regular point) of the symmetry condition of F(x, y, p) = 0,
    p = y', polynomial in p: F divides pr X F as polynomials in p. Only the
    Taylor coefficients of the pseudo-remainder below degree N are exact, so
    only those must vanish. Independent of delierium's determining equations;
    the dimensions settle at that of the symmetry algebra."""
    rng = random.Random(seed)
    params = sorted(F.free_symbols - {x, y, p}, key=str)
    F = numer(together(F.subs({a: Rational(rng.randint(2, 9), rng.randint(2, 5)) for a in params})))
    X, Y = Symbol("X"), Symbol("Y")
    while True:
        x0, y0 = (Rational(rng.randint(1, 9), rng.randint(2, 7)) for _ in range(2))
        G = expand(F.subs({x: x0 + X, y: y0 + Y}))
        if Poly(G, p).LC().subs({X: 0, Y: 0}) != 0:
            break
    result = []
    for N in orders:
        monomials = [X**i * Y**j for i in range(N + 1) for j in range(N + 1 - i)]
        a, b = symbols(f"a:{len(monomials)}"), symbols(f"b:{len(monomials)}")
        xi = sum(c * m for c, m in zip(a, monomials, strict=True))
        eta = sum(c * m for c, m in zip(b, monomials, strict=True))
        eta1 = eta.diff(X) + (eta.diff(Y) - xi.diff(X)) * p - xi.diff(Y) * p**2
        remainder = Poly(expand(xi * G.diff(X) + eta * G.diff(Y) + eta1 * G.diff(p)), p).prem(
            Poly(G, p)
        )
        equations = [
            v
            for coeff in remainder.all_coeffs()
            for (i, j), v in Poly(expand(coeff), X, Y).terms()
            if i + j < N
        ]
        unknowns = [*a, *b]
        rows = [[Poly(e, *unknowns).coeff_monomial(u) for u in unknowns] for e in equations]
        M = DomainMatrix.from_list_sympy(len(rows), len(unknowns), rows).to_field()
        result.append(len(unknowns) - M.rank())
    return result


@pytest.mark.parametrize("entry", [pytest.param(e, id=e.name) for e in KAMKE_FIRST_ORDER])
def test_first_order_finite_algebra(entry):
    """#28: the finite dimension of first order ODEs nonlinear in y', checked
    without delierium by power series."""
    (x,), (yf,) = entry.variables()
    y, p = Symbol("y"), Symbol("p")
    [eq] = entry.parsed_equations()
    F = eq.subs(Derivative(yf, x), p).subs(yf, y)
    assert series_dimensions(F, x, y, p, (4, 5)) == [entry.dimension] * 2
