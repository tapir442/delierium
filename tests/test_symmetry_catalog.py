"""Check delierium against the catalogue of equations with known symmetries.

For every entry of tests/symmetry_catalog.py: each listed generator solves the
determining equations, and the Janet basis of the determining equations has
the expected dimension of the symmetry algebra. A complete list of generators
of a finite algebra is closed under commutators.

Slow (the whole catalogue takes over a minute, 15 s with -n auto), so
deselected by default; run with

    uv run pytest -m slow -n auto tests/test_symmetry_catalog.py
"""

import dataclasses
import random

import pytest
from sympy import Symbol, oo

from delierium import (
    LieAlgebra,
    determining_janet_basis,
    verify_symmetries,
)

from .symmetry_catalog import CATALOG, INFINITE

pytestmark = pytest.mark.slow

# Known problems, by entry name. An xfail that starts passing fails the run
# (xfail_strict), so remove the entry here when the problem is fixed.
XFAIL: dict[str, str] = {}
# Known problems of the dimension check only (the generators are confirmed)
XFAIL_DIMENSION: dict[str, str] = {}
# Dimension checks too slow for the catalogue run (minutes to half an hour even
# with random parameters); the dimension was computed once.
SLOW_DIMENSION: dict[str, str] = {
    "EqWorld 2.2.5: w_tt = [a (x + b)**n w_x]_x + f(w)": (
        "the Janet basis does not finish in 3 min, at random parameters took 25 min "
        "(dimension 1 at other random values)"
    ),
}
# The symbolic Janet basis does not finish in reasonable time (still running
# after 16 min), so the dimension is checked at random values of the
# parameters. It can only rise at special values, so random ones give the
# generic dimension (almost surely); the seed is the entry's name.
RANDOM_PARAMETERS = {
    "Kamke 6.171",
    "Kamke 6.219",
    "EqWorld 2.2.5: w_tt = [a (x + b)**n w_x]_x + f(w)",
}


def entry_param(entry, check):
    marks = []
    if entry.name in XFAIL:
        marks.append(pytest.mark.xfail(reason=XFAIL[entry.name]))
    elif check == "dimension" and entry.name in XFAIL_DIMENSION:
        marks.append(pytest.mark.xfail(reason=XFAIL_DIMENSION[entry.name]))
    elif check == "dimension" and entry.name in SLOW_DIMENSION:
        marks.append(pytest.mark.skip(reason=SLOW_DIMENSION[entry.name]))
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


def with_random_parameters(entry):
    """entry with random integers substituted for its parameters."""
    indep, _ = entry.variables()
    eqs = entry.parsed_equations()
    parameters = sorted(set().union(*(e.free_symbols for e in eqs)) - set(indep), key=str)
    rng = random.Random(entry.name)
    values = {p: rng.randint(2, 100) for p in parameters}
    return dataclasses.replace(entry, equations=tuple(str(e.subs(values)) for e in eqs))


@pytest.mark.parametrize("entry", [entry_param(e, "dimension") for e in CATALOG])
def test_dimension(entry):
    """The Janet basis has the expected dimension of the symmetry algebra."""
    if entry.name in RANDOM_PARAMETERS:
        entry = with_random_parameters(entry)
    check_dimension(entry)


@pytest.mark.too_slow
@pytest.mark.parametrize(
    "entry", [pytest.param(e, id=e.name) for e in CATALOG if e.name in RANDOM_PARAMETERS]
)
def test_dimension_symbolic(entry):
    """The entries of RANDOM_PARAMETERS as they are, for debugging; run with

    uv run pytest -m too_slow --run-too-slow tests/test_symmetry_catalog.py
    """
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
        entry_param(e, "algebra")
        for e in CATALOG
        if e.dimension not in (INFINITE, None)
        and len(e.generators) == e.dimension
        and e.name not in RANDOM_PARAMETERS
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
