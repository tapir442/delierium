"""Tests for delierium.thomas: the examples of Bächler, Gerdt,
Lange-Hegermann, Robertz (2012, arXiv:1108.0817), and that the simple
systems partition the solutions."""

import itertools

import pytest
from sympy import Rational, expand, roots, sqf_part, symbols

from delierium.thomas import SimpleSystem, _Ring, thomas_decomposition

x, y, a, b, c = symbols("x y a b c")


def decomposition(equations, inequations=(), variables=(), factorize=False):
    """The decomposition as strings; without factorizing, as in the paper."""
    return [str(s) for s in thomas_decomposition(equations, inequations, variables, factorize)]


def vanishes(e, point) -> bool:
    """e = 0 at point, numerically with 40 digits (the points are roots)."""
    return abs(e.subs(point).evalf(40)) < 1e-25


def holds(equations, inequations, point) -> bool:
    return all(vanishes(e, point) for e in equations) and not any(
        vanishes(e, point) for e in inequations
    )


def in_system(system: SimpleSystem, point) -> bool:
    return holds(system.equations, system.inequations, point)


@pytest.fixture(params=[False, True], ids=["plain", "factorize"])
def factorize(request):
    return request.param


def assert_partition(equations, inequations, variables, lower_points, factorize=True):
    """At every point (the lower variables from lower_points, the top
    variable a root of any polynomial involved or a random number): the
    input holds iff exactly one simple system does, and never two do."""
    systems = thomas_decomposition(equations, inequations, variables, factorize)
    top = variables[0]
    polys = [*equations, *inequations] + [
        p for s in systems for p in [*s.equations, *s.inequations]
    ]
    for lower in lower_points:
        values = {Rational(1, 3), Rational(-7, 2)}
        for p in polys:
            q = expand(p.subs(lower))
            if q.has(top) and not (q.free_symbols - {top}):
                values |= set(roots(sqf_part(q), top))
        for value in values:
            point = {**lower, top: value}
            inside = sum(in_system(s, point) for s in systems)
            assert inside <= 1, point
            assert inside == holds(equations, inequations, point), point


def test_example_2_1(factorize):
    """Two simple systems; the fibres have 3 and 2 points."""
    p = x**3 + (3 * y + 1) * x**2 + (3 * y**2 + 2 * y) * x + y**3
    assert decomposition([p], variables=[x, y]) == [
        "{x**3 + 3*x**2*y + x**2 + 3*x*y**2 + 2*x*y + y**3 = 0, 27*y**3 - 4*y != 0}",
        "{6*x**2 - 27*x*y**2 + 12*x*y + 6*x - 3*y**2 + 2*y = 0, 27*y**3 - 4*y = 0}",
    ]
    special = [{y: r} for r in roots(27 * y**3 - 4 * y, y)]
    assert_partition([p], [], [x, y], [*special, {y: 1}, {y: Rational(-2, 5)}], factorize=factorize)


def test_example_2_5(factorize):
    """a x**2 + b x + c: initial, discriminant and the degenerate cases
    (Example 4.1: the AlgebraicThomas output)."""
    p = a * x**2 + b * x + c
    assert decomposition([p], variables=[x, c, b, a]) == [
        "{a*x**2 + b*x + c = 0, 4*a*c - b**2 != 0, a != 0}",
        "{b*x + c = 0, b != 0, a = 0}",
        "{2*a*x + b = 0, 4*a*c - b**2 = 0, a != 0}",
        "{c = 0, b = 0, a = 0}",
    ]
    assert decomposition([p], [a], variables=[x, c, b, a]) == [
        "{a*x**2 + b*x + c = 0, 4*a*c - b**2 != 0, a != 0}",
        "{2*a*x + b = 0, 4*a*c - b**2 = 0, a != 0}",
    ]
    grid = [dict(zip((a, b, c), v, strict=True)) for v in itertools.product([0, 1, 2], repeat=3)]
    assert_partition([p], [], [x, c, b, a], grid, factorize=factorize)


def test_example_2_15_subresultants():
    ring = _Ring([x, y])
    p, q = ring.check(x**3 + y), ring.check(x**2 + x + y + 1)
    assert [ring.prs(p, q, x, i)[1].as_expr() for i in range(3)] == [
        y**3 + 7 * y**2 + 5 * y + 1,
        -y,
        1,
    ]
    assert ring.prs(p, q, x, 1)[0].as_expr() in (-x * y + 2 * y + 1, x * y - 2 * y - 1)


def test_example_2_23(factorize):
    """x**2 = a: two roots, or one for a = 0."""
    assert decomposition([x**2 - a], variables=[x, a]) == [
        "{-a + x**2 = 0, a != 0}",
        "{x = 0, a = 0}",
    ]
    assert_partition([x**2 - a], [], [x, a], [{a: 0}, {a: 4}, {a: -3}], factorize=factorize)


def test_example_2_26(factorize):
    """An inequation divides the equation where they share a root."""
    assert decomposition([x**2 + x + 1], [x + a], variables=[x, a]) == [
        "{x**2 + x + 1 = 0, a**2 - a + 1 != 0}",
        "{-a + x + 1 = 0, a**2 - a + 1 = 0}",
    ]
    special = [{a: r} for r in roots(a**2 - a + 1, a)]
    assert_partition(
        [x**2 + x + 1], [x + a], [x, a], [*special, {a: 0}, {a: 2}], factorize=factorize
    )


def test_two_equations_and_inequations(factorize):
    """Two equations of the same leader (conditional gcd), and inequations
    of the same leader (their lcm)."""
    eqs = [x**2 - 1, x**2 - y]
    assert_partition(eqs, [], [x, y], [{y: 1}, {y: 0}, {y: 4}], factorize=factorize)
    # the lcm of two inequations; for y = 1 they coincide (paper's 2.20 would lose it)
    assert decomposition([], [x - y, x - 1], variables=[x, y]) == [
        "{x**2 - x*y - x + y != 0, y - 1 != 0}",
        "{x - 1 != 0, y - 1 = 0}",
    ]
    assert_partition([], [x - y, x - 1], [x, y], [{y: 1}, {y: 2}], factorize=factorize)
    assert_partition([x**3 - y], [x - 1], [x, y], [{y: 1}, {y: 8}, {y: 0}], factorize=factorize)


def test_unknown_symbols():
    with pytest.raises(ValueError, match="not among the variables"):
        thomas_decomposition([a * x - 1], variables=[x])


def test_factorize():
    """Splitting on factors: y*(x - 1) = 0 into y = 0 and y != 0, x = 1."""
    assert decomposition([y * (x - 1)], variables=[x, y], factorize=True) == [
        "{y = 0}",
        "{x - 1 = 0, y != 0}",
    ]
    assert decomposition([], [y * (x - 1)], variables=[x, y], factorize=True) == [
        "{x - 1 != 0, y != 0}"
    ]
    # Example 2.1: 27 y**3 - 4 y = y (27 y**2 - 4), and for y = 0 the
    # equation is x**2 (x + 1): two systems more than without factorizing
    p = x**3 + (3 * y + 1) * x**2 + (3 * y**2 + 2 * y) * x + y**3
    assert decomposition([p], variables=[x, y], factorize=True) == [
        "{x**3 + 3*x**2*y + x**2 + 3*x*y**2 + 2*x*y + y**3 = 0, 27*y**3 - 4*y != 0}",
        "{x = 0, y = 0}",
        "{x + 1 = 0, y = 0}",
        "{27*x**2 + 54*x*y + 9*x + 9*y - 2 = 0, 27*y**2 - 4 = 0}",
    ]


@pytest.mark.parametrize(
    "factorize", [True, pytest.param(False, marks=pytest.mark.slow)], ids=["factorize", "plain"]
)
def test_defective_subresultant_sequence(factorize):
    """F is a polynomial in y**3, so its subresultant sequence with dF/dy
    is defective; SymPy's subresultant PRS has a spurious factor 9 z + 1 in
    the resultant there, which lost the solutions at z = -1/9 (fuzz test)."""
    z = symbols("z")
    p = (
        y**9 * z**6 + 2 * y**9 * z**4 + y**9 * z**2 + 9 * y**6 * z**5
        + y**6 * z**4 + 9 * y**6 * z**3 + y**6 * z**2 - 27 * y**3 * z**5
    )  # fmt: skip
    systems = [str(s) for s in thomas_decomposition([p, 9 * z + 1], [], [y, z], factorize)]
    assert any("6724*y**6 + 243" in s or "6724*y**7 + 243*y" in s for s in systems), systems
    special = [{z: Rational(-1, 9)}, {z: 0}, {z: Rational(-1, 3)}, {z: 1}]
    assert_partition([p], [], [y, z], special, factorize=factorize)
