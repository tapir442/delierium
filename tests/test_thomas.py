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


def test_rational_coefficients():
    """Denominators of numbers are cleared; other non-polynomials are refused."""
    assert decomposition([x / 2 - Rational(1, 3)], variables=[x]) == ["{3*x - 2 = 0}"]
    with pytest.raises(ValueError, match="not a polynomial"):
        thomas_decomposition([x - 1 / y], variables=[x, y])


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


def test_subresultants_of_a_defective_sequence():
    """F is a polynomial in y**3, so the subresultant sequence of F and dF/dy
    has degree gaps; SymPy's subresultants() then differs from the
    subresultants by polynomial factors (its resultant has a spurious factor
    9 z + 1, which lost the solutions at z = -1/9). res_0 is the resultant."""
    from sympy import cancel, diff, resultant

    z = symbols("z")
    F = expand(
        y**6 * z**4 + 2 * y**6 * z**2 + y**6 + 9 * y**3 * z**3
        + y**3 * z**2 + 9 * y**3 * z + y**3 - 27 * z**3
    )  # fmt: skip
    ring = _Ring([y, z])
    p, q = ring.check(F), ring.check(diff(F, y))
    res0 = ring.prs(p, q, y, 0)[1].as_expr()
    assert cancel(res0 / resultant(F, diff(F, y), y)).is_number
    # the regular subresultants are those of degree 3 and 2 (and 0)
    assert [i for i in range(5) if ring.prs(p, q, y, i)[1] != 0] == [0, 2, 3]


def test_defective_subresultant_sequence():
    """The fuzz case that lost the solutions at z = -1/9 through the
    defective subresultant sequence (see test_subresultants_of_a_defective_
    sequence); since the coefficients are reduced modulo 9 z + 1, the
    decomposition no longer meets that sequence here, but the case stays."""
    factorize = True
    z = symbols("z")
    p = (
        y**9 * z**6 + 2 * y**9 * z**4 + y**9 * z**2 + 9 * y**6 * z**5
        + y**6 * z**4 + 9 * y**6 * z**3 + y**6 * z**2 - 27 * y**3 * z**5
    )  # fmt: skip
    systems = [str(s) for s in thomas_decomposition([p, 9 * z + 1], [], [y, z], factorize)]
    assert any("6724*y**6 + 243" in s or "6724*y**7 + 243*y" in s for s in systems), systems
    special = [{z: Rational(-1, 9)}, {z: 0}, {z: Rational(-1, 3)}, {z: 1}]
    assert_partition([p], [], [y, z], special, factorize=factorize)


# ---------------------------------------------------------------------------
# fuzz test: random systems, the partition checked at points built level by
# level from rationals and roots (a numerical check with adaptive precision:
# the coefficients of a decomposition may have thousands of digits)


def _coefficient_digits(polys, variables):
    from sympy import Poly as SPoly

    return max(
        int(abs(int(c)).bit_length() * 0.30103) + 1
        for p in polys
        for c in SPoly(p, *variables).coeffs()
    )


def _mp(value, dps):
    import mpmath
    from sympy import Float

    re, im = value.as_real_imag()
    return mpmath.mpc(mpmath.mpf(Float(re, dps)), mpmath.mpf(Float(im, dps)))


def _sympy_point(point, dps):
    import mpmath
    from sympy import Float, I

    return {
        v: c if isinstance(c, Rational) else Float(mpmath.re(c), dps) + I * Float(mpmath.im(c), dps)
        for v, c in point.items()
    }


def _roots(p, v, point, dps):
    """roots of p in v at point: exact where all coordinates are rational
    (the rational ones stay Rational, the others from the square-free part),
    numerical otherwise"""
    import mpmath
    from sympy import Poly as SPoly
    from sympy import factor_list, quo, sqf_part

    with mpmath.workdps(dps):
        if all(isinstance(c, Rational) for c in point.values()):
            q = SPoly(expand(p.subs(point)), v)
            if q.degree() <= 0:
                return []
            exact = [
                Rational(-f.all_coeffs()[1], f.all_coeffs()[0])
                for f, _ in factor_list(q)[1]
                if f.degree() == 1
            ]
            q = SPoly(sqf_part(q.as_expr()), v)
            for r in exact:
                q = SPoly(quo(q.as_expr(), v - r, v), v)
        else:
            q = SPoly(expand(p.subs(_sympy_point(point, dps))), v)
            exact = []
        if q.degree() <= 0:
            return exact
        coeffs = [_mp(c.evalf(dps + 20), dps + 20) for c in q.all_coeffs()]
        found = mpmath.polyroots(coeffs, maxsteps=2000, extraprec=4 * dps, error=False)
        tiny = mpmath.mpf(10) ** -(dps // 3)  # an exact root 0 comes out tiny
        return exact + [mpmath.mpf(0) if abs(r) < tiny else r for r in found if abs(r) < 1e10]


def _point(path, dps):
    """the point of path [(v, Rational or (p, approximate root))] at dps"""
    import mpmath

    point = {}
    for v, source in path:
        if isinstance(source, Rational):
            point[v] = source
            continue
        p, approx = source
        found = _roots(p, v, point, dps)

        def distance(r, approx=approx):
            def mp(c):
                return mpmath.mpf(c.p) / c.q if isinstance(c, Rational) else c

            return abs(mp(r) - mp(approx))

        point[v] = min(found, key=distance) if found else approx
    return point


def _partition_fails(systems, equations, inequations, path, dps, tol):
    import mpmath

    point = _point(path, dps)

    def zero(e):
        with mpmath.workdps(dps):
            sub = _sympy_point(point, dps)
            terms = [abs(_mp(t.subs(sub).evalf(dps), dps)) for t in expand(e).as_ordered_terms()]
            return abs(_mp(e.subs(sub).evalf(dps), dps)) <= tol * max(sum(terms), 1)

    def holds(eqs, ineqs):
        return all(zero(e) for e in eqs) and not any(zero(e) for e in ineqs)

    inside = sum(holds(s.equations, s.inequations) for s in systems)
    return inside > 1 or inside != holds(equations, inequations)


def _random_system(rng, variables, degree):
    def poly():
        e = 0
        for _ in range(rng.randint(1, 3)):
            t = rng.choice([-2, -1, 1, 2, 3])
            for v in variables:
                t *= v ** rng.randint(0, degree if v == variables[0] else 2)
            e += t
        return expand(e)

    eqs = [e for e in (poly() for _ in range(rng.randint(0, 2))) if e != 0]
    ineqs = [e for e in (poly() for _ in range(rng.randint(0, 2))) if e != 0]
    return eqs, ineqs


@pytest.mark.slow
@pytest.mark.parametrize(
    "nvars, count, degree", [(2, 60, 3), (3, 8, 2)], ids=["2 variables", "3 variables"]
)
def test_fuzz_partition(nvars, count, degree):
    """Random systems: at points built from rationals and roots of the
    polynomials involved, the input holds iff exactly one simple system
    does. This found the defective subresultants, ResSplitDivide and the
    pquo of SymPy 1.14."""
    import random

    variables = list(symbols("x y z")[:nvars])
    rng = random.Random(58)
    for _ in range(count):
        eqs, ineqs = _random_system(rng, variables, degree)
        if not eqs and not ineqs:
            continue
        systems = thomas_decomposition(eqs, ineqs, variables)
        polys = [*eqs, *ineqs] + [p for s in systems for p in [*s.equations, *s.inequations]]
        high = max(200, 2 * _coefficient_digits(polys, variables) + 100)
        for _ in range(10):
            path = []
            for v in reversed(variables):
                point = _point(path, 60)
                options = [Rational(rng.randint(-9, 9), rng.randint(1, 5))]
                for p in polys:
                    if p.has(v) and not (p.free_symbols - {v} - set(point)):
                        options += [(p, r) for r in _roots(p, v, point, 60)]
                path.append((v, rng.choice(options)))
            if _partition_fails(systems, eqs, ineqs, path, 60, 1e-20):  # screen, then recheck
                assert not _partition_fails(
                    systems, eqs, ineqs, path, 4 * high, Rational(1, 10 ** (high // 2))
                ), (eqs, ineqs, [str(s) for s in systems], path)
