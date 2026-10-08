"""Tests for delierium.classification"""

import itertools
import random

import pytest
from sympy import Function, Rational, Symbol, diff, oo, sqrt, symbols

from delierium.classification import (
    Case,
    _inequations,
    _solutions,
    classify,
    group_classification,
)
from delierium.infinitesimals import create_infinitesimals, overdetermined_system_pde

from .symmetry_catalog import CATALOG


def holds(case: Case, values: dict) -> bool:
    """values (all parameters) lie in case: its rule holds, no inequation fails."""
    if any(
        (v - value.subs(values)).simplify() != 0
        for p, value in case.rule.items()
        for v in [values[p]]
    ):
        return False
    return all(any(e.subs(values) != 0 for e in ineq) for ineq in case.inequations)


def assert_partition(cases: list[Case], parameters: list[Symbol], values: list) -> None:
    """Every point of values**parameters lies in exactly one case."""
    for point in itertools.product(values, repeat=len(parameters)):
        point = dict(zip(parameters, point, strict=True))
        assert sum(holds(c, point) for c in cases) == 1, point


def test_solutions_split_on_the_initial():
    """#58: solving for the leading symbol assumes its initial nonzero; the
    initial vanishing is a case of its own."""
    a, b, p, q = symbols("a b p q")
    # a*b = 0: b = 0 (any a), or a = 0 where b != 0
    assert _solutions([a * b]) == [({b: 0}, []), ({a: 0}, [b])]
    # p*q - 6*q + 8 = 0: p = 6 - 8/q needs q != 0; q = 0 gives 8 = 0
    [(rule, initials)] = _solutions([p * q - 6 * q + 8])
    assert list(rule) == [p] and (rule[p] - (6 - 8 / q)).simplify() == 0 and initials == [q]
    # several equations together; no real solution
    assert _solutions([a - 1, b - a]) == [({a: 1, b: 1}, [])]
    assert _solutions([a**2 + 1]) == []


def test_solutions_are_disjoint():
    """#58: the solutions come from a Thomas decomposition; where two roots
    coincide (a**2 = b at b = 0) that is a solution of its own."""
    a, b = symbols("a b")
    solutions = _solutions([a**2 - b])
    assert [rule for rule, _ in solutions] == [{a: -sqrt(b)}, {a: sqrt(b)}, {a: 0, b: 0}]
    assert [initials for _, initials in solutions] == [[b], [b], []]


def test_inequations_are_cleaned_up():
    a, b = symbols("a b")
    assert _inequations([[a], [-a], [b - b + 3], [a, 0 * b]]) == [[a]]
    assert _inequations([[a - a]]) is None


def test_classify_linear_system_is_a_partition():
    x, y, a, b = symbols("x y a b")
    z = Function("z")(x, y)
    S = [diff(z, x) - a * diff(z, y), b * diff(z, y, 2) - a * b * diff(z, y)]
    cases = classify(S, [z], [x, y])
    assert [str(c) for c in cases] == [
        "generic (a != 0; b != 0): rank 2",
        "a = 0 (b != 0): rank 2",
        "a = 0, b = 0: rank oo",
        "b = 0 (a != 0): rank oo",
    ]
    assert_partition(cases, [a, b], [0, 1, -2, Rational(3, 7)])


@pytest.mark.slow
def test_classify_anco():
    """Anco et al. u_t = -kappa p u_x**(p - 1) u_xx + c (a + u)**q: generic
    rank 3 (the catalogue dimension), larger algebras for c = 0, q = 0, ...;
    the 35 cases partition the parameter space."""
    entry = next(
        e for e in CATALOG if e.name.startswith("Anco et al.: u_t = -kappa p u_x**(p - 1)")
    )
    indep, dep = entry.variables()
    infinitesimals = create_infinitesimals(dep, indep)
    plain = {d: Symbol(d.func.__name__) for d in dep}
    determining = overdetermined_system_pde(
        entry.parsed_equations()[0], dep, indep, infinitesimals=infinitesimals
    )
    system = [e.xreplace(plain) for e in determining]
    functions = [infinitesimals[v].xreplace(plain) for v in indep + dep]
    cases = classify(system, functions, indep + [plain[d] for d in dep])
    assert cases[0].rank() == entry.dimension
    ranks = {str(c).split(" (")[0].split(":")[0]: c.rank() for c in cases}
    assert ranks["c = 0"] == 5
    assert ranks["q = 0"] == 5
    assert ranks["p = 2, q = 2"] == 4
    c, kappa, p, q = symbols("c kappa p q")
    rng = random.Random(1)
    special = [0, 1, -1, 2]
    for _ in range(200):
        point = {
            s: rng.choice([*special, Rational(rng.randint(3, 20), rng.randint(2, 9))])
            for s in (c, kappa, p, q)
        }
        point[Symbol("a")] = Rational(5, 3)
        assert sum(holds(case, point) for case in cases) == 1, point


def test_group_classification_porous_medium():
    """u_t = (u**sigma u_x)_x (Ovsiannikov): 4 symmetries in general, the
    heat equation for sigma = 0, a projective one more for sigma = -4/3."""
    x, t, sigma = symbols("x t sigma")
    u = Function("u")(x, t)
    cases = group_classification(diff(u, t) - diff(u**sigma * diff(u, x), x), u, [x, t])
    assert [str(c) for c in cases] == [
        "generic (sigma != 0; 3*sigma + 4 != 0): rank 4",
        "sigma = 0: rank oo",
        "sigma = -4/3: rank 5",
    ]
    assert_partition(cases, [sigma], [0, Rational(-4, 3), 1, Rational(2, 3)])


@pytest.mark.slow
def test_group_classification_with_source():
    """u_t = (u**sigma u_x)_x + a u**n (Dorodnitsyn): 3 symmetries in general,
    4 for n = 1, 5 for sigma = -4/3 with n = 1 or n = -1/3."""
    x, t, sigma, a, n = symbols("x t sigma a n")
    u = Function("u")(x, t)
    eq = diff(u, t) - diff(u**sigma * diff(u, x), x) - a * u**n
    cases = group_classification(eq, u, [x, t])
    ranks = {str(c).split(" (")[0].split(":")[0]: c.rank() for c in cases}
    assert ranks["generic"] == 3
    assert ranks["n = 1"] == 4
    assert ranks["n = 1, sigma = -4/3"] == 5
    assert ranks["sigma = -4/3, n = -1/3"] == 5
    assert ranks["a = 0, sigma = -4/3"] == 5
    assert_partition(cases, [sigma, a, n], [0, 1, Rational(-4, 3), Rational(-1, 3), 2])


@pytest.mark.slow
def test_group_classification_anco():
    """Computed from the equation itself, kappa = 0 (no x derivatives left)
    has infinitely many symmetries; the determining equations of the generic
    case, derived by solving for u_xx, do not show that."""
    x, t, a, c, kappa, p, q = symbols("x t a c kappa p q")
    u = Function("u")(x, t)
    eq = diff(u, t) + kappa * p * diff(u, x) ** (p - 1) * diff(u, x, 2) - c * (a + u) ** q
    cases = group_classification(eq, u, [x, t])
    ranks = {str(case).split(" (")[0].split(":")[0]: case.rank() for case in cases}
    assert ranks["generic"] == 3
    assert ranks["kappa = 0"] == oo
    assert ranks["c = 0"] == 5
    assert ranks["p = 2, q = 2"] == 4
    rng = random.Random(2)
    for _ in range(200):
        point = {
            s: rng.choice([0, 1, -1, 2, Rational(rng.randint(3, 20), rng.randint(2, 9))])
            for s in (c, kappa, p, q)
        }
        point[a] = Rational(5, 3)
        assert sum(holds(case, point) for case in cases) == 1, point
