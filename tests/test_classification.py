"""Tests for delierium.classification"""

import itertools
import random

import pytest
from sympy import Function, Rational, Symbol, diff, symbols

from delierium.classification import Case, _inequations, _solutions, classify
from delierium.infinitesimals import create_infinitesimals

from .symmetry_catalog import CATALOG
from .test_symmetry_catalog import determining_equations


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
    system = [e.xreplace(plain) for e in determining_equations(entry, infinitesimals)]
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
