"""Types of Lie algebras in Lie's classification, Schwarz's names (#11)."""

import random

import pytest
from sympy import Matrix, Rational, Symbol, cancel

from delierium import LieAlgebra
from delierium.lie_algebra_types import LieAlgebraType, lie_algebra_type


def algebra(r, brackets):
    """structure constants from the nonvanishing [U_i, U_j] (1-based)"""
    c = [[[0] * r for _ in range(r)] for _ in range(r)]
    for (i, j), rhs in brackets.items():
        for k, v in rhs.items():
            c[i - 1][j - 1][k - 1] += v
            c[j - 1][i - 1][k - 1] -= v
    return c


def change_basis(c, P):
    """new basis V_a = sum_i P[a, i] U_i"""
    r = len(c)
    Pinv = P.inv()
    new = [[[0] * r for _ in range(r)] for _ in range(r)]
    for a in range(r):
        for b in range(r):
            vec = [
                sum(P[a, i] * P[b, j] * c[i][j][k] for i in range(r) for j in range(r))
                for k in range(r)
            ]
            coords = Matrix([vec]) * Pinv
            for m in range(r):
                new[a][b][m] = cancel(coords[m])
    return new


c_, a_, b_ = Rational(3, 5), Rational(-2, 7), Rational(5, 3)
SCHWARZ = {
    "l2,1": (2, {(1, 2): {1: 1}}),
    "l2,2": (2, {}),
    "l3,1": (3, {(1, 2): {1: 1}, (1, 3): {2: 2}, (2, 3): {3: 1}}),
    "l3,2(c = 3/5)": (3, {(1, 3): {1: 1}, (2, 3): {2: c_}}),
    "l3,2(c = -1)": (3, {(1, 3): {1: 1}, (2, 3): {2: -1}}),
    "l3,3": (3, {(1, 3): {1: 1}, (2, 3): {1: 1, 2: 1}}),
    "l3,4": (3, {(1, 3): {1: 1}}),
    "l3,5": (3, {(2, 3): {1: 1}}),
    "l3,6": (3, {}),
    "l4,1": (4, {(1, 2): {1: 1}, (1, 3): {2: 2}, (2, 3): {3: 1}}),
    "l4,2": (4, {(1, 4): {1: 1}, (2, 4): {1: 1, 2: 1}, (3, 4): {2: 1, 3: 1}}),
    "l4,3(c = 3/5)": (4, {(1, 4): {1: c_}, (2, 4): {2: c_ + 1}, (3, 4): {1: 1, 3: c_}}),
    "l4,4": (4, {(1, 4): {1: 2}, (2, 3): {1: 1}, (2, 4): {2: 1}, (3, 4): {2: 1, 3: 1}}),
    "l4,5(c = 3/5)": (4, {(1, 4): {1: c_}, (2, 3): {1: 1}, (2, 4): {2: 1}, (3, 4): {3: c_ - 1}}),
    "l4,6(a = -2/7, b = 5/3)": (4, {(1, 4): {1: 1}, (2, 4): {2: a_}, (3, 4): {3: b_}}),
    "l4,7": (4, {(1, 4): {1: 1}, (2, 4): {2: 1}, (3, 4): {2: 1, 3: 1}}),
    "l4,8": (4, {(1, 2): {2: 1}, (1, 3): {2: 1, 3: 1}}),
    "l4,9(a = -2/7)": (4, {(1, 2): {2: 1}, (1, 3): {3: a_}}),
    "l4,10": (4, {(1, 2): {2: 1}, (3, 4): {4: 1}}),
    "l4,11": (4, {(2, 4): {2: 1}, (3, 4): {1: 1}}),
    "l4,12": (4, {(1, 4): {1: 1}, (2, 3): {1: 1}, (2, 4): {2: 1}}),
    "l4,13": (4, {(1, 4): {2: 1}, (3, 4): {1: 1}}),
    "l4,14": (4, {(1, 4): {1: 1}, (2, 4): {2: 1}}),
    "l4,15": (4, {(1, 4): {1: 1}}),
    "l4,16": (4, {(1, 2): {3: 1}}),
    "l4,17": (4, {}),
}


@pytest.mark.parametrize("name", SCHWARZ)
def test_schwarz_listing_in_random_bases(name):
    """Each representative of Schwarz's listing, in three random bases."""
    r, brackets = SCHWARZ[name]
    c = algebra(r, brackets)
    rng = random.Random(name)
    for _ in range(3):
        while (P := Matrix(r, r, lambda i, j: rng.randint(-3, 3))).det() == 0:
            pass
        assert str(LieAlgebra.from_structure_constants(change_basis(c, P)).type()) == name


def test_symbolic_parameter_and_higher_dimension():
    x, y, n = Symbol("x"), Symbol("y"), Symbol("n")
    # d/dx, d/dy, x d/dx + n y d/dy: l3,2 with c = n or 1/n
    assert LieAlgebra([[1, 0], [0, 1], [x, n * y]], [x, y]).type() == LieAlgebraType(
        "l3,2", {"c": n}
    )
    sl3 = [(1, 0), (0, 1), (x, 0), (y, 0), (0, x), (0, y), (x**2, x * y), (x * y, y**2)]
    assert lie_algebra_type(LieAlgebra(sl3, [x, y])) is None
    assert str(LieAlgebraType("l4,6", {"a": 1, "b": 2})) == "l4,6(a = 1, b = 2)"
