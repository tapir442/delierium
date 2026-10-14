"""Tests for delierium.optimal_systems: one-dimensional optimal systems (#44)."""

import random

import pytest
from sympy import Function, Matrix, Rational, diff, simplify, symbols

from delierium import (
    LieAlgebra,
    adjoint_invariants,
    adjoint_matrix,
    determining_janet_basis,
    optimal_system,
)
from delierium.optimal_systems import (
    _EPS,
    _Classifier,
    _constants,
    _heat,
    _kdv,
    _numerically_equivalent,
    _sl2,
    _so3,
)


def algebra(c):
    return LieAlgebra.from_structure_constants(c)


def representatives(c):
    return [str(r) for r in optimal_system(algebra(c)).representatives]


@pytest.mark.parametrize(
    "name, c, expected",
    [
        # Hydon, Example 10.1
        ("a(1)", _constants(2, {(1, 2): {1: 1}}), ["X1", "X2"]),
        # Hydon, Example 10.2
        ("sl(2)", _sl2(), ["X3", "X2", "X1 + X3"]),
        # Hydon, Exercise 10.2: all rotations are conjugate
        ("so(3)", _so3(), ["X3"]),
        # rotations and translations of the plane
        ("e(2)", _constants(3, {(1, 3): {2: 1}, (2, 3): {1: -1}}), ["X2", "X3"]),
        # Olver 3.3, Hu-Li-Chen (21)
        ("KdV", _kdv(), ["X1", "X2", "X3", "X2 + X3", "X2 - X3", "X4"]),
        # abelian: every line is its own class
        ("abelian", _constants(2, {}), ["X2", "X1 + X2*c1"]),
    ],
)
def test_optimal_systems(name, c, expected):
    assert representatives(c) == expected, name


@pytest.mark.slow
def test_heat_equation():
    """Hu-Li-Chen (49): v4 + a v3, v2 + v6 + b v3, v2 + v5/sqrt(2) (here
    v1 + v6), v3/4 +- v6 (here v6 +- v3), v6, v1 (here v5), v3."""
    result = optimal_system(algebra(_heat()))
    assert [str(r) for r in result.representatives] == [
        "X3",
        "X5",
        "X6",
        "X3 + X6",
        "-X3 + X6",
        "X1 + X6",
        "X3*c1 + X4",
        "X2 + X3*c1 + X6",
    ]
    # X6, X6 + X3, X6 - X3: separated only by an invariant of the stratum of
    # the vanishing invariants (Hu-Li-Chen (43))
    assert result.unseparated == [(2, 3), (2, 4), (3, 4)]


def test_from_generators():
    """y'' = y**-3 (Hydon, Example 10.3): sl(2), whose optimal system is the
    one of Example 10.2 in a different basis."""
    x, y = symbols("x y")
    sl2 = LieAlgebra([[1, 0], [x, y / 2], [x**2, x * y]], [x, y])
    result = sl2.optimal_system()
    assert len(result) == 3
    assert result.unseparated == []


def test_symmetry_algebra_of_an_equation():
    """From the Janet basis of the determining equations: the KdV equation."""
    x, t = symbols("x t")
    u = Function("u")(x, t)
    janet = determining_janet_basis(diff(u, t) + u * diff(u, x) + diff(u, x, 3), u, [x, t])
    result = LieAlgebra.from_janet_basis(janet).optimal_system()
    assert len(result) == 6


@pytest.mark.parametrize("c", [_sl2(), _so3(), _kdv(), _constants(2, {(1, 2): {1: 1}})])
def test_complete(c):
    """Random generators are equivalent to a representative (numerically,
    the parameters of the representatives among the unknowns)."""
    cl = _Classifier(c)
    families = cl.run()
    n = len(c)
    full = [tuple(int(i == j) for i in range(n + 1)) for j in range(n + 1)]
    matrices = [cl.matrix(s) for s in full * 2]
    # the move matrices of the adapted basis act on adapted coordinates
    inverse = cl.P.inv()
    rng = random.Random(0)
    for _ in range(5):
        v = [Rational(rng.randint(-5, 5)) for _ in range(n)]
        if not any(v):
            continue
        start = list(Matrix([v]) * inverse)
        found = False
        for f in families:
            target = list(Matrix([f.a]) * inverse)
            if any(not e.is_number for e in target):
                continue
            for sign in (1, -1):
                if _numerically_equivalent(
                    matrices, start, {i: sign * target[i] for i in range(n)}, 12
                ):
                    found = True
        # families with parameters: the scaled vector has to match up to the
        # parameter, checked through the parameter-free coordinates only
        if not found:
            for f in families:
                target = list(Matrix([f.a]) * inverse)
                fixed = {i: e for i, e in enumerate(target) if e.is_number}
                if len(fixed) < n and _numerically_equivalent(matrices, start, fixed, 12):
                    found = True
        assert found, v


def test_adjoint_matrix_is_a_representation():
    """A(x, s) A(x, t) = A(x, s + t)."""
    s, t = symbols("s t")
    kdv = algebra(_kdv())
    x = [1, 0, 0, 1]
    product = adjoint_matrix(kdv, x, s) * adjoint_matrix(kdv, x, t)
    assert simplify(product - adjoint_matrix(kdv, x, s + t)) == Matrix.zeros(4, 4)


def test_adjoint_invariants():
    """Hu-Li-Chen: a4 for KdV, (27) and (28) for the heat equation."""
    a = symbols("a1:7", real=True)
    assert adjoint_invariants(algebra(_kdv())) == [a[3]]
    delta1 = a[3] ** 2 - 4 * a[1] * a[5]
    delta2 = (
        a[3] ** 3
        + 2 * a[2] * a[3] ** 2
        - 4 * a[3] * a[1] * a[5]
        + 2 * a[3] * a[0] * a[4]
        - 8 * a[1] * a[2] * a[5]
        - 2 * a[1] * a[4] ** 2
        - 2 * a[0] ** 2 * a[5]
    )
    invariants = adjoint_invariants(algebra(_heat()))
    assert len(invariants) == 2
    assert simplify(invariants[0] ** 2 - delta1**2) == 0
    heat = algebra(_heat())
    for j in range(6):
        A = adjoint_matrix(heat, [int(i == j) for i in range(6)], _EPS)
        moved = dict(zip(a, Matrix([a]) * A, strict=True))
        for phi in [*invariants, delta2]:
            assert simplify(phi.xreplace(moved) - phi) == 0


def test_empty_algebra():
    assert len(optimal_system(LieAlgebra.from_structure_constants([]))) == 0
