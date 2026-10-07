"""Lie algebras of generators (#11)."""

import pytest
from sympy import Function, Matrix, Rational, Symbol, cancel, exp, sqrt

from delierium import (
    JanetBasis,
    LieAlgebra,
    Mgrevlex,
    NotClosedError,
    VectorField,
    symmetry_algebra,
)
from delierium.classification import _determining_janet_basis

x, y, t, u = Symbol("x"), Symbol("y"), Symbol("t"), Symbol("u")


def test_sl3_of_free_particle():
    """y'' = 0: the projective algebra sl(3), simple of dimension 8."""
    generators = [
        (1, 0),
        (0, 1),
        (x, 0),
        (y, 0),
        (0, x),
        (0, y),
        (x**2, x * y),
        (x * y, y**2),
    ]
    algebra = LieAlgebra(generators, [x, y])
    assert algebra.is_semisimple()
    assert algebra.derived_series() == [8]
    assert algebra.center().rows == 0


def test_sl2():
    """d/dx, x d/dx, x**2 d/dx: [X1, X2] = X1, [X1, X3] = 2 X2, [X2, X3] = X3."""
    algebra = LieAlgebra([[1], [x], [x**2]], [x])
    X1, X2, X3 = algebra.basis_symbols
    assert algebra.commutator_table() == Matrix([[0, X1, 2 * X2], [-X1, 0, X3], [-2 * X2, -X3, 0]])
    assert algebra.killing_form().det() != 0
    assert not algebra.is_solvable()


def test_heat_equation():
    """The six-dimensional finite part of the symmetries of u_t = u_xx
    (Olver, Example 2.41): solvable, not nilpotent; the center is u d/du."""
    generators = [
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, u),
        (x, 2 * t, 0),
        (2 * t, 0, -x * u),
        (4 * t * x, 4 * t**2, -(x**2 + 2 * t) * u),
    ]
    algebra = LieAlgebra(generators, [x, t, u])
    assert not algebra.is_solvable()  # it contains sl(2)
    assert algebra.center() == Matrix([[0, 0, 1, 0, 0, 0]])
    radical = LieAlgebra([generators[i] for i in (0, 2, 4)], [x, t, u])
    assert radical.is_nilpotent()  # the Heisenberg algebra
    assert radical.lower_central_series() == [3, 1, 0]


def test_parameters_and_transcendental_coefficients():
    """y'' = a y': d/dx, d/dy, y d/dy, exp(a x) d/dy, ... The structure
    constants depend on the parameter a."""
    a = Symbol("a")
    algebra = LieAlgebra([(1, 0), (0, 1), (0, exp(a * x))], [x, y])
    assert algebra.commutator_table()[0, 2] == a * algebra.basis_symbols[2]
    assert algebra.is_solvable() and not algebra.is_nilpotent()


def test_algebraic_coefficients():
    algebra = LieAlgebra([(1, 0), (0, sqrt(x))], [x, y])
    with pytest.raises(NotClosedError):
        algebra.commutator_table()  # [d/dx, sqrt(x) d/dy] = 1/(2 sqrt(x)) d/dy
    closed = LieAlgebra([(0, 1), (0, sqrt(x)), (0, y)], [x, y])
    assert closed.derived_series() == [3, 2, 0]


def test_not_closed():
    with pytest.raises(NotClosedError):
        LieAlgebra([(1, 0), (x**2, 0)], [x, y]).commutator_table()


def test_vector_field():
    rotation = VectorField([-y, x], [x, y])
    assert rotation(x**2 + y**2) == 0
    assert rotation.commutator(rotation).is_zero()
    with pytest.raises(ValueError):
        VectorField([1], [x, y])


def test_trigonometric_identities():
    """y'' + y = 0, the generators as LIEPDE gives them: [X1, X4] is
    (sin(x)**2 cos(x) + cos(x)**3) d/dy = X1 only by sin**2 + cos**2 = 1."""
    from sympy import cos, sin

    generators = [
        (0, cos(x)),
        (0, sin(x)),
        (2 * cos(x) ** 2 - 1, -2 * y * sin(x) * cos(x)),
        (sin(x) * cos(x), y * cos(x) ** 2),
        (0, y),
        (1, 0),
        (y * sin(x), y**2 * cos(x)),
        (y * cos(x), -(y**2) * sin(x)),
    ]
    assert LieAlgebra(generators, [x, y]).is_semisimple()  # sl(3)


@pytest.mark.parametrize(
    "generators",
    [
        # Kamke 6.134, (x - y) y'' + 2 (y' + 1) y' = 0: poles on y = x
        [
            (-y / (y - x), x / (y - x)),
            (-x * y / (y - x), x * y / (y - x)),
            ((x * y - x**2) / (y - x), (y**2 - x * y) / (y - x)),
            (x**3 / (y - x), -(y**3) / (y - x)),
            (1, 1),
            (x**3 * y / (y - x), -x * y**3 / (y - x)),
            (1 / (y - x), -1 / (y - x)),
            (x**2 * y / (y - x), -x * y**2 / (y - x)),
        ],
        # poles on y = 1: [X1, X3] = X1, [X3, X2] = -X2
        [(1 / (y - 1), 0), (1, 0), (x, 0)],
    ],
)
def test_poles_at_the_random_points(generators):
    """The structure constants do not depend on random points where a
    coefficient has a pole."""
    assert len(LieAlgebra(generators, [x, y]).structure_constants) == len(generators)


def test_symbolic_exponents():
    """Kamke 6.173, x y y'' + 2 x y'**2 + a y y' = 0, the generators as LIEPDE
    gives them: closed only if x**a, x**(a + 1) = x x**a and x**(2 - a) at a
    point are not taken as independent numbers."""
    a = Symbol("a")
    generators = [
        (0, y**-2),
        (0, y),
        (3 * x ** (a + 1) * y**3 / x**a, (1 - a) * y**4),
        (x**a * y**3, 0),
        (x ** (a + 1) / x**a, 0),
        (x**a, 0),
        (0, x ** (1 - a) / (a * y**2 - y**2)),
        (-3 * x ** (2 - a) / (a**2 - 2 * a + 1), x ** (1 - a) * y / (a - 1)),
    ]
    assert len(LieAlgebra(generators, [x, y]).structure_constants) == 8


def jacobi_holds(algebra):
    c, r = algebra.structure_constants, algebra.dimension
    return all(
        cancel(
            sum(
                c[i][j][m] * c[m][k][n] + c[j][k][m] * c[m][i][n] + c[k][i][m] * c[m][j][n]
                for m in range(r)
            )
        )
        == 0
        for i in range(r)
        for j in range(r)
        for k in range(r)
        for n in range(r)
    )


def test_from_structure_constants():
    """sl(2) from [H, E] = 2E, [H, F] = -2F, [E, F] = H; c must be antisymmetric."""
    c = [[[0] * 3 for _ in range(3)] for _ in range(3)]
    for i, j, k, v in [(0, 1, 1, 2), (0, 2, 2, -2), (1, 2, 0, 1)]:
        c[i][j][k], c[j][i][k] = v, -v
    sl2 = LieAlgebra.from_structure_constants(c)
    assert sl2.is_semisimple() and sl2.derived_series() == [3]
    c[0][1][1] = 1
    with pytest.raises(ValueError, match="antisymmetric"):
        LieAlgebra.from_structure_constants(c)


def test_from_janet_basis():
    """The Killing vectors of the plane, e(2), at the default point and at
    another one; z_x = 0 has infinitely many solutions."""
    xi, eta = Function("xi")(x, y), Function("eta")(x, y)
    killing = JanetBasis([xi.diff(x), eta.diff(y), xi.diff(y) + eta.diff(x)], [xi, eta], [x, y])
    for point in (None, (Rational(1, 2), -3)):
        e2 = LieAlgebra.from_janet_basis(killing, point)
        assert e2.dimension == 3 and jacobi_holds(e2)
        assert e2.derived_series() == [3, 2, 0] and e2.center().rows == 0
    with pytest.raises(ValueError, match="infinitely many"):
        LieAlgebra.from_janet_basis(JanetBasis([xi.diff(x)], [xi, eta], [x, y]))
    with pytest.raises(ValueError, match="one unknown function"):
        LieAlgebra.from_janet_basis(JanetBasis([xi.diff(x), xi.diff(y)], [xi], [x, y]))


def test_symmetry_algebra():
    """y'' = y'**2/y (sl(3)) is singular at y = 0; y'' = y**n for generic n:
    d/dx and a scaling, the 2-dimensional non-abelian algebra."""
    f = Function("f")(x)
    eq = f.diff(x, 2) - f.diff(x) ** 2 / f
    janet, _ = _determining_janet_basis(eq, f, [x], Mgrevlex)
    assert LieAlgebra.from_janet_basis(janet, (1, 2)).is_semisimple()
    with pytest.raises(ValueError, match="not a regular point"):
        LieAlgebra.from_janet_basis(janet, (1, 0))
    n = Symbol("n")
    algebra = symmetry_algebra(f.diff(x, 2) - f**n, f, [x])
    assert algebra.dimension == 2 and jacobi_holds(algebra)
    assert algebra.derived_series() == [2, 1, 0] and not algebra.is_nilpotent()
