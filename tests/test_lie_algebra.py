"""Lie algebras of generators (#11)."""

import pytest
from sympy import Matrix, Symbol, exp, sqrt

from delierium import LieAlgebra, NotClosedError, VectorField

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
