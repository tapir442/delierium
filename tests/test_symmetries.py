"""Tests for delierium.symmetries"""

import pytest
from sympy import Function, diff, exp, log, oo, symbols

from delierium import determining_janet_basis, lie_symmetries


def test_ode_with_a_finite_algebra():
    """u'' + u'/x - e^u = 0 (Baumann, 4.3.3): two symmetries, l2,1."""
    x, u_ = symbols("x u")
    u = Function("u")(x)
    s = lie_symmetries(diff(u, x, 2) + diff(u, x) / x - exp(u), u, x)
    assert s.dimension == 2 and s.is_finite
    assert s.coordinates == [x, u_]
    assert s.algebra.dimension == 2
    assert s.algebra.type().name == "l2,1"
    generators = [(-x / 2, 1), (-x / 2 * (log(x) - 1), log(x))]
    assert all(s.verify(generators))


def test_same_as_determining_janet_basis():
    x, t = symbols("x t")
    u = Function("u")(x, t)
    burgers = diff(u, t) + u * diff(u, x) - diff(u, x, 2)
    s = lie_symmetries(burgers, u, [x, t])
    assert s.dimension == determining_janet_basis(burgers, u, [x, t]).rank() == 5
    assert len(s.infinitesimals) == 3


def test_infinite_algebra():
    x, t = symbols("x t")
    u = Function("u")(x, t)
    s = lie_symmetries(diff(u, t) - diff(u, x, 2), u, [x, t])
    assert s.dimension == oo and not s.is_finite
    with pytest.raises(ValueError):
        _ = s.algebra


def test_assumptions_and_parameters():
    """u'' = a u'^2 / u: the initial and the parameter cases."""
    x, a = symbols("x a")
    u = Function("u")(x)
    s = lie_symmetries(diff(u, x, 2) - a * diff(u, x) ** 2 / u, u, x)
    assert s.dimension == 8
    assert isinstance(s.assumptions, list)
    assert isinstance(s.parameter_conditions, list)
