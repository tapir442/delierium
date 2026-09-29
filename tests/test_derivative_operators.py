"""Tests for delierium.derivative_operators"""

import pytest
from sympy import Function, Symbol, diff, simplify, sin

from delierium import euler_operator, variational_derivative

x = Symbol("x")
U = Function("u")
u = U(x)


@pytest.mark.parametrize(
    ("L", "expected"),
    [
        (diff(u, x) ** 2 / 2, -diff(u, x, 2)),
        (u * diff(u, x, 2), 2 * diff(u, x, 2)),
        (diff(u, x, 2) ** 2, 2 * diff(u, x, 4)),
        (u * diff(u, x, 3), 0),
    ],
)
def test_variational_derivative(L, expected):
    assert simplify(variational_derivative(L, u) - expected) == 0


@pytest.mark.parametrize("L", [diff(u, x) ** 2 / 2 - u**2 / 2, u * diff(u, x) ** 2 + sin(u)])
def test_variational_derivative_is_euler_operator(L):
    assert simplify(variational_derivative(L, u) - euler_operator(L, [U], x)[0]) == 0
