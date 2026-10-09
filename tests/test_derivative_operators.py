"""Tests for delierium.derivative_operators"""

import pytest
from sympy import Function, Rational, Symbol, diff, simplify, sin, sqrt, symbols

from delierium import (
    adjoint_frechet_derivative,
    euler_operator,
    frechet_derivative,
    variational_derivative,
)

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


# Baumann, Symmetry Analysis of Differential Equations with Mathematica,
# chapter 3: explicit results of the derivative operators (#50)


def test_euler_operator_baumann():
    g = Symbol("g", positive=True)
    xp = Symbol("x", positive=True)
    up = U(xp)
    ux, uxx = diff(up, xp), diff(up, xp, 2)
    # Example 1 of 3.6.4: the brachistochrone, a cycloid
    [e] = euler_operator(sqrt((1 + ux**2) / (2 * g * xp)), [U], xp)
    expected = (ux + ux**3 - 2 * xp * uxx) / (
        2 * sqrt(2) * sqrt(g) * xp ** Rational(3, 2) * (1 + ux**2) ** Rational(3, 2)
    )
    assert simplify(e - expected) == 0
    # Example 1 of 3.6.6: the wave equation in 2 + 1 dimensions
    x1, x2, x3 = symbols("x1 x2 x3")
    w = U(x1, x2, x3)
    density = (diff(w, x1) ** 2 - diff(w, x2) ** 2 - diff(w, x3) ** 2) / 2
    assert euler_operator(density, [U], (x1, x2, x3)) == [
        -diff(w, x1, 2) + diff(w, x2, 2) + diff(w, x3, 2)
    ]
    # Example 2 of 3.6.6: coupled nonlinear diffusion of u and v
    t = Symbol("t")
    V = Function("v")
    u, v = U(x, t), V(x, t)
    density = v * diff(u, t) + diff(u, x) * diff(v, x) + u**2 * v**2
    eu, ev = euler_operator(density, [U, V], (x, t))
    assert simplify(eu - (2 * u * v**2 - diff(v, t) - diff(v, x, 2))) == 0
    assert simplify(ev - (2 * u**2 * v + diff(u, t) - diff(u, x, 2))) == 0


def test_frechet_derivative_baumann():
    # (3.14): f = u_x u_xxx + u_x**2, D_f(w) = (u_xxx + 2 u_x) D_x w + u_x D_x**3 w
    W = Function("w")
    f = diff(u, x) * diff(u, x, 3) + diff(u, x) ** 2
    [[d]] = frechet_derivative([f], [U], [x], [W])
    expected = (diff(u, x, 3) + 2 * diff(u, x)) * diff(W(x), x) + diff(u, x) * diff(W(x), x, 3)
    assert simplify(d - expected) == 0


def test_adjoint_frechet_derivative():
    """Baumann (3.19): the adjoint of the Frechet derivative, and for a
    single equation the formal adjoint: D_x -> -D_x, D_x**2 -> D_x**2."""
    t = Symbol("t")
    V, W1, W2 = Function("v"), Function("w1"), Function("w2")
    u2, v2 = U(x, t), V(x, t)
    eqsys = [diff(v2, x) - u2, diff(v2, t) - diff(u2, x) / u2**2]
    adjoint = adjoint_frechet_derivative(eqsys, [U, V], [x, t], [W1, W2])
    w1, w2 = W1(x, t), W2(x, t)
    assert adjoint == [[-w1, diff(w1, x) / u2**2], [-diff(w2, x), -diff(w2, t)]]
    # u_xx + u u_x: D_f = D_x**2 + u D_x + u_x, adjoint D_x**2 - u D_x
    W = Function("w")
    [[a]] = adjoint_frechet_derivative([diff(u, x, 2) + u * diff(u, x)], [U], [x], [W])
    assert simplify(a - (diff(W(x), x, 2) - u * diff(W(x), x))) == 0


def test_euler_operator_deprecated_keywords():
    """depend and independ are the former names of dependent and independent."""
    t = symbols("t")
    u = Function("u")
    density = diff(u(t), t) ** 2
    expected = euler_operator(density, dependent=[u], independent=t)
    with pytest.warns(DeprecationWarning):
        assert euler_operator(density, depend=[u], independ=t) == expected
    with pytest.raises(TypeError):
        euler_operator(density, [u], t, dependant=[u])
