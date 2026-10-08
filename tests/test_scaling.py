"""Scaling symmetries by linear algebra on the exponents (#48)."""

from sympy import Abs, Function, exp, sin, symbols

from delierium import scaling_symmetries, verify_symmetries

x, t, n, a = symbols("x t n a")
u = Function("u")(x, t)


def test_pdes():
    # the heat equation: x d/dx + 2 t d/dt and u d/du (linear)
    U = symbols("u")
    assert scaling_symmetries(u.diff(t) - u.diff(x, 2), u, [x, t]) == [(x, 2 * t, 0), (0, 0, U)]
    # exp(u) forbids scaling u, and then x and t
    assert scaling_symmetries(u.diff(t) - u.diff(x, 2) - exp(u), u, [x, t]) == []
    # an arbitrary k(u): u is not scaled
    k = Function("k")
    assert scaling_symmetries(u.diff(t) - (k(u) * u.diff(x)).diff(x), u, [x, t]) == [(x, 2 * t, 0)]
    # symbolic exponents: generic values
    pde = u.diff(t) - (u**n * u.diff(x)).diff(x) + a * u**3
    assert scaling_symmetries(pde, u, [x, t]) == [((n - 2) * x, -4 * t, 2 * U)]


def test_odes_and_functions():
    y = Function("y")(x)
    Y = symbols("y")
    # Emden-Fowler y'' = x**a y**n: one scaling for generic a, n
    ode = y.diff(x, 2) - x**a * y**n
    [scaling] = scaling_symmetries(ode, y, x)
    assert all(verify_symmetries(ode, y, x, [scaling]))
    # sin(x) forbids scaling x; Abs scales like its argument
    assert scaling_symmetries(y.diff(x, 2) - sin(x) * y, y, x) == [(0, Y)]
    assert scaling_symmetries(y.diff(x) - Abs(y) / x, y, x) == [(x, 0), (0, Y)]
    # a system: the harmonic oscillator, p and q scaled together
    p, q = Function("p")(t), Function("q")(t)
    P, Q = symbols("p q")
    system = [p.diff(t) + q, q.diff(t) - p]
    assert scaling_symmetries(system, [p, q], t) == [(0, P, Q)]
