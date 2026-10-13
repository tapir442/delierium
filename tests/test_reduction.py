"""Tests for delierium.reduction: similarity reduction of PDEs by a given
generator (#15)"""

import pytest
from sympy import Derivative, Function, exp, simplify, symbols

from delierium import similarity_reduction

x, y, t, c, u_, v_ = symbols("x y t c u v")
u = Function("u")(x, t)
v = Function("v")(x, t)


def proportional(a, b):
    """a = k b for a constant k != 0."""
    k = simplify(a / b)
    return k != 0 and not k.free_symbols and not k.has(Derivative, Function)


def F(*args):  # noqa: N802
    return Function("F")(*args)  # pylint: disable=not-callable


z, z1, z2 = symbols("zeta zeta1 zeta2")


@pytest.mark.parametrize(
    "equation, generator, independent, zeta, ansatz, expected",
    [
        # Olver 3.1: the heat equation by its scaling
        (
            u.diff(t) - u.diff(x, 2),
            (x, 2 * t, 0),
            [x, t],
            [t / x**2],
            F(t / x**2),
            4 * z**2 * F(z).diff(z, 2) + 6 * z * F(z).diff(z) - F(z).diff(z),
        ),
        # Galilean boost: the source solution up to the factor F(t)
        (
            u.diff(t) - u.diff(x, 2),
            (2 * t, 0, -x * u_),
            [x, t],
            [t],
            F(t) * exp(-(x**2) / (4 * t)),
            2 * z * F(z).diff(z) + F(z),
        ),
        (u.diff(t) - u.diff(x, 2), (1, 0, u_), [x, t], [t], F(t) * exp(x), F(z).diff(z) - F(z)),
        # KdV: travelling waves
        (
            u.diff(t) + u * u.diff(x) + u.diff(x, 3),
            (c, 1, 0),
            [x, t],
            [x - c * t],
            F(x - c * t),
            F(z).diff(z, 3) + (F(z) - c) * F(z).diff(z),
        ),
        # Burgers: scaling, u = F/x
        (
            u.diff(t) + u * u.diff(x) - u.diff(x, 2),
            (x, 2 * t, -u_),
            [x, t],
            [t / x**2],
            F(t / x**2) / x,
            4 * z**2 * F(z).diff(z, 2)
            + 2 * z * F(z) * F(z).diff(z)
            + 10 * z * F(z).diff(z)
            + F(z) ** 2
            + 2 * F(z)
            - F(z).diff(z),
        ),
    ],
)
def test_reduction_to_an_ode(equation, generator, independent, zeta, ansatz, expected):
    r = similarity_reduction(equation, generator, u, independent)
    assert r.similarity_variables == zeta
    assert r.variables == [z]
    assert r.functions == [F(z)]
    assert len(r.ansatz) == 1 and r.ansatz[0].lhs == u
    assert simplify(r.ansatz[0].rhs - ansatz) == 0
    assert len(r.equations) == 1 and proportional(r.equations[0], expected)


def test_laplace_rotation():
    """Radial solutions: zeta = r**2."""
    w = Function("u")(x, y)
    r = similarity_reduction(w.diff(x, 2) + w.diff(y, 2), (-y, x, 0), w, [x, y])
    assert r.similarity_variables == [x**2 + y**2]
    assert proportional(r.equations[0], z * F(z).diff(z, 2) + F(z).diff(z))


def test_three_variables():
    """The two-dimensional heat equation by rotations and by the scaling:
    PDEs in two variables."""
    w = Function("u")(x, y, t)
    heat = w.diff(t) - w.diff(x, 2) - w.diff(y, 2)
    r = similarity_reduction(heat, (-y, x, 0, 0), w, [x, y, t])
    assert r.similarity_variables == [x**2 + y**2, t]
    G = F(z1, z2)
    assert proportional(r.equations[0], 4 * z1 * G.diff(z1, 2) + 4 * G.diff(z1) - G.diff(z2))
    r = similarity_reduction(heat, (x, y, 2 * t, 0), w, [x, y, t])
    assert r.similarity_variables == [y / x, t / x**2]
    assert r.equations[0].has(G.diff(z1, z2))
    assert not r.equations[0].has(x, y, t)


def test_systems():
    """A system: one new function per dependent variable."""
    F1, F2 = (Function(f)(z) for f in ("F1", "F2"))  # pylint: disable=not-callable
    r = similarity_reduction(
        [u.diff(t) - v.diff(x), v.diff(t) - u.diff(x)], (x, t, 0, 0), [u, v], [x, t]
    )
    assert r.functions == [F1, F2]
    assert [a.rhs for a in r.ansatz] == [F1.subs(z, t / x), F2.subs(z, t / x)]
    assert proportional(r.equations[0], F1.diff(z) + z * F2.diff(z))
    assert proportional(r.equations[1], F2.diff(z) + z * F1.diff(z))


def test_names_do_not_clash():
    """zeta and F as independent variables: the new names get underscores."""
    zeta, Fs = symbols("zeta F")
    w = Function("u")(zeta, Fs)
    r = similarity_reduction(w.diff(Fs) - w.diff(zeta, 2), (1, 0, 0), w, [zeta, Fs])
    assert [str(s) for s in r.variables] == ["zeta_"]
    assert r.functions[0].func.__name__ == "F_"


def test_arbitrary_function_named_f():
    """u_t = u_xx + F(u): the new function is F_, not the F of the equation."""
    Fu = Function("F")(u)  # pylint: disable=not-callable
    r = similarity_reduction(u.diff(t) - u.diff(x, 2) - Fu, (1, 0, 0), u, [x, t])
    G = Function("F_")(z)  # pylint: disable=not-callable
    assert r.functions == [G]
    assert proportional(r.equations[0], G.diff(z) - Function("F")(G))  # pylint: disable=not-callable


def test_errors():
    with pytest.raises(ValueError, match="two or more"):
        similarity_reduction(Function("y")(x).diff(x), (1, 0), Function("y")(x), [x])
    # X acts on u only: no invariant contains u
    with pytest.raises(NotImplementedError, match="similarity variables"):
        similarity_reduction(u.diff(t) - u.diff(x, 2), (0, 0, 1), u, [x, t])
    # not invariant: u_t = u_xx + x u by d/dx, F' = x F
    with pytest.raises(NotImplementedError, match="do not reduce"):
        similarity_reduction(u.diff(t) - u.diff(x, 2) - x * u, (1, 0, 0), u, [x, t])
