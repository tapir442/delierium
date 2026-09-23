"""Tests for delierium.Infinitesimals.prolongation.

The expected results are the extended infinitesimals and prolonged
equations from D. J. Arrigo, "Symmetry Analysis of Differential
Equations: An Introduction" (Chapter 2 for ODEs, Chapter 3 for PDEs).
Arrigo's xi, eta (ODE) and xi, tau, eta (PDE) are X, Y and X, T, U here.

prolongation returns derivatives of the infinitesimals taken w.r.t.
y(x) and u(x, t). To compare them with the book, both sides are moved to
jet space: every derivative of a dependent variable becomes a plain
symbol (y_x, u_xt, ...) and the dependent variable itself becomes a
symbol, so that e.g. X_y is an ordinary partial derivative of X(x, y).
"""

from sympy import Function as PlainFunction
from sympy import Symbol as PlainSymbol
from sympy import expand
from sympy.core.backend import Derivative, Function, Symbol

from delierium.helpers import make_infinitesimal
from delierium.Infinitesimals import prolongation

D = Derivative


def prolong(eq, dep, indep):
    """Prolong eq and move the result to jet space: each derivative of
    dep becomes a symbol named after its variables in the order of indep
    (u_xt, y_xx, ...), then dep itself becomes a symbol.

    xreplace keeps the variable order of mixed partials (X_yx vs X_xy),
    so doit() rebuilds them in sympy's canonical order.
    """
    infinitesimals = {v: make_infinitesimal(v, *indep, dep) for v in [*indep, dep]}
    r = prolongation(eq, infinitesimals, [dep], indep)
    jet = {}
    for d in r.atoms(Derivative):
        if d.expr == dep:
            counts = dict(d.variable_count)
            suffix = "".join(str(v) * counts.get(v, 0) for v in indep)
            jet[d] = PlainSymbol(f"{dep.name}_{suffix}")
    return r.xreplace(jet).xreplace({dep: PlainSymbol(dep.name)}).doit()


def assert_equal(actual, expected):
    assert expand(actual - expected) == 0


# ---------------------------------------------------------------------------
# ODEs, y = y(x): Arrigo Chapter 2
# ---------------------------------------------------------------------------

x_, y_ = PlainSymbol('x'), PlainSymbol('y')
X_, Y_ = PlainFunction('X')(x_, y_), PlainFunction('Y')(x_, y_)
y1, y2, y3 = PlainSymbol('y_x'), PlainSymbol('y_xx'), PlainSymbol('y_xxx')


def d(f, *vs):
    return f.diff(*vs)


def ode_setup():
    x = Symbol('x')
    y = Function('y')(x)
    return x, y


def test_first_extension():
    # eta^(1) = eta_x + (eta_y - xi_x) y' - xi_y y'^2
    x, y = ode_setup()
    r = prolong(D(y, x), y, [x])
    expected = d(Y_, x_) + (d(Y_, y_) - d(X_, x_)) * y1 - d(X_, y_) * y1**2
    assert_equal(r, expected)


def eta2():
    # eta^(2) = eta_xx + (2 eta_xy - xi_xx) y' + (eta_yy - 2 xi_xy) y'^2
    #           - xi_yy y'^3 + (eta_y - 2 xi_x - 3 xi_y y') y''
    return (
        d(Y_, x_, x_)
        + (2 * d(Y_, x_, y_) - d(X_, x_, x_)) * y1
        + (d(Y_, y_, y_) - 2 * d(X_, x_, y_)) * y1**2
        - d(X_, y_, y_) * y1**3
        + (d(Y_, y_) - 2 * d(X_, x_) - 3 * d(X_, y_) * y1) * y2
    )


def test_second_extension():
    x, y = ode_setup()
    r = prolong(D(y, x, x), y, [x])
    assert_equal(r, eta2())


def test_third_extension():
    # eta^(3) = eta_xxx + (3 eta_xxy - xi_xxx) y'
    #           + 3 (eta_xyy - xi_xxy) y'^2 + (eta_yyy - 3 xi_xyy) y'^3
    #           - xi_yyy y'^4
    #           + 3 (eta_xy - xi_xx + (eta_yy - 3 xi_xy) y' - 2 xi_yy y'^2) y''
    #           - 3 xi_y y''^2 + (eta_y - 3 xi_x - 4 xi_y y') y'''
    # Arrigo, eq 2.135
    x, y = ode_setup()
    r = prolong(D(y, x, x, x), y, [x])
    expected = (
        d(Y_, x_, x_, x_)
        + (3 * d(Y_, x_, x_, y_) - d(X_, x_, x_, x_)) * y1
        + 3 * (d(Y_, x_, y_, y_) - d(X_, x_, x_, y_)) * y1**2
        + (d(Y_, y_, y_, y_) - 3 * d(X_, x_, y_, y_)) * y1**3
        - d(X_, y_, y_, y_) * y1**4
        + 3
        * (
            d(Y_, x_, y_)
            - d(X_, x_, x_)
            + (d(Y_, y_, y_) - 3 * d(X_, x_, y_)) * y1
            - 2 * d(X_, y_, y_) * y1**2
        )
        * y2
        - 3 * d(X_, y_) * y2**2
        + (d(Y_, y_) - 3 * d(X_, x_) - 4 * d(X_, y_) * y1) * y3
    )
    assert_equal(r, expected)


def test_example_2_18():
    # y'' + y y' + x y^4 = 0:
    # Gamma^(2) = xi y^4 + eta (y' + 4 x y^3) + eta^(1) y + eta^(2)
    x, y = ode_setup()
    r = prolong(D(y, x, x) + y * D(y, x) + x * y**4, y, [x])
    eta1 = d(Y_, x_) + (d(Y_, y_) - d(X_, x_)) * y1 - d(X_, y_) * y1**2
    expected = X_ * y_**4 + Y_ * (y1 + 4 * x_ * y_**3) + eta1 * y_ + eta2()
    assert_equal(r, expected)


# ---------------------------------------------------------------------------
# PDEs, u = u(x, t): Arrigo Chapter 3
# ---------------------------------------------------------------------------

t_, u_ = PlainSymbol('t'), PlainSymbol('u')
Xp, Tp, Up = (PlainFunction(n)(x_, t_, u_) for n in 'XTU')
ux, ut = PlainSymbol('u_x'), PlainSymbol('u_t')
uxx, uxt = PlainSymbol('u_xx'), PlainSymbol('u_xt')


def pde_setup():
    x, t = Symbol('x'), Symbol('t')
    u = Function('u')(x, t)
    return x, t, u


def eta_t():
    # eta^t = eta_t - xi_t u_x + (eta_u - tau_t) u_t - xi_u u_x u_t
    #         - tau_u u_t^2
    return (
        d(Up, t_)
        - d(Xp, t_) * ux
        + (d(Up, u_) - d(Tp, t_)) * ut
        - d(Xp, u_) * ux * ut
        - d(Tp, u_) * ut**2
    )


def eta_xx():
    # eta^xx = eta_xx + (2 eta_xu - xi_xx) u_x - tau_xx u_t
    #          + (eta_uu - 2 xi_xu) u_x^2 - 2 tau_xu u_x u_t
    #          - xi_uu u_x^3 - tau_uu u_x^2 u_t
    #          + (eta_u - 2 xi_x - 3 xi_u u_x - tau_u u_t) u_xx
    #          - 2 (tau_x + tau_u u_x) u_xt
    return (
        d(Up, x_, x_)
        + (2 * d(Up, x_, u_) - d(Xp, x_, x_)) * ux
        - d(Tp, x_, x_) * ut
        + (d(Up, u_, u_) - 2 * d(Xp, x_, u_)) * ux**2
        - 2 * d(Tp, x_, u_) * ux * ut
        - d(Xp, u_, u_) * ux**3
        - d(Tp, u_, u_) * ux**2 * ut
        + (d(Up, u_) - 2 * d(Xp, x_) - 3 * d(Xp, u_) * ux - d(Tp, u_) * ut) * uxx
        - 2 * (d(Tp, x_) + d(Tp, u_) * ux) * uxt
    )


def test_pde_first_extension_x():
    # eta^x = eta_x + (eta_u - xi_x) u_x - tau_x u_t - xi_u u_x^2
    #         - tau_u u_x u_t
    x, t, u = pde_setup()
    r = prolong(D(u, x), u, [x, t])
    expected = (
        d(Up, x_)
        + (d(Up, u_) - d(Xp, x_)) * ux
        - d(Tp, x_) * ut
        - d(Xp, u_) * ux**2
        - d(Tp, u_) * ux * ut
    )
    assert_equal(r, expected)


def test_pde_first_extension_t():
    x, t, u = pde_setup()
    r = prolong(D(u, t), u, [x, t])
    assert_equal(r, eta_t())


def test_pde_second_extension_xx():
    x, t, u = pde_setup()
    r = prolong(D(u, x, x), u, [x, t])
    assert_equal(r, eta_xx())


def test_heat_equation():
    # Section 3.2.1, u_t = u_xx: Gamma^(2) (u_t - u_xx) = eta^t - eta^xx
    x, t, u = pde_setup()
    r = prolong(D(u, t) - D(u, x, x), u, [x, t])
    assert_equal(r, eta_t() - eta_xx())
