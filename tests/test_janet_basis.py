"""Tests for delierium.janet_basis"""

import pytest
from sympy import Function, Symbol, diff, simplify, symbols

from delierium.infinitesimals import is_janet_basis_of_ode, janet_basis_from_ode
from delierium.janet_basis import LHDP
from delierium.matrix_order import Context


@pytest.mark.parametrize(
    "variables", [("h",), ("h", "h"), ("h", "x"), ("x", "h", "h"), ("x", "x", "h")]
)
def test_lhdp_diff_is_leibniz(variables):
    # differentiating by several variables needs the full Leibniz rule for
    # coefficient * derivative, not only f' g + f g'
    x, h = symbols("x h")
    X, Y = Function("X")(h, x), Function("Y")(h, x)
    context = Context([X, Y], [h, x])
    e = diff(Y, x, 2) - 2 * h**2 * diff(X, x) + h**2 * diff(Y, h) - 2 * h * Y + x * h * X
    by = [{"x": x, "h": h}[v] for v in variables]
    assert simplify(LHDP(e, context).diff(*by).expression() - diff(e, *by)) == 0


def test_janet_basis_schwarz_example_5_2():
    # Schwarz, Algorithmic Lie Theory, Example 5.2, p. 200 (Kamke 6.159): the
    # integrability condition of Y_yy = 0 with the Y_xx equation needs
    # the second derivative by x of Y_yy; without it the Janet basis
    # described 6 instead of 2 symmetries
    x = Symbol("x")
    y = Function("y")(x)
    ode = 4 * diff(y, x, 2) * y - 3 * diff(y, x) ** 2 - 12 * y**3
    ys = Symbol("y")
    X, Y = Function("X")(ys, x), Function("Y")(ys, x)
    B = [diff(X, x) + Y / (2 * ys), diff(X, ys), diff(Y, x), diff(Y, ys) - Y / ys]
    assert is_janet_basis_of_ode(B, ode, y, x)


def leading_orders(B, variables):
    orders = []
    for b in B:
        d = b.p[0].derivative
        counts = dict(d.variable_count) if d.is_Derivative else {}
        f = d.expr if d.is_Derivative else d
        orders.append((f.func, tuple(counts.get(v, 0) for v in variables)))
    return orders


@pytest.mark.parametrize(
    ("name", "ode", "dimension"),
    [
        # Kamke 6.1, Schwarz Appendix E: {d_x, x d_x - 2y d_y}
        ("y'' = y**2", lambda y, x: diff(y, x, 2) - y**2, 2),
        # Kamke 6.3, Painleve I: no point symmetries
        ("Painleve I", lambda y, x: diff(y, x, 2) - 6 * y**2 - x, 0),
        # Chazy: sl(2); with the wrong Leibniz rule the basis described only 1
        ("Chazy", lambda y, x: diff(y, x, 3) - 2 * y * diff(y, x, 2) + 3 * diff(y, x) ** 2, 3),
    ],
)
def test_janet_basis_dimension(name, ode, dimension):
    x = Symbol("x")
    y = Function("y")(x)
    B = janet_basis_from_ode(ode(y, x), y, x)
    variables = [x, y]
    leaders = leading_orders(B, variables)
    # count the parametric derivatives: those of X, Y that are no derivative
    # of a leading derivative; all have order <= 3 here
    count = 0
    for f in {f for f, _ in leaders}:
        for i in range(5):
            for j in range(5 - i):
                if not any(g == f and i >= a and j >= b for g, (a, b) in leaders):
                    count += 1
    assert count == dimension, name
