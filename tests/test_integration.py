"""Tests for delierium.integration: integration of ODEs by their symmetries
(#43) and reduction of order by one generator (#14)."""

import random

import pytest
from sympy import (
    Derivative,
    Dummy,
    Eq,
    Function,
    Rational,
    Symbol,
    log,
    nsolve,
    symbols,
)

from delierium import OrderReduction, integrate_ode, reduce_order

x, y_ = symbols("x y")
y = Function("y")(x)


def residual(ode, relation, order, points=3):
    """The ODE holds on the family of curves relation = 0 at random points:
    y', y'', ... by implicit differentiation, a constant solved for."""
    Y = Dummy("Y")
    F = (relation.lhs - relation.rhs).subs(y, Y)
    first = -F.diff(x) / F.diff(Y)
    derivatives = [Y, first]
    for _ in range(2, order + 1):
        derivatives.append(derivatives[-1].diff(x) + derivatives[-1].diff(Y) * first)
    e = ode
    for k in range(order, 0, -1):
        e = e.subs(Derivative(y, (x, k)), derivatives[k])
    e = e.subs(y, Y)
    c = sorted((s for s in F.free_symbols if s.name[0] == "C"), key=str)[-1]
    rng = random.Random(0)
    checked = 0
    for _ in range(20):
        point = {
            s: Rational(rng.randint(11, 97), 37) for s in (e.free_symbols | F.free_symbols) - {c}
        }
        try:
            # an additive constant drops out of the derivatives
            if e.has(c):
                point[c] = nsolve(F.xreplace(point), c, 1)
            value = complex(e.xreplace(point).evalf(30))
        except (ValueError, ZeroDivisionError, TypeError, NotImplementedError):
            continue
        if value != value or abs(value) == float("inf"):
            continue
        assert abs(value) < 1e-8, (relation, point, value)
        checked += 1
        if checked == points:
            return True
    return False


def constants(relation):
    return {s for s in relation.free_symbols if s.name[0] == "C" and s.name[1:].isdigit()}


@pytest.mark.parametrize(
    "ode, generators, order",
    [
        # Hydon (5.10): translation and scaling of y
        (y.diff(x, 2) - y.diff(x) ** 2 / y, [(1, 0), (0, y_)], 2),
        # y'' = 0 by two of its eight symmetries
        (y.diff(x, 2), [(1, 0), (0, 1)], 2),
        # the harmonic oscillator: d/dx and the superposition with sin x
        (y.diff(x, 2) + y, [(1, 0), (0, y_)], 2),
        # Ermakov-Pinney: sl(2), a two-dimensional subalgebra suffices
        (y.diff(x, 2) - y**-3, [(1, 0), (2 * x, y_)], 2),
        # y''' = y''**2/y': three translations and scalings, solvable
        (y.diff(x, 3) - y.diff(x, 2) ** 2 / y.diff(x), [(1, 0), (0, 1), (x, 0)], 3),
        # a first order ODE with a scaling (homogeneous)
        (y.diff(x) - (x + y) / x, [(x, y_)], 1),
        # a Riccati equation with a scaling (Hydon, Example 2.10 type)
        (y.diff(x) - x * y**2 + 2 * y / x + 1 / x**3, [(x, -2 * y_)], 1),
    ],
)
def test_general_solution(ode, generators, order):
    solutions = integrate_ode(ode, y, x, generators)
    assert solutions
    for s in solutions:
        assert len(constants(s)) == order, s
        assert residual(ode, s, order), s


def test_orbits_are_the_solutions():
    """y' = y/x and the scaling x d/dx + y d/dy: eta = xi y', the solutions
    are its orbits, the invariant y/x is constant."""
    assert integrate_ode(y.diff(x) - y / x, y, x, [(x, y_)]) == [Eq(y, Symbol("C1") * x)]


def test_not_enough_symmetries():
    """Blasius: the translation and a scaling leave an Abel equation."""
    blasius = y.diff(x, 3) + y * y.diff(x, 2)
    with pytest.raises(NotImplementedError):
        integrate_ode(blasius, y, x, [(1, 0), (x, -y_)])


def test_default_generators():
    """Without generators: those of lie_symmetries."""
    ode = y.diff(x, 2) - y.diff(x) ** 2 / y
    for s in integrate_ode(ode, y, x):
        assert len(constants(s)) == 2
        assert residual(ode, s, 2)


def test_reduce_order():
    """y'' = y'**2/y + y'/x by y d/dy: w = y'/y, w' = w/r; the scaling of x
    commutes with y d/dy and goes down."""
    ode = y.diff(x, 2) - y.diff(x) ** 2 / y - y.diff(x) / x
    red = reduce_order(ode, (0, y_), y, x, [(x, 0)])
    assert isinstance(red, OrderReduction)
    r, w = Symbol("r"), Function("w")
    assert red.equation == Eq(Derivative(w(r), r), w(r) / r)
    assert (red.r, red.s) == (x, log(y_))
    assert red.generators == [(r, -Symbol("w"))]


def test_reduce_order_drops_others():
    """[d/dy, x**2 d/dx + x y d/dy] = x d/dy is not a multiple of d/dy: the
    generator does not go down."""
    ode = y.diff(x, 2)
    red = reduce_order(ode, (0, 1), y, x, [(x**2, x * y_)])
    assert red.generators == []


def test_reduce_order_fresh_names():
    r = Symbol("r")
    ode = y.diff(x, 2) - r * y
    red = reduce_order(ode, (0, y_), y, x)
    assert red.function.args[0] == Symbol("r1")


def test_not_an_ode():
    with pytest.raises(ValueError):
        integrate_ode(y - x, y, x, [(1, 0)])
