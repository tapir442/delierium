"""Tests for delierium.infinitesimals"""

import pathlib
import sys
from collections import OrderedDict

from sympy import Lambda, Matrix, cancel, simplify
from sympy.core.backend import Derivative, Function, Symbol
from sympy.core.function import AppliedUndef

from delierium.helpers import finish_substitution, make_infinitesimal
from delierium.Infinitesimals import (
    canonical_derivatives,
    overdetermined_system_ode,
    overdetermined_system_odes,
    overdetermined_system_pde,
)

sys.path.insert(0, pathlib.Path("tests/Arrigo").absolute())


def is_in(v, rlist):
    return any(
        v.simplify().expand() == _.simplify().expand()
        or v.simplify().expand() == -_.simplify().expand()
        for _ in rlist
    )


D = Derivative


def equivalent(a, b, dependents):
    """a and b differ only by a nonzero factor free of the infinitesimals
    (a number, or a power of the dependent variable)."""
    ratio = cancel(a / b)
    return ratio != 0 and not ratio.has(Derivative) and ratio.atoms(AppliedUndef) <= set(dependents)


def assert_same_system(computed, expected, dependents):
    expected = [canonical_derivatives(finish_substitution(e), dependents) for e in expected]
    assert all(any(equivalent(c, e, dependents) for e in expected) for c in computed)
    assert all(any(equivalent(c, e, dependents) for c in computed) for e in expected)


def assert_same_span(computed, expected, dependents):
    """computed and expected generate the same linear system: both are
    linear in the infinitesimals and their derivatives, with coefficients
    in the dependent variables, and have the same span over those."""
    expected = [canonical_derivatives(finish_substitution(e), dependents) for e in expected]
    unknowns = sorted(
        {a for e in computed + expected for a in e.atoms(Derivative, AppliedUndef)}
        - set(dependents),
        key=str,
    )

    def matrix(system):
        rows = [[e.expand().coeff(a) for a in unknowns] for e in system]
        for e, row in zip(system, rows, strict=True):
            assert (e - sum(c * a for c, a in zip(row, unknowns, strict=True))).expand() == 0
        return Matrix(rows)

    rank = matrix(expected).rank(simplify=True)
    assert matrix(computed).rank(simplify=True) == rank
    assert matrix(computed + expected).rank(simplify=True) == rank


def test_example_2_17():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = Derivative(y, x, x)
    inf = overdetermined_system_ode(
        ode, dependents, independents, infinitesimals=OrderedDict({x: X, y: Y})
    )
    expected = [
        Derivative(Y, x, x),
        2 * Derivative(Y, x, y) - Derivative(X, x, x),
        Derivative(Y, y, y) - 2 * Derivative(X, x, y),
        -Derivative(X, y, y),
    ]
    expected = [finish_substitution(_) for _ in expected]
    assert_same_system(inf, expected, dependents)


def test_example_2_18():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = D(y, x, x) + y * D(y, x) + x * y**4
    inf = overdetermined_system_ode(
        ode, dependents, independents, infinitesimals=OrderedDict({x: X, y: Y})
    )

    expected = [
        D(Y, x, x)
        - (x * y**4) * (D(Y, y) - 2 * D(X, x))
        + y * D(Y, x)
        + X * y**4
        + 4 * Y * x * y**3,  # (2.102a)
        2 * D(Y, x, y) - D(X, x, x) + y * D(X, x) + 3 * D(X, y) * x * (y**4) + Y,  # (2.102b)
        D(Y, y, y) - 2 * D(X, x, y) + 2 * y * D(X, y),  # (2.102c)
        -D(X, y, y),
    ]  # (2.102d)

    expected = [finish_substitution(_) for _ in expected]
    inf = [finish_substitution(_) for _ in inf]
    assert_same_system(inf, expected, dependents)


def test_example_2_19():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = (
        D(
            y,
            x,
            x,
        )
        + 3 * y * D(y, x)
        + y**3
    )
    inf = overdetermined_system_ode(
        ode, dependents, independents, infinitesimals=OrderedDict({x: X, y: Y})
    )

    expected = [
        D(Y, x, x)
        + 2 * y**3 * D(X, x)
        + 3 * Y * y**2
        + 3 * y * D(Y, x)
        - y**3 * D(Y, y),  # (2.119a)
        2 * D(Y, x, y) - D(X, x, x) + 3 * y * D(X, x) + 3 * y**3 * D(X, y) + 3 * Y,  # (2.119b)
        D(Y, y, y) - 2 * D(X, x, y) + 6 * y * D(X, y),  # (2.119c)
        D(X, y, y),
    ]  # (2.119d)

    expected = [finish_substitution(_).expand() for _ in expected]
    assert_same_system(inf, expected, dependents)


def test_example_2_20():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = D(y, x, x, x) + y * D(y, x, x)
    inf = overdetermined_system_ode(
        ode, dependents, independents, infinitesimals=OrderedDict({x: X, y: Y})
    )

    expected = [
        3 * D(Y, x, x, y) - D(X, x, 3) + y * (2 * D(Y, x, y) - D(X, x, 2)),  # (2.137a)
        3 * (D(Y, x, y, y) - D(X, x, x, y)) + y * (D(Y, y, 2) - 2 * D(X, x, y)),  # (2.137b)
        D(Y, y, 3) - 3 * D(X, x, y, y) - y * D(X, y, y),  # (2.137c)
        D(X, y, 3),  # (2.137d)
        3 * (D(Y, x, y) - D(X, x, x)) + y * D(X, x) + Y,  # (2.137e)
        3 * (D(Y, y, 2) - 3 * D(X, y, x)) + y * D(X, y),  # (2.137f)
        6 * D(X, y, y),  # (2.137g)
        3 * D(X, y),  # (2.137h)
        D(Y, x, 3) + y * D(Y, x, 2),
    ]  # (2.137i)

    expected = [finish_substitution(_).expand() for _ in expected]
    assert_same_system(inf, expected, dependents)


def _test_example_2_21():
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)

    independents = [t]
    dependents = [x, y]

    T = make_infinitesimal(t, t, x, y)
    X = make_infinitesimal(x, t, x, y)
    Y = make_infinitesimal(y, t, x, y)

    odes = [D(x, t) - 2 * x * y, D(y, t) - x**2 - y**2]
    inf = overdetermined_system_odes(
        odes, dependents, independents, infinitesimals=OrderedDict({t: T, x: X, y: Y})
    )

    expected = [
        D(X, t)
        + (D(X, x) - D(T, t)) * 2 * x * y
        + (x**2 + y**2) * D(X, y)
        - (2 * x * y) ** 2 * D(T, x)
        - 2 * x * y * (x**2 + y**2) * D(T, y)
        - 2 * X * y
        - 2 * x * Y,  # 2.155a
        D(Y, t)
        + 2 * x * y * D(Y, x)
        + (x**2 + y**2) * (D(Y, y) - D(T, t))
        - 2 * x * y * (x**2 + y**2) * D(T, x)
        + (x**2 + y**2) ** 2 * D(T, y)
        - 2 * x * X
        - 2 * y * Y,  # 2.155b
    ]

    expected = [finish_substitution(_).expand() for _ in expected]
    assert_same_system(inf, expected, dependents)


def test_heat_equation():
    x = Symbol('x')
    t = Symbol('t')
    u = Function('u')(x, t)

    independents = [x, t]
    dependents = [u]

    X = make_infinitesimal(x, x, t, u)
    T = make_infinitesimal(t, x, t, u)
    U = make_infinitesimal(u, x, t, u)

    ode = D(u, t) - D(u, x, x)
    inf = overdetermined_system_pde(
        ode, dependents, independents, infinitesimals=OrderedDict({x: X, t: T, u: U})
    )

    expected = [
        D(U, t) - D(U, x, x),  # 3.34a
        -D(X, t) - 2 * D(U, x, u) + D(X, x, x),  # b
        -D(U, u, u) + 2 * D(X, u, x),  # c
        D(X, u, u),  # d
        -D(T, t) + D(T, x, x) + 2 * D(X, x),  # e
        2 * D(X, u) + 2 * D(T, x, u),  # f
        D(T, u, u),  # g
        2 * D(T, x),  # h
        2 * D(T, u),
    ]  # i

    expected = [finish_substitution(_) for _ in expected]
    assert_same_system(inf, expected, dependents)


def _test_example_2_22():
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)

    independents = [t]
    dependents = [x, y]

    T = make_infinitesimal(t, t, x, y)
    X = make_infinitesimal(x, t, x, y)
    Y = make_infinitesimal(y, t, x, y)

    odes = [D(x, t, t) - x / ((x**2 + y**2) ** 2), D(y, t, t) - x / ((x**2 + y**2) ** 2)]
    inf = overdetermined_system_odes(
        odes, dependents, independents, infinitesimals=OrderedDict({t: T, x: X, y: Y})
    )

    expected = [
        D(X, t)
        + (D(X, x) - D(T, t)) * 2 * x * y
        + (x**2 + y**2) * D(X, y)
        - (2 * x * y) ** 2 * D(T, x)
        - 2 * x * y * (x**2 + y**2) * D(T, y)
        - 2 * X * y
        + 2 * x * Y,
        D(Y, t)
        + 2 * x * y * D(Y, x)
        + (x**2 + y**2) * (D(Y, y) - D(T, t))
        - 2 * x * y * (x**2 + y * +2) * D(T, x)
        + (x**2 + y**2) ** 2 * D(T, y)
        - 2 * x * X
        + 2 * y * Y,
    ]

    expected = [finish_substitution(_).expand() for _ in expected]
    assert_same_system(inf, expected, dependents)


def test_harry_dym_baumann_226():
    # u_t = u^3 u_xxx
    x = Symbol('x')
    t = Symbol('t')
    u = Function('u')(x, t)
    independents = [x, t]
    dependents = [u]

    X = make_infinitesimal(x, x, t, u)
    T = make_infinitesimal(t, x, t, u)
    U = make_infinitesimal(u, x, t, u)

    ode = D(u, t) - D(u, x, x, x) * u**3
    inf = overdetermined_system_pde(
        ode, dependents, independents, infinitesimals=OrderedDict({x: X, t: T, u: U})
    )

    expected = [
        D(T, x),
        D(T, x, x),
        D(T, u),
        D(T, u, u),
        D(T, u, u, u),
        D(T, u, x),
        D(T, u, u, x),
        D(X, u),
        D(X, u, u),
        D(X, u, u, u),
        D(U, t) - u**3 * D(U, x, x, x),
        D(U, u, u) - 3 * D(X, u, x),
        D(U, u, u, u) - 3 * D(X, u, u, x),
        D(U, u, x) - D(X, x, x),
        D(U, u, u, x) - D(X, u, x, x),
        u**3 * D(T, u, x, x) + D(X, u),
        u**3 * D(X, x, x, x) - 3 * u**3 * D(U, u, x, x) - D(X, t),
        u**4 * D(T, x, x, x) - u * D(T, t) + 3 * u * D(X, x) - 3 * U,
    ]
    # symlie returns a different generating set of the same system
    assert_same_span(inf, expected, dependents)

    # general solution: the five-dimensional symmetry algebra
    # d_x, d_t, x d_x + u d_u, x^2 d_x + 2 x u d_u, 3 t d_t - u d_u
    c1, c2, c3, c4, c5 = Symbol('c1'), Symbol('c2'), Symbol('c3'), Symbol('c4'), Symbol('c5')
    us = Symbol('u')
    solution = {
        X.func: Lambda((x, t, us), c1 + c2 * x + c3 * x**2),
        T.func: Lambda((x, t, us), c4 + 3 * c5 * t),
        U.func: Lambda((x, t, us), us * (c2 + 2 * c3 * x - c5)),
    }
    for e in inf:
        assert simplify(e.xreplace({u: us}).subs(solution).doit()) == 0
