"""Tests for delierium.infinitesimals"""


from sympy.core.backend import Derivative, Symbol, Function

from delierium.helpers import make_infinitesimal, finish_substitution
from delierium.Infinitesimals import overdeterminedSystemODE, overdeterminedSystemODEs
import os
import sys
import pathlib

from collections import OrderedDict

sys.path.insert(0, pathlib.Path("tests/Arrigo").absolute())

def is_in(v, rlist):
    print(f"{v=}")
    print(f"{rlist=}")
    return any(v.simplify().expand() == _.simplify().expand() or v.simplify().expand() == - _.simplify().expand()
                   for _ in rlist)

D = Derivative

def test_example_2_17():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = Derivative(y, x, x)
    inf = overdeterminedSystemODE(ode, dependents, independents,
                                  infinitesimals=OrderedDict({x: X, y: Y}))
    expected = [Derivative(Y, x, x),
                2*Derivative(Y, x, y) - Derivative(X, x, x),
                Derivative(Y, y, y) - 2*Derivative(X, x, y),
                Derivative(X, y, y)]
    for i in inf:
        assert is_in(i, expected)


def test_example_2_18():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = D(y, x, x) + y * D(y, x) + x*y**4
    inf = overdeterminedSystemODE(ode, dependents, independents,
                                  infinitesimals=OrderedDict({x: X, y: Y}))

    expected = [D(Y, x, x) - (x*y**4)*(D(Y, y) - 2*D(X, x)) + y * D(Y, x) + X*y**4 + 4*Y*x*y**3, # (2.102a)
                2*D(Y, x, y) - D(X, x, x) + y*D(X, x) + 3*D(X, y)*x*(y**4) + Y, #(2.102b)
                D(Y, y, y) - 2*D(X, x, y) + 2*y*D(X, y), #(2.102c)
                D(X, y, y)] # (2.102d)

    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    assert len(inf) == len(expected)
    for i in inf:
        assert is_in(i, expected)


def test_example_2_19():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = D(y, x, x, ) + 3 * y * D(y, x) + y**3
    inf = overdeterminedSystemODE(ode, dependents, independents,
                                  infinitesimals=OrderedDict({x: X, y: Y}))

    expected = [D(Y, x, x) +  2*y**3*D(X, x) + 3*Y*y**2 + 3*y*D(Y, x)- y**3*D(Y, y), # (2.119a)
                2*D(Y, x, y) - D(X, x, x) + 3*y*D(X, x) + 3*y**3*D(X, y) + 3*Y, #(2.119b)
                D(Y, y, y) - 2*D(X, x, y) + 6*y*D(X, y), #(2.119c)
                D(X, y, y)] # (2.119d)

    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    assert len(inf) == len(expected)
    for i in expected:
        assert is_in(i, inf)

def test_example_2_20():
    x = Symbol('x')
    y = Function('y')(x)

    independents = [x]
    dependents = [y]

    X = make_infinitesimal(x, x, y)
    Y = make_infinitesimal(y, x, y)

    ode = D(y, x, x, x) + y * D(y, x, x)
    inf = overdeterminedSystemODE(ode, dependents, independents,
                                  infinitesimals=OrderedDict({x: X, y: Y}))

    expected = [3*D(Y, x, x, y) - D(X, x, 3) + y*(2*D(Y, x, y) - D(X, x, 2)), # (2.137a)
                3*(D(Y, x, y, y) - D(X, x, x, y)) + y*(D(Y, y, 2) - 2*D(X, x, y)), # (2.137b)
                D(Y, y, 3) - 3*D(X, x, y, y) - y*D(X, y, y), # (2.137c)
                D(X, y, 3), # (2.137d)
                3*(D(Y, x, y) - D(X, x, x)) + y*D(X, x) + Y, # (2.137e)
                3*(D(Y, y, 2) - 3*D(X, y, x)) + y*D(X, y), # (2.137f)
                6*D(X, y, y), # (2.137g)
                3*D(X, y), # (2.137h)
                D(Y, x, 3) + y*D(Y, x, 2)] # (2.137i)

    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    assert len(inf) == len(expected)
    for i in expected:
        assert is_in(i, inf)


def test_example_2_21():
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)

    independents = [t]
    dependents = [x, y]

    T = make_infinitesimal(t, t, x, y)
    X = make_infinitesimal(x, t, x, y)
    Y = make_infinitesimal(y, t, x, y)

    odes = [D(x, t) - 2*x*y,
            D(y, t) - x**2 - y**2]
    breakpoint()
    inf = overdeterminedSystemODEs(odes, dependents, independents,
                                   infinitesimals=OrderedDict({t: T, x: X, y: Y}))

    expected = [D(X, t) + (D(X, x) - D(T, t)) * 2 * x * y + (x**2 + y**2) * D(X, y) -
                (2*x*y)**2 * D(T, x) - 2*x*y*(x**2+y**2)*D(T, y) - 2*X*y+2*x*Y,
                D(Y, t) + 2*x*y*D(Y, x) + (x**2+y**2)*(D(Y, y) - D(T, t))
                - 2 * x * y * (x**2 + y*+2) * D(T, x) +
                (x**2+y**2)**2*D(T, y) - 2*x*X + 2*y*Y
                ]

    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    assert len(inf) == len(expected)
    for i in expected:
        assert is_in(i, inf)

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
    inf = overdeterminedSystemODE(ode, dependents, independents,
                                  infinitesimals=OrderedDict({x: X, t: T, u: U}))

    expected = [D(U, t) - D(U, x, x), # 3.34a
                -D(X, t) - 2*D(U, x, u) + D(X, x, x), #b
                -D(U, u, u) + 2*D(X, u, x), #c
                D(X, u, u), #d
                -D(T, t) + D(T, x, x) +2*D(X, x), #e
                2*D(X, u), + 2*D(T, x, u), #f
                D(T, u, u), #g
                2*D(T, x), #h
                2*D(T, u)] #i


    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    for i in inf:
        print(f"{i=}")

    print("IIIIIIIIIIIIIIIIIIIIII")
#    assert len(inf) == len(expected)
    for i in inf:
        print(f"{i=}")
        print(is_in(i, expected))

    print("AAAAAAAAAAAAAAAAAAAA")
    for i in expected:
        print(f"{i=}")
        print(is_in(i, inf))
    assert False


def test_example_2_22():
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)

    independents = [t]
    dependents = [x, y]

    T = make_infinitesimal(t, t, x, y)
    X = make_infinitesimal(x, t, x, y)
    Y = make_infinitesimal(y, t, x, y)

    odes = [D(x, t, t) - x/((x**2 + y**2)**2),
            D(y, t, t) - x/((x**2 + y**2)**2)]
    inf = overdeterminedSystemODEs(odes, dependents, independents,
                                   infinitesimals=OrderedDict({t: T, x: X, y: Y}))

    expected = [D(X, t) + (D(X, x) - D(T, t)) * 2 * x * y + (x**2 + y**2) * D(X, y) -
                (2*x*y)**2 * D(T, x) - 2*x*y*(x**2+y**2)*D(T, y) - 2*X*y+2*x*Y,
                D(Y, t) + 2*x*y*D(Y, x) + (x**2+y**2)*(D(Y, y) - D(T, t))
                - 2 * x * y * (x**2 + y*+2) * D(T, x) +
                (x**2+y**2)**2*D(T, y) - 2*x*X + 2*y*Y
                ]

    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    assert len(inf) == len(expected)
    for i in expected:
        assert is_in(i, inf)


def test_harry_dym_baumann_226():
    x = Symbol('x')
    t = Symbol('t')
    u = Function('u')(x, t)
    l = Symbol('lambda')
    independents = [x, t]
    dependents = [u]

    X = make_infinitesimal(x, x, t, u)
    T = make_infinitesimal(t, x, t, u)
    U = make_infinitesimal(u, x, t, u)

    ode = D(u, t) - l * D(u, x, x, x)*u**3
    inf = overdeterminedSystemODE(ode, dependents, independents,
                                  infinitesimals=OrderedDict({x: X, t: T, u: U}))

    expected = [D(U, t) - D(u, x, x), # 3.34a
                -D(X, t) - 2*D(U, x, u) + D(X, x, x), #b
                -D(U, u, u) + 2*D(X, u, x), #c
                D(X, u, u), #d
                -D(T, t) + D(T, x, x) +2*D(X, x), #e
                2*D(X, u), + 2*D(T, x, u), #f
                D(T, u, u), #g
                2*D(T, x), #h
                2*D(T, u)] #i


    expected = [_.xreplace(finish_substitution(_)).expand() for _ in expected]

    for i in inf:
        print(f"{i=}")

    print("IIIIIIIIIIIIIIIIIIIIII")
#    assert len(inf) == len(expected)
    for i in inf:
        print(f"{i=}")
        print(is_in(i, expected))

    print("AAAAAAAAAAAAAAAAAAAA")
    for i in expected:
        print(f"{i=}")
        print(is_in(i, inf))
    assert False
