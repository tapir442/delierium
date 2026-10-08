"""Tests for delierium.infinitesimals"""

import pathlib
import sys
from collections import OrderedDict
from itertools import product

import pytest
from sympy import (
    Abs,
    Derivative,
    Float,
    Function,
    Lambda,
    Rational,
    Symbol,
    cancel,
    im,
    oo,
    re,
    sign,
    simplify,
    sin,
)
from sympy.core.function import AppliedUndef

from delierium.helpers import finish_substitution, make_infinitesimal
from delierium.infinitesimals import (
    _linear_system_odes,
    canonical_derivatives,
    create_infinitesimals,
    is_janet_basis_of_odes,
    janet_basis_from_odes,
    overdetermined_system_ode,
    overdetermined_system_odes,
    overdetermined_system_pde,
    verify_symmetries,
    verify_symmetry,
)
from delierium.janet_basis import JanetBasis

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


def test_example_2_21():
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
        # the notebook had +(x**2 + y**2)**2 * T_y; the term comes from
        # -y' * D_t(T) with y' = x**2 + y**2, so the sign is minus
        - (x**2 + y**2) ** 2 * D(T, y)
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


def test_free_particle_2d():
    # x'' = 0, y'' = 0: the point symmetries are the 15-dimensional sl(4)
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)
    dependents = [x, y]

    T = make_infinitesimal(t, t, x, y)
    X = make_infinitesimal(x, t, x, y)
    Y = make_infinitesimal(y, t, x, y)

    inf = overdetermined_system_odes(
        [D(x, t, t), D(y, t, t)], dependents, [t], infinitesimals=OrderedDict({t: T, x: X, y: Y})
    )

    ts, xs, ys = Symbol('t'), Symbol('x'), Symbol('y')

    def is_symmetry(tau, xi, eta):
        solution = {f.func: Lambda((ts, xs, ys), g) for f, g in [(T, tau), (X, xi), (Y, eta)]}
        return all(simplify(e.xreplace({x: xs, y: ys}).subs(solution).doit()) == 0 for e in inf)

    generators = [
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
        (0, ts, 0),
        (0, 0, ts),
        (0, xs, 0),
        (0, ys, 0),
        (0, 0, xs),
        (0, 0, ys),
        (ts, 0, 0),
        (xs, 0, 0),
        (ys, 0, 0),
        (ts**2, ts * xs, ts * ys),
        (ts * xs, xs**2, xs * ys),
        (ts * ys, xs * ys, ys**2),
    ]
    assert all(is_symmetry(*g) for g in generators)
    assert not is_symmetry(0, 0, xs**2)
    assert not is_symmetry(ts**2, 0, 0)


def test_example_2_22():
    # Arrigo, Example 2.22, p. 70: x'' = x/r**4, y'' = y/r**4 with r**2 = x**2 + y**2.
    # The book gives the general solution (2.186) of the determining
    # equations, not the equations themselves:
    # T = k2 t**2 + 2 k1 t + k0, X = (k2 t + k1) x + k3 y, Y = -k3 x + (k2 t + k1) y
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)
    r4 = (x**2 + y**2) ** 2
    B = janet_basis_from_odes([D(x, t, t) - x / r4, D(y, t, t) - y / r4], [x, y], [t])
    assert parametric_dimension(B, [t, x, y]) == 4
    ts, xs, ys = Symbol('t'), Symbol('x'), Symbol('y')
    for g in [
        (1, 0, 0),  # k0
        (2 * ts, xs, ys),  # k1
        (ts**2, ts * xs, ts * ys),  # k2
        (0, ys, -xs),  # k3
    ]:
        assert satisfies_janet_basis(B, g, t, x, y)
    # the scaling of Kepler's third law is no symmetry for this force law
    assert not satisfies_janet_basis(B, (3 * ts, 2 * xs, 2 * ys), t, x, y)


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
    assert_same_system(inf, expected, dependents)

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


def parametric_dimension(B, variables, bound=6):
    """Number of parametric derivatives of a Janet basis, i.e. the dimension
    of its solution space; None if there are parametric derivatives of order
    bound (then the space is taken as infinite-dimensional)."""

    def leader(b):
        d = b.terms[0].derivative
        if not isinstance(d, Derivative):
            return d.func, (0,) * len(variables)
        counts = dict(d.variable_count)
        return d.expr.func, tuple(counts.get(v, 0) for v in variables)

    leaders = [leader(b) for b in B]
    functions = {f for f, _ in leaders}
    count = 0
    for n in range(bound + 1):
        for f in functions:
            for a in product(range(n + 1), repeat=len(variables)):
                if sum(a) == n and not any(
                    g == f and all(ai >= li for ai, li in zip(a, l, strict=True))
                    for g, l in leaders
                ):
                    if n == bound:
                        return None
                    count += 1
    return count


def satisfies_janet_basis(B, generator, t, x, y):
    ts, xs, ys = Symbol('t'), Symbol('x'), Symbol('y')
    solution = {
        Function(name): Lambda((xs, ys, ts), g) for name, g in zip('TXY', generator, strict=True)
    }
    return all(
        simplify(b.expression().xreplace({x: xs, y: ys}).subs(solution).doit()) == 0 for b in B
    )


def test_janet_basis_free_particle_2d():
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)
    B = janet_basis_from_odes([D(x, t, t), D(y, t, t)], [x, y], [t])
    assert parametric_dimension(B, [t, x, y]) == 15
    ts, xs, ys = Symbol('t'), Symbol('x'), Symbol('y')
    generators = [
        (1, 0, 0),
        (0, 1, 0),
        (0, 0, 1),
        (0, ts, 0),
        (0, 0, ts),
        (0, xs, 0),
        (0, ys, 0),
        (0, 0, xs),
        (0, 0, ys),
        (ts, 0, 0),
        (xs, 0, 0),
        (ys, 0, 0),
        (ts**2, ts * xs, ts * ys),
        (ts * xs, xs**2, xs * ys),
        (ts * ys, xs * ys, ys**2),
    ]
    assert all(satisfies_janet_basis(B, g, t, x, y) for g in generators)
    assert not satisfies_janet_basis(B, (0, 0, xs**2), t, x, y)


def test_janet_basis_kepler():
    # x'' = -x/r**3, y'' = -y/r**3: time translation, rotation, and the
    # scaling of Kepler's third law
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)
    r3 = (x**2 + y**2) ** Rational(3, 2)
    B = janet_basis_from_odes([D(x, t, t) + x / r3, D(y, t, t) + y / r3], [x, y], [t])
    assert parametric_dimension(B, [t, x, y]) == 3
    ts, xs, ys = Symbol('t'), Symbol('x'), Symbol('y')
    for g in [(1, 0, 0), (0, -ys, xs), (3 * ts, 2 * xs, 2 * ys)]:
        assert satisfies_janet_basis(B, g, t, x, y)
    assert not satisfies_janet_basis(B, (0, xs, ys), t, x, y)


def test_is_janet_basis_of_odes_ranking():
    t = Symbol('t')
    x = Function('x')(t)
    y = Function('y')(t)
    free = [D(x, t, t), D(y, t, t)]
    B = janet_basis_from_odes(free, [x, y], [t])
    assert is_janet_basis_of_odes(B, free, [x, y], [t])
    # e.g. T_tt - 2 Y_ty: which term leads depends on the ranking of T and Y
    assert not is_janet_basis_of_odes(B, free, [x, y], [t], dependent_order=['Y', 'X', 'T'])
    assert not is_janet_basis_of_odes(B[1:], free, [x, y], [t])

    # all leaders of the Kepler basis are first derivatives, whatever the ranking
    r3 = (x**2 + y**2) ** Rational(3, 2)
    kepler = [D(x, t, t) + x / r3, D(y, t, t) + y / r3]
    B = janet_basis_from_odes(kepler, [x, y], [t])
    assert is_janet_basis_of_odes(
        B, kepler, [x, y], [t], dependent_order=['Y', 'X', 'T'], independent_order=['y', 'x', t]
    )


def test_symbolic_power_of_a_derivative():
    # #39: v_t = v_x**n v_xx is solved for v_xx = v_t v_x**(-n); v_x**n and
    # v_x**(-n) are one family (G and 1/G), not two independent generators.
    # The scalings (x, 2t, v) and (0, n t, -v) are symmetries (CRC Handbook,
    # Vol. 1, 10.3)
    x, t, n, V = Symbol('x'), Symbol('t'), Symbol('n'), Symbol('v')
    v = Function('v')(x, t)
    infinitesimals = OrderedDict({v: make_infinitesimal(v, v, x, t, name='V')})
    for s, name in ((x, 'X'), (t, 'T')):
        infinitesimals[s] = make_infinitesimal(s, v, x, t, name=name)
    det = overdetermined_system_pde(
        Derivative(v, t) - Derivative(v, x) ** n * Derivative(v, x, 2),
        [v],
        [x, t],
        infinitesimals=infinitesimals,
    )
    plain = {v: V}
    args = infinitesimals[x].xreplace(plain).args
    for generator in ({x: x, t: 2 * t, v: V}, {x: 0, t: n * t, v: -V}):
        solution = {
            infinitesimals[s].xreplace(plain).func: Lambda(args, generator[s]) for s in (x, t, v)
        }
        assert all(simplify(e.xreplace(plain).subs(solution).doit()) == 0 for e in det)


def test_float_in_the_equation():
    # #37: Kamke 1.641 has the float 0.5; solve() used to turn the whole
    # equation into floats, so the determining equation carried
    # sqrt(4*x**2*y + 1) and sqrt(4.0*x**2*y + 1.0) as different roots, and
    # the symmetry (1/x**2, 1/(2*x**5)) left a residue zero only numerically
    x, Y = Symbol('x'), Symbol('y')
    y = Function('y')(x)
    infinitesimals = OrderedDict(
        {x: make_infinitesimal(x, y, x, name='X'), y: make_infinitesimal(y, y, x, name='Y')}
    )
    ode = Derivative(y, x) - (x**4 * (4 * x**2 * y + 1) ** Rational(1, 2) + 0.5) / x**3
    det = overdetermined_system_ode(ode, [y], [x], infinitesimals=infinitesimals)
    assert not any(e.atoms(Float) for e in det)
    plain = {y: Y}
    X_, Y_ = (infinitesimals[v].xreplace(plain) for v in (x, y))
    solution = {X_.func: Lambda(X_.args, 1 / x**2), Y_.func: Lambda(Y_.args, 1 / (2 * x**5))}
    assert all(simplify(e.xreplace(plain).subs(solution).doit()) == 0 for e in det)


def test_absolute_value_of_a_dependent_variable():
    # #51: x1' = c - sin(x0) - x1 |x1| (ODEBench 44, pendulum with quadratic
    # damping). Abs(x1) used to become re, im and sign, and the Janet basis
    # stopped at an assertion; |x1| is now s*x1 with a constant sign s
    t, c = Symbol('t'), Symbol('c')
    x0, x1 = Function('x0')(t), Function('x1')(t)
    system = [Derivative(x0, t) - x1, Derivative(x1, t) - c + sin(x0) + x1 * Abs(x1)]
    det = overdetermined_system_odes(system, [x0, x1], [t])
    assert not any(e.has(re, im, Abs, sign) for e in det)
    equations, functions, variables, _ = _linear_system_odes(system, [x0, x1], [t])
    assert JanetBasis(equations, functions, variables).rank() == oo


NOT_POLYNOMIAL_IN_DERIVATIVES = [
    "Baumann p. 203: Kamke 7.13 u'' u''' - a sqrt(1 + b**2 u''**2) = 0",
    "CRC 1, 10.3: nonlinear filtration equation v_t = k(v_x) v_xx",
    "CRC 1, 10.4: potential filtration equation w_t = exp(w_xx)",
    "CRC 1, 12.4: w_tt = k w_xx**(-1/3)",
    "CRC 1, 12.4: w_tt = k log(w_xx)",
    "Gabel et al. 7: u_t = atan(u_xx)",
]


@pytest.mark.parametrize("name", NOT_POLYNOMIAL_IN_DERIVATIVES)
def test_not_polynomial_in_the_derivatives(name):
    # #5: square roots, fractional powers, log, atan and arbitrary functions
    # of derivatives raised PolynomialError; the published generators of
    # these catalogue entries solve the determining equations now
    from tests.symmetry_catalog import CATALOG

    (entry,) = [e for e in CATALOG if e.name == name]
    indep, dep = entry.variables()
    for result in verify_symmetries(
        entry.parsed_equations(), dep, indep, entry.parsed_generators()
    ):
        assert result, (result.generator, result.nonzero_residues())


def test_square_root_of_the_highest_derivative():
    # #5: Kamke 1.558, a x sqrt(y'**2 + 1) + x y' - y = 0: the root contains
    # the highest derivative; homogeneous, so (x, y) is a symmetry
    x, a, Y = Symbol('x'), Symbol('a'), Symbol('y')
    y = Function('y')(x)
    ode = a * x * (Derivative(y, x) ** 2 + 1) ** Rational(1, 2) + x * Derivative(y, x) - y
    assert verify_symmetry(ode, y, x, (x, Y))
    assert not verify_symmetry(ode, y, x, (1, 0))


def test_trigonometric_function_of_a_derivative():
    # #5: y'' = sin(y'), written with exponentials and split into real and
    # imaginary parts; the translations are symmetries, the scaling (x, y) not
    x = Symbol('x')
    y = Function('y')(x)
    ode = Derivative(y, x, 2) - sin(Derivative(y, x))
    assert verify_symmetry(ode, y, x, (1, 0))
    assert verify_symmetry(ode, y, x, (0, 1))
    assert not verify_symmetry(ode, y, x, (x, Symbol('y')))


def test_exponent_with_a_parameter_in_a_denominator():
    """#69: u_x**((5*q - 8)/q) and u_x**(-8/q) are one family of powers;
    as independent generators they split into too many determining
    equations (rank 2 instead of 3)."""
    from sympy import Function, Symbol, diff, symbols

    from delierium.infinitesimals import overdetermined_system_pde

    x, t, a, c, kappa, q = symbols("x t a c kappa q")
    u = Function("u")(x, t)
    p = 6 - 8 / q
    pde = diff(u, t) + kappa * p * diff(u, x) ** (p - 1) * diff(u, x, 2) - c * (a + u) ** q
    inf = create_infinitesimals([u], [x, t])
    plain = {u: Symbol("u")}
    system = [e.xreplace(plain) for e in overdetermined_system_pde(pde, [u], [x, t], inf)]
    functions = [inf[v].xreplace(plain) for v in (x, t, u)]
    assert JanetBasis(system, functions, [x, t, Symbol("u")]).rank() == 3


def test_verify_symmetry():
    """#4: residues, assumptions (initials), systems of ODEs, errors."""
    x, t, Y = Symbol("x"), Symbol("t"), Symbol("y")
    y = Function("y")(x)
    # y' y'' = 1: solving for y'' assumes y' != 0; d/dx, d/dy are symmetries
    ode = Derivative(y, x) * Derivative(y, x, 2) - 1
    result = verify_symmetry(ode, y, x, (1, 0))
    assert result and result.assumptions == [Derivative(y, x)]
    assert not verify_symmetry(ode, y, x, (Y, 0))
    with pytest.raises(ValueError, match="one component per coordinate"):
        verify_symmetry(ode, y, x, (1,))
    # the harmonic oscillator as a system: rotations in the (p, q) plane
    p, q = Function("p")(t), Function("q")(t)
    P, Q = Symbol("p"), Symbol("q")
    system = [Derivative(p, t) + q, Derivative(q, t) - p]
    results = verify_symmetries(system, [p, q], [t], [(1, 0, 0), (0, -Q, P), (0, Q, P)])
    assert [bool(r) for r in results] == [True, True, False]
    u, v = Function("u")(x, t), Function("v")(x, t)
    with pytest.raises(NotImplementedError, match="#21"):
        verify_symmetry([Derivative(u, t) - v, Derivative(v, t) - u], [u, v], [x, t], (0,) * 4)
