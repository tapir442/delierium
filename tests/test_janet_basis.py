"""Tests for delierium.janet_basis"""

from itertools import product

import pytest
from sympy import (
    Add,
    Derivative,
    Function,
    Mul,
    Poly,
    Rational,
    Symbol,
    diff,
    exp,
    expand,
    oo,
    simplify,
    sin,
    sinh,
    solve,
    symbols,
    sympify,
)

from delierium.infinitesimals import (
    _linear_system_ode,
    create_infinitesimals,
    is_janet_basis_of_ode,
    janet_basis_from_ode,
    overdetermined_system_pde,
)
from delierium.janet_basis import (
    LHDP,
    JanetBasis,
    _janet_completion,
    integrability_conditions,
    is_janet_basis_of,
    janet_type,
    reduce_by_system,
)
from delierium.matrix_order import Context, Mgrevlex, Mgrlex, Mlex


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


def parametric_count(B, variables, functions, bound=6):
    """Number of parametric derivatives of the Janet basis B, None if there
    are some of order bound (i.e. infinitely many)."""
    leaders = leading_orders(B, variables)
    count = 0
    for f in functions:
        for orders in product(range(bound + 1), repeat=len(variables)):
            n = sum(orders)
            if n > bound or any(
                g == f and all(o >= a for o, a in zip(orders, lead, strict=True))
                for g, lead in leaders
            ):
                continue
            if n == bound:
                return None
            count += 1
    return count


@pytest.mark.parametrize(
    ("name", "pde", "dimension"),
    [
        # {d_x, d_t, x d_x - t d_t}
        ("sine-Gordon", lambda u, x, t: diff(u, x, t) - sin(u), 3),
        # {d_x, d_t, t d_x + x d_t}
        ("sine-Gordon, laboratory", lambda u, x, t: diff(u, t, 2) - diff(u, x, 2) - sin(u), 3),
        # {d_x, d_t, t d_t - (1 + u) d_u}
        (
            "BBM",
            lambda u, x, t: diff(u, t) + diff(u, x) + u * diff(u, x) - diff(u, x, x, t),
            3,
        ),
        # X = f(x), T = g(t), U = -f' - g': infinite
        ("Liouville", lambda u, x, t: diff(u, x, t) - exp(u), None),
        # the same, written with unevaluated derivatives in a non-canonical
        # order of the variables (as in the catalogue); this gave infinitely
        # many symmetries for sine-Gordon and 4 for BBM
        ("sine-Gordon, Derivative", lambda u, x, t: Derivative(u, x, t) - sin(u), 3),
        (
            "BBM, Derivative",
            lambda u, x, t: diff(u, t) + diff(u, x) + u * diff(u, x) - Derivative(u, (x, 2), t),
            3,
        ),
        ("Liouville, Derivative", lambda u, x, t: Derivative(u, x, t) - exp(u), None),
    ],
)
@pytest.mark.parametrize("variable_order", ["xt", "tx"])
def test_janet_basis_dimension_mixed_leader_pde(name, pde, dimension, variable_order):
    # PDEs with a mixed highest derivative (u_xt, u_xxt); the catalogue
    # check of 2026-09 reported wrong dimensions for them, not reproducible
    x, t, us = symbols("x t u")
    indep = [x, t] if variable_order == "xt" else [t, x]
    u = Function("u")(*indep)
    inf = create_infinitesimals([u], indep)
    system = [
        e.xreplace({u: us})
        for e in overdetermined_system_pde(pde(u, x, t), [u], indep, infinitesimals=inf)
    ]
    functions = [inf[v].xreplace({u: us}) for v in [*indep, u]]
    variables = [*indep, us]
    B = JanetBasis(system, functions, variables).S
    count = parametric_count(B, variables, [f.func for f in functions])
    assert count == dimension, name


@pytest.mark.parametrize("sort_order", [Mgrevlex, Mgrlex, Mlex])
@pytest.mark.parametrize("variables", ["xy", "yx"])
def test_representation_of_the_input(sort_order, variables):
    # every equation of Schwarz's system (2.25) is a combination of the
    # Janet basis elements and their derivatives, and nothing else is
    x, y = symbols("x y")
    z, w = Function("z")(x, y), Function("w")(x, y)
    system = [
        diff(z, y, y) + diff(z, y) / (2 * y),
        diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y,
        diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y),
        diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2),
    ]
    janet = JanetBasis(system, [w, z], [x, y] if variables == "xy" else [y, x], sort_order)
    for e in system:
        terms, remainder = janet.representation(e)
        assert remainder == 0
        assert simplify(janet.combination(terms) - e) == 0
    assert janet.representation(diff(z, x, y) + z)[1] != 0


def schwarz_type(ode):
    # Janet basis type of the determining system of ode under Schwarz's
    # ranking: grlex, eta > xi, y > x
    x = Symbol("x")
    y = Function("y")(x)
    system, inf, variables, _ = _linear_system_ode(ode(y, x), y, x)
    return JanetBasis(system, inf[::-1], variables[::-1], Mgrlex).type()


@pytest.mark.parametrize(
    ("example", "ode", "dimension", "name"),
    [
        (
            "5.10",
            lambda y, x: x**4 * y.diff(x, 2) - x**2 * y.diff(x) ** 2 - x**3 * y.diff(x) + 4 * y**2,
            1,
            "J^(2,2)_1,2",
        ),
        # Kamke 6.227, misprinted in the book
        (
            "5.11",
            lambda y, x: (x * y.diff(x) - y) * y.diff(x, 2) + 4 * y.diff(x) ** 2,
            2,
            "J^(2,2)_2,3",
        ),
        (
            "5.12",
            lambda y, x: 4 * y.diff(x, 2) * y - 3 * y.diff(x) ** 2 - 12 * y**3,
            2,
            "J^(2,2)_2,3",
        ),
        (
            "5.14",
            lambda y, x: y.diff(x, 2) * y + x * y.diff(x, 2) + y.diff(x) ** 2 - y.diff(x),
            3,
            "J^(2,2)_3,6",
        ),
        (
            "5.15",
            lambda y, x: (
                y.diff(x, 2) * y.diff(x) * y * x**6
                - 2 * y.diff(x) ** 3 * x**6
                + 2 * y.diff(x) ** 2 * y * x**5
                + y**5
            ),
            3,
            "J^(2,2)_3,6",
        ),
        (
            "5.15, second equation",
            lambda y, x: (
                y.diff(x) * y.diff(x, 2)
                + 2 * y.diff(x, 2)
                - y.diff(x) ** 4
                - 12 * y.diff(x) ** 3
                - 54 * y.diff(x) ** 2
                - 108 * y.diff(x)
                - 81
            ),
            3,
            "J^(2,2)_3,7",
        ),
        (
            "5.33",
            lambda y, x: (
                (
                    y.diff(x, 3) * y.diff(x) * y**6
                    - 3 * y.diff(x, 2) ** 2 * y**6
                    + (6 * y.diff(x) * y + 2 * y.diff(x) / x**2 + 3 * y**2 / x)
                    * y.diff(x, 2)
                    * y.diff(x)
                    * y**4
                    - y.diff(x) ** 5 / x**5
                    - 2 * (3 * y + 2 / x**2) * y.diff(x) ** 4 * y**3
                    - 6 * y**5 * y.diff(x) ** 3 / x
                )
                * x**5
            ),
            3,
            "J^(2,2)_3,7",
        ),
        # type J^(2,2)_4,17, beyond Tables 2.1 - 2.3
        (
            "5.45",
            lambda y, x: (
                y.diff(x, 3) * (y.diff(x) + 1) * (y + x - Rational(1, 2))
                - 3 * y.diff(x, 2) ** 2 * (y + x - Rational(1, 2))
                - 4 * x * y.diff(x) ** 5
                + 4 * y.diff(x) ** 4 * (y - 4 * x)
                + 8 * y.diff(x) ** 3 * (2 * y - 3 * x)
                + 8 * y.diff(x) ** 2 * (3 * y - 2 * x)
                + 4 * y.diff(x) * (4 * y - x)
                + 4 * y
            ),
            4,
            None,
        ),
    ],
)
def test_janet_basis_type_schwarz_chapter_5(example, ode, dimension, name):
    # Schwarz names the type of the Janet basis in these examples
    t = schwarz_type(ode)
    assert (t.dimension, t.name) == (dimension, name), example


def test_janet_basis_type_infinite():
    # u_xt = exp(u) (Liouville): infinitely many parametric derivatives
    x, t, us = symbols("x t u")
    u = Function("u")(x, t)
    inf = create_infinitesimals([u], [x, t])
    system = [
        e.xreplace({u: us})
        for e in overdetermined_system_pde(diff(u, x, t) - exp(u), [u], [x, t], infinitesimals=inf)
    ]
    functions = [inf[v].xreplace({u: us}) for v in [x, t, u]]
    jt = JanetBasis(system, functions, [x, t, us]).type()
    assert jt.parametric is None
    assert jt.dimension == oo


a1, a2, a3, b1, b2, b3, c1, c2, c3 = (
    Function(n)(*symbols("x y")) for n in ["a1", "a2", "a3", "b1", "b2", "b3", "c1", "c2", "c3"]
)


def _theorem_2_15():
    x, y = symbols("x y")
    z = Function("z")(x, y)
    a, b = Function("a")(x, y), Function("b")(x, y)
    d = diff
    t = Rational(1, 3)
    return z, {
        "J1": ([d(z, x) + a * z, d(z, y) + b * z], [d(a, y) - d(b, x)], {}),
        "J2,1": (
            [d(z, y) + a1 * d(z, x) + a2 * z, d(z, x, 2) + b1 * d(z, x) + b2 * z],
            [
                d(a1, x, 2) - d(b1, x) * a1 - d(a1, x) * b1 + 2 * d(a2, x) - d(b1, y),
                d(a2, x, 2) + d(a2, x) * b1 - 2 * d(a1, x) * b2 - d(b2, x) * a1 - d(b2, y),
            ],
            {},
        ),
        "J2,2": (
            [d(z, x) + a1 * z, d(z, y, 2) + b1 * d(z, y) + b2 * z],
            [d(b1, x) - 2 * d(a1, y), d(a1, y, 2) + d(a1, y) * b1 - d(b2, x)],
            {},
        ),
        "J3,1": (
            [
                d(z, y) + a1 * d(z, x) + a2 * z,
                d(z, x, 3) + b1 * d(z, x, 2) + b2 * d(z, x) + b3 * z,
            ],
            [
                d(a1, x, 2) - t * d(b1, y) - t * d(b1, x) * a1 + d(a2, x) - t * d(a1, x) * b1,
                d(a2, x, 3)
                + d(a2, x, 2) * b1
                - d(b3, y)
                - d(b3, x) * a1
                + d(a2, x) * b2
                - 3 * d(a1, x) * b3,
                d(b1, x, y)
                + d(b1, x, 2) * a1
                + 6 * d(a2, x, 2)
                - 3 * d(b2, y)
                - 3 * d(b2, x) * a1
                + 4 * t * d(b1, y) * b1
                + 2 * d(b1, x) * d(a1, x)
                + 2 * d(a2, x) * b1
                - 6 * d(a1, x) * b2
                + 4 * t * b1 * d(a1 * b1, x),
            ],
            # the third condition is the book's after eliminating b1_y by the first
            {(b1, y): 0},
        ),
        "J3,2": (
            [
                d(z, x, 2) + a1 * d(z, y) + a2 * d(z, x) + a3 * z,
                d(z, x, y) + b1 * d(z, y) + b2 * d(z, x) + b3 * z,
                d(z, y, 2) + c1 * d(z, y) + c2 * d(z, x) + c3 * z,
            ],
            [
                d(a1, y) - d(b1, x) + a1 * b2 - a1 * c1 - a2 * b1 + a3 + b1**2,
                d(a2, y) - d(b2, x) - a1 * c2 + b1 * b2 - b3,
                d(a3, y) - d(b3, x) - a1 * c3 - a2 * b3 + a3 * b2 + b1 * b3,
                d(b1, y) - d(c1, x) + a1 * c2 - b1 * b2 + b3,
                d(b2, y) - d(c2, x) + a2 * c2 - b1 * c2 - b2**2 + b2 * c1 - c3,
                d(b3, y) - d(c3, x) + a3 * c2 - b1 * c3 - b2 * b3 + b3 * c1,
            ],
            {},
        ),
        "J3,3": (
            [d(z, x) + a1 * z, d(z, y, 3) + b1 * d(z, y, 2) + b2 * d(z, y) + b3 * z],
            [
                d(b1, x) - 3 * d(a1, y),
                d(a1, y, 2) - t * d(b2, x) + 2 * t * d(a1, y) * b1,
                d(b2, x, y)
                - 3 * d(b3, x)
                + t * d(b2, x) * b1
                - 2 * d(b1, y) * d(a1, y)
                + 3 * d(a1, y) * b2
                - 2 * t * d(a1, y) * b1**2,
            ],
            # the third condition is the book's after eliminating b1_x, b2_x
            {(b1, x): 0, (b2, x): 1},
        ),
    }


def _eliminate(e, rules):
    """Replace every derivative of f by v (possibly by further variables too)
    by the corresponding derivative of rules[(f, v)]."""

    def repl(d):
        for (f, v), solution in rules.items():
            if d.expr == f and v in d.variables:
                rest = list(d.variables)
                rest.remove(v)
                return diff(solution, *rest) if rest else solution
        return d

    for _ in range(3):
        e = e.replace(lambda d: isinstance(d, Derivative), repl)
    return expand(e)


def _proportional(e, f):
    return f != 0 and e != 0 and simplify(e / f).is_number


@pytest.mark.parametrize("name", ["J1", "J2,1", "J2,2", "J3,1", "J3,2", "J3,3"])
def test_integrability_conditions_schwarz_theorem_2_15(name):
    # Schwarz, Theorem 2.15, pp. 59-60: the conditions on the coefficients of
    # the Janet basis types J^(1,2) (grlex, y > x); the book simplifies two of
    # them by the others of the same type
    z, types = _theorem_2_15()
    x, y = symbols("x y")
    system, book, eliminations = types[name]
    computed = integrability_conditions(system, [z], [y, x], Mgrlex)
    assert len(computed) == len(book)
    rules = {(f, v): solve(book[k], diff(f, v))[0] for (f, v), k in eliminations.items()}
    for b in book:
        b = expand(b)
        assert any(_proportional(e, b) for e in computed) or any(
            _proportional(_eliminate(e, rules), _eliminate(b, rules)) for e in computed
        ), b
    context = Context([z], [y, x], Mgrlex)
    lhdps = [LHDP(s, context) for s in system]
    assert janet_type(lhdps, context).name == f"J^(1,2)_{name[1:]}"


def _ode_dimension(B, x, y):
    leaders = leading_orders(B, [x, y])
    count = 0
    for f in {f for f, _ in leaders}:
        for i, j in product(range(9), repeat=2):
            if i + j < 9 and not any(g == f and i >= a and j >= b for g, (a, b) in leaders):
                count += 1
    return count


def test_assumed_nonzero_kamke_6_74():
    # x y'' + 2 y' + a x^m y^n = 0: one symmetry in general (Schwarz), but
    # more for special parameters; the Janet basis is computed for the
    # generic case and says which factors it assumes nonzero
    x = Symbol("x")
    y = Function("y")(x)
    a, m, n = symbols("a m n")
    ode = a * x**m * y**n + x * diff(y, x, 2) + 2 * diff(y, x)
    B = janet_basis_from_ode(ode, y, x)
    assert _ode_dimension(B, x, y) == 1
    for factor in (a, n, n - 1, m + 3, m - n):
        assert factor in B.assumed_nonzero
        assert [factor] in B.parameter_conditions
    assert set(B.singular_loci) == {x, y}
    # and these special cases do have more symmetries
    for special, dimension in (({a: 0}, 8), ({n: 1}, 8), ({n: 0}, 8), ({m: -3}, 2), ({m: n}, 2)):
        assert _ode_dimension(janet_basis_from_ode(ode.subs(special), y, x), x, y) == dimension


def _bases_for_derivative_classes():
    x, y = symbols("x y")
    z = Function("z")(x, y)
    w = Function("w")(x, y)
    # Schwarz, system (2.25): rank 2
    g1 = diff(z, y, y) + diff(z, y) / (2 * y)
    g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
    g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
    g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
    yield JanetBasis([g2, g3, g4, g1], (w, z), (x, y))
    # the determining equations of Kamke 6.57 with r = 3: rank 3
    Y = Function("y")(x)
    ode = diff(Y, x, 2) - (x * diff(Y, x) - Y) ** 3
    system, functions, variables, _ = _linear_system_ode(ode, Y, x)
    yield JanetBasis(system, functions, variables)
    # y'' = 0: rank 8, parametric derivatives up to order 2
    ode = diff(Y, x, 2)
    system, functions, variables, _ = _linear_system_ode(ode, Y, x)
    yield JanetBasis(system, functions, variables)
    # z_x = 0: infinite rank
    yield JanetBasis([diff(z, x)], [z], [x, y])


@pytest.mark.parametrize("janet", list(_bases_for_derivative_classes()))
def test_parametric_and_principal_derivatives(janet):
    """Up to any order, every derivative is either parametric or principal,
    and a large enough bound gives the parametric derivatives of type()."""
    for n in range(4):
        parametric = janet.parametric_derivatives(n)
        principal = janet.principal_derivatives(n)
        assert not set(parametric) & set(principal)
        count = sum(
            1 for o in product(range(n + 1), repeat=len(janet.context.independent)) if sum(o) <= n
        )
        assert len(parametric) + len(principal) == count * len(janet.context.dependent)
    rank = janet.rank()
    if rank == oo:
        assert janet.parametric_derivatives() is None
    else:
        assert janet.parametric_derivatives(6) == janet.parametric_derivatives()
        assert len(janet.parametric_derivatives()) == rank


def test_janet_basis_lex_system_of_two_functions():
    # formerly notebooks/Schwarz/AllTypes.ipynb, whose result was "wrong by
    # any means" then; the expected basis is w_xx, w_y, z + 2y w_x
    x, y = symbols("x y")
    z = Function("z")(x, y)
    w = Function("w")(x, y)
    system = [
        diff(w, y, y) + 3 * diff(w, y) / (4 * y),
        diff(z, x, 2) + 3 * y**2 * diff(z, y) - 6 * y**2 * diff(w, x) - 6 * y * z,
        diff(z, x, y)
        - diff(w, x, x) / 2
        - 3 * diff(z, x) / (4 * y)
        - Rational(9, 2) * y**2 * diff(w, y),
        diff(z, y, y) - 2 * diff(w, x, y) - 3 * diff(z, y) / (4 * y) + 3 * z / (4 * y**2),
    ]
    expected = [diff(w, x, 2), diff(w, y), 2 * y * diff(w, x) + z]
    assert is_janet_basis_of(expected, system, (z, w), (y, x), Mlex)


def test_equation_zero_after_simplify():
    # #38: for u_t = (u**sigma u_x)_x one determining equation is zero only
    # after simplify() (sigma u**(sigma - 1) - sigma u**sigma/u); JanetBasis
    # used to stop at an assertion in LHDP._init. Dimension 4 (CRC Handbook,
    # Vol. 1, 10.2): translations, x d/dx + 2t d/dt, sigma x d/dx + 2u d/du
    x, t, sigma = symbols("x t sigma")
    u = Function("u")(x, t)
    infinitesimals = create_infinitesimals([u], [x, t])
    det = overdetermined_system_pde(
        diff(u, t) - diff(u**sigma * diff(u, x), x), [u], [x, t], infinitesimals=infinitesimals
    )
    assert any(simplify(e) == 0 and e != 0 for e in det)
    plain = {u: Symbol("u")}
    functions = [infinitesimals[v].xreplace(plain) for v in (x, t, u)]
    janet = JanetBasis([e.xreplace(plain) for e in det], functions, [x, t, Symbol("u")])
    assert janet.rank() == 4
    assert (
        LHDP(
            sigma * Symbol("u") ** (sigma - 1) - sigma * Symbol("u") ** sigma / Symbol("u"),
            janet.context,
        ).p
        == []
    )


def test_hyperbolic_coefficients():
    # #52: the determining equations of sinh-Gordon w_tt = a w_xx + b sinh(lam w)
    # (EqWorld 2.1.5) made simplify() fail inside trigsimp/collect on mixed
    # derivatives; dimension 3 (translations and the boost)
    x, t, a, b, lam = symbols("x t a b lam")
    w = Function("w")(x, t)
    infinitesimals = create_infinitesimals([w], [x, t])
    det = overdetermined_system_pde(
        diff(w, t, 2) - a * diff(w, x, 2) - b * sinh(lam * w),
        [w],
        [x, t],
        infinitesimals=infinitesimals,
    )
    plain = {w: Symbol("w")}
    functions = [infinitesimals[v].xreplace(plain) for v in (x, t, w)]
    janet = JanetBasis([e.xreplace(plain) for e in det], functions, [x, t, Symbol("w")])
    assert janet.rank() == 3


def _polynomials(janet, f, variables):
    """The Janet basis of a system with constant coefficients as polynomials
    (d/dx -> x)."""
    result = set()
    for e in janet.S:
        expr = e.expression().replace(
            lambda a: isinstance(a, Derivative),
            lambda a: Mul(*(v**k for v, k in a.variable_count)),
        )
        result.add(expand(expr.xreplace({f: 1})))
    return result


def _operator(polynomial, f, variables):
    terms = Poly(polynomial, *variables).terms()
    return Add(
        *(
            c
            * (
                Derivative(f, *[(v, k) for v, k in zip(variables, m, strict=True) if k])
                if any(m)
                else f
            )
            for m, c in terms
        )
    )


# Janet bases of constant coefficient systems, as computed by CoCoA 5
# (JanetBasis, degrevlex): the minimal reduced Janet basis is unique (#54)
COCOA_JANET_BASES = [
    (
        "CoCoA manual",
        "x y z",
        ["x - y", "x**2 - z + 1", "x**3 - y**2"],
        ["x - y", "z**2 - 3*z + 2", "y*z - y - z + 1", "y**2 - z + 1"],
    ),
    (
        "Janet's example: tails reduced",
        "x y z",
        ["z**2 - y**2", "x*z - y*z"],
        ["y**2 - z**2", "x*z - y*z", "x*y*z - z**3", "x*y**2 - y*z**2"],
    ),
    (
        "same leading derivative twice before #54",
        "x y z w",
        ["-y*z**2/2", "w**2 - x*z**2 - y**2/2"],
        None,
    ),
    (
        "random 98: incomplete reduction before #54",
        "x y z w",
        ["-x**2*y", "3*w*y**2", "w**2*x + w*y + 3*x*z**2 - 3*z**2"],
        None,
    ),
]


@pytest.mark.parametrize(
    "name, variables, system, expected", COCOA_JANET_BASES, ids=[c[0] for c in COCOA_JANET_BASES]
)
def test_minimal_reduced_janet_basis(name, variables, system, expected):
    """Distinct leading derivatives, Janet complete with no redundant element,
    reduced tails; equal to CoCoA's where given."""
    variables = symbols(variables)
    f = Function("f")(*variables)
    janet = JanetBasis([_operator(sympify(p), f, variables) for p in system], (f,), variables)
    leading = [tuple(e.order) for e in janet.S]
    assert len(leading) == len(set(leading))
    generators = [
        m
        for m in leading
        if not any(o != m and all(a >= b for a, b in zip(m, o, strict=True)) for o in leading)
    ]
    assert _janet_completion(generators, len(variables)) == set(leading)
    for e in janet.S:
        for term in e.p[1:]:
            assert not any(
                all(a >= b for a, b in zip(term.order, g.order, strict=True)) for g in janet.S
            ), (e, term)
    if expected is not None:
        assert _polynomials(janet, f, variables) == {expand(sympify(p)) for p in expected}


def test_reduce_by_system_reduces_fully():
    """After a reduction by a later element, earlier ones are tried again
    (#54): D(x,y,z**4) of random 98 reduced to D(w**3, y**2), which D(w, y**2)
    reduces further."""
    x, y, z, w = symbols("x y z w")
    f = Function("f")(x, y, z, w)
    context = Context((f,), (x, y, z, w), Mgrevlex)
    S = [
        LHDP(f.diff(w, y, y), context),
        LHDP(f.diff(x, y, z, 4) - f.diff(w, 3, y, y), context),
        LHDP(f.diff(x, 5), context),  # last: reduces nothing
    ]
    assert reduce_by_system(LHDP(f.diff(x, y, z, 4), context), S, context) is None
