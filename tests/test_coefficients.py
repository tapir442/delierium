from sympy import Function, I, Rational, cos, cosh, exp, nan, sin, sinh, sqrt, symbols, tan, zoo

from delierium.coefficients import Coeff

x, y, n = symbols("x y n")


def test_powers_of_one_base_share_a_generator():
    assert Coeff(sqrt(x)) ** 2 == Coeff(x)
    assert Coeff(x ** Rational(-3, 2)) * Coeff(x) ** 2 == Coeff(sqrt(x))
    assert Coeff(exp(x / 2)) ** 2 - Coeff(exp(x)) == 0
    assert Coeff(y ** (n + 1)) / Coeff(y**n) == Coeff(y)
    assert Coeff(y ** (-n - 1)) * Coeff(y ** (n + 1)) == 1


def test_diff_chain_rule():
    f = Function("f")(x)
    assert Coeff(y**n).diff(y) == Coeff(n * y ** (n - 1))
    assert Coeff(sin(x) * exp(2 * x)).diff(x) == Coeff(
        cos(x) * exp(2 * x) + 2 * sin(x) * exp(2 * x)
    )
    assert Coeff(x * f).diff(x, x) == Coeff(2 * f.diff(x) + x * f.diff(x, 2))
    # a derivative only involves the generators the coefficient contains
    assert Coeff(x).diff(x) == 1


def test_floats_are_exact_decimals():
    # a float is the decimal it prints as, not its binary approximation
    assert Coeff(0.5 * x).is_field
    assert Coeff(0.5 * x) == Coeff(x / 2)
    assert Coeff(0.1 * x + 0.25) == Coeff(x / 10 + Rational(1, 4))
    assert Coeff(x**0.5) == Coeff(sqrt(x))


def test_algebraic_elements_stay_expressions():
    for e in (sqrt(2) * x, I * x, sqrt(x + 1)):
        assert not Coeff(e).is_field
    r = Coeff(sqrt(x**2 + 1))
    # a relation the field would miss is recognized by cancel
    assert r * r - Coeff(x**2 + 1) == 0
    assert not (r * r - Coeff(x**2 + 1))
    assert (r + Coeff(x)) - Coeff(x) == r


def test_growing_field_lifts_old_elements():
    a = Coeff(x / (x + 1))
    b = Coeff(Function("g")(x, y))  # new generator
    assert (a * b) / b == a
    c = Coeff(x ** Rational(1, 3))  # replaces the generator x by a root of it
    assert c**3 * a == Coeff(x**2 / (x + 1))


def test_janet_basis_has_a_field_of_its_own():
    from sympy import diff

    from delierium import coefficients
    from delierium.janet_basis import JanetBasis

    default = coefficients._state()
    before = default.symbols
    a = symbols("a")
    u = Function("u")(x, y)
    janet = JanetBasis([diff(u, x) - a * exp(x) * u, diff(u, y) - a * u], [u], [x, y])
    assert coefficients._state() is default and default.symbols == before
    # its coefficients still work together with those of the default field
    c = janet.S[0].p[-1].coeff
    assert c - c * Coeff(1) == 0


def test_trigonometric_identities():
    """sin, cos of one argument and their multiples are related (#61)."""
    x, a = symbols("x a")
    assert not Coeff(sin(x) ** 2 + cos(x) ** 2 - 1)
    assert Coeff(sin(2 * x)) == Coeff(2 * sin(x) * cos(x))
    assert not Coeff(sin(2 * x) * cos(x)) - 2 * Coeff(sin(x) * cos(x) ** 2)
    assert Coeff(sin(x)) * Coeff(sin(x)) + Coeff(cos(x)) ** 2 == 1
    assert Coeff(sin(x)) / Coeff(cos(x)) == Coeff(tan(x))
    assert not Coeff(cosh(a * x) ** 2 - sinh(a * x) ** 2 - 1)


def test_janet_basis_does_not_divide_by_a_trigonometric_zero():
    """#61: the second equation is 2 * (first) + f_y; the basis divided by
    2 sin(x) cos(x) - sin(2 x), which is 0."""
    from sympy import simplify

    from delierium.janet_basis import JanetBasis

    x, y = symbols("x y")
    f, g = Function("f")(x, y), Function("g")(x, y)
    eqs = [
        sin(x) * cos(x) ** 2 * f.diff(x) + g,
        sin(2 * x) * cos(x) * f.diff(x) + 2 * g + f.diff(y),
    ]
    basis = [simplify(e.expression()) for e in JanetBasis(eqs, [f, g], [x, y]).S]
    assert g.diff(y) in basis
    assert all(not e.has(zoo, nan) for e in basis)
