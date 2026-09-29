from sympy import Function, I, Rational, cos, exp, sin, sqrt, symbols

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
