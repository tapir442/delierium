"""Tests for delierium.invariants: invariants, canonical coordinates and
differential invariants of a given generator (#42)"""

import pytest
from sympy import Function, Matrix, Rational, Symbol, diff, exp, simplify, symbols, sympify

from delierium import VectorField, prolongation
from delierium.invariants import (
    _is_zero,
    canonical_coordinates,
    differential_invariants,
    invariants,
)

x, y, t, u, a, b = symbols("x y t u a b")


@pytest.mark.parametrize(
    "generator, coordinates",
    [
        ((1, 0), (x, y)),
        ((x, y), (x, y)),
        ((-y, x), (x, y)),
        ((y, -x), (x, y)),
        ((a * x, b * u), (x, u)),  # SymPy's pdsolve: NotImplementedError (Baumann 4.2.3)
        ((u, -x), (x, u)),  # Baumann prints t = -arctan(x/u), which gives X t = -1
        ((x**2, x * y), (x, y)),
        ((t, 0, 1), (x, t, u)),
        ((2 * t, 0, 0, -u * x), (x, y, t, u)),
        ((x**2 - y**2, 2 * x * y, 2 * u * x), (x, y, u)),
        ((t * y, t**2, 0, y / 6), (x, y, t, u)),
    ],
)
def test_canonical_coordinates(generator, coordinates):
    X = VectorField(generator, coordinates)
    r, s = canonical_coordinates(generator, coordinates)
    assert len(r) == len(coordinates) - 1
    assert all(simplify(X(i)) == 0 for i in r)
    # X s = 1 near a point with positive coordinates (the branch of a root)
    point = {z: k + 2 for k, z in enumerate(coordinates)} | {a: 2, b: 3}
    assert abs((X(s) - 1).xreplace(point).evalf()) < 1e-12 or simplify(X(s) - 1) == 0
    assert invariants(X) == r


def test_rotation_on_its_branch():
    r, s = canonical_coordinates((-y, x), (x, y))
    X = VectorField((-y, x), (x, y))
    assert r == [x**2 + y**2]
    assert X(s).subs({x: 3, y: 4}) == 1


def test_heat_galilei():
    """2t d/dx - x u d/du (heat equation): the invariant u exp(x**2/(4t))."""
    assert u * exp(x**2 / (4 * t)) in invariants((2 * t, 0, -x * u), (x, t, u))


def test_differential_invariants_reduce_the_order():
    """y'' = y'**2/y + y' is invariant under the scaling y d/dy: in the
    differential invariants r = x, v = y'/y it is the first order ODE
    dv/dr = v."""
    y = Function("y")(x)
    r, v, dv = differential_invariants((0, Symbol("y")), y, x, 2)
    assert r == x
    assert simplify(v - diff(y, x) / y) == 0
    on_solutions = dv.subs(diff(y, x, 2), diff(y, x) ** 2 / y + diff(y, x))
    assert simplify(on_solutions - v) == 0


def test_differential_invariants_of_a_translation():
    y = Function("y")(x)
    assert differential_invariants((1, 0), y, x, 2) == [
        y,
        1 / diff(y, x),
        -diff(y, x, 2) / diff(y, x) ** 3,
    ]


@pytest.mark.parametrize(
    "generator",
    [(-y, x), (x, y), (x**2, x * y), (1, y), (0, exp(x))],
)
def test_differential_invariants_ode(generator):
    """Annihilated by the prolonged generator; order + 1 of them."""
    f = Function("y")(x)
    on_f = {y: f}
    infinitesimals = {x: sympify(generator[0]).subs(on_f), f: sympify(generator[1]).subs(on_f)}
    found = differential_invariants(generator, f, x, 2)
    assert len(found) == 3
    assert all(simplify(prolongation(e, infinitesimals, [f], [x])) == 0 for e in found)


@pytest.mark.parametrize(
    "generator",
    [(x, 2 * t, 0), (2 * t, 0, -x * u), (1, 0, 0), (0, 0, u), (x, 2 * t, -u)],
)
def test_differential_invariants_pde(generator):
    """Heat equation generators: N - 1 = 2 of order 0, 2 of order 1, 3 of
    order 2, all annihilated by the prolonged generator."""
    f = Function("u")(x, t)
    on_f = {u: f}
    infinitesimals = {
        x: sympify(generator[0]).subs(on_f),
        t: sympify(generator[1]).subs(on_f),
        f: sympify(generator[2]).subs(on_f),
    }
    found = differential_invariants(generator, f, [x, t], 2)
    assert len(found) == 2 + 2 + 3
    assert all(simplify(prolongation(e, infinitesimals, [f], [x, t])) == 0 for e in found)


def test_arguments():
    with pytest.raises(ValueError, match="zero generator"):
        invariants((0, 0), (x, y))
    with pytest.raises(ValueError, match="coordinates are needed"):
        invariants((1, 0))
    with pytest.raises(ValueError, match="one coefficient per coordinate"):
        invariants((1, 0, 0), (x, y))
    with pytest.raises(ValueError, match="order"):
        differential_invariants((1, 0), Function("y")(x), x, -1)


# entries with a generator whose characteristic system takes a minute
SLOW = {
    "Hydon Example 2.17: y' = (y**3 + y - 3 x**2 y)/(3 x y**2 + x - x**3)",
    "CRC 1, 12.2: u_tt = (A x + B)**(2 C) u_xx",
    "Bluman-Anco (4.64): u_tt = c(x)**2 u_xx, c = (1 + x)**(1 + A/2) (1 - x)**(1 - A/2)",
    "Kahlmeyer et al. example10: y' = (t*log(y1), t*y0**2)",
}


def _catalogue_generators():
    from tests.symmetry_catalog import CATALOG  # pylint: disable=import-outside-toplevel

    for entry in CATALOG:
        if entry.name in SLOW:
            continue
        coordinates = [Symbol(v) for v in entry.independent + entry.dependent]
        for k, generator in enumerate(entry.parsed_generators()):
            yield pytest.param(generator, coordinates, id=f"{entry.name} [{k}]")


@pytest.mark.slow
@pytest.mark.parametrize("generator, coordinates", list(_catalogue_generators()))
def test_catalogue_generators(generator, coordinates):
    """Canonical coordinates of every generator of the catalogue: verified,
    or NotImplementedError (15 of 1439, e.g. nested roots, Kamke 1.535)."""
    X = VectorField(generator, coordinates)
    try:
        r, s = canonical_coordinates(X)
    except NotImplementedError:
        return
    assert all(_is_zero(X(i)) for i in r)
    assert _is_zero(X(s) - 1)


# Hydon, Symmetry Methods for Differential Equations, chapters 2, 4 and 5


def test_hydon_2_7_scaling():
    """(x, k y): (r, s) = (x**(-k) y, log|x|)."""
    k = Symbol("k", positive=True)
    assert canonical_coordinates((x, k * y), (x, y)) == ([y / x**k], sympify("log(x)"))


def test_hydon_2_8_inversions():
    """(x**2, x y): (r, s) = (y/x, -1/x)."""
    assert canonical_coordinates((x**2, x * y), (x, y)) == ([y / x], -1 / x)


def _reduced(omega, generator):
    """ds/dr of y' = omega in the canonical coordinates of the generator
    (Hydon 2.46), in x and y."""
    (r,), s = canonical_coordinates(generator, (x, y))
    return r, simplify((s.diff(x) + omega * s.diff(y)) / (r.diff(x) + omega * r.diff(y)))


def test_hydon_2_11_reduced_to_quadrature():
    """y' = (y + 1)/x + y**2/x**3 with the inversions: ds/dr = 1/(1 + r**2)."""
    r, reduced = _reduced((y + 1) / x + y**2 / x**3, (x**2, x * y))
    assert simplify(reduced - 1 / (1 + r**2)) == 0


@pytest.mark.parametrize(
    "omega, generator",
    [
        (x * y**2 - 2 * y / x - 1 / x**3, (x, -2 * y)),  # 2.10, Riccati
        ((y - 4 * x * y**2 - 16 * x**3) / (y**3 + 4 * x**2 * y + x), (-y, 4 * x)),  # 2.12
        ((1 - y**2) / (x * y) + 1, (1 / x, -y / x**2)),  # 2.13
    ],
)
def test_hydon_2_reduced_to_quadrature(omega, generator):
    """Hydon 2.10, 2.12, 2.13: ds/dr is a function of r alone, X(ds/dr) = 0."""
    _, reduced = _reduced(omega, generator)
    assert _is_zero(VectorField(generator, (x, y))(reduced))


def test_hydon_4_1_riccati():
    """y'' = (3/x - 2x) y' + 4y with y d/dy: r = x, v = y'/y, and the ODE is
    the Riccati equation dv/dr = (3/r - 2r) v + 4 - v**2 (4.9)."""
    f = Function("y")(x)
    r, v, dv = differential_invariants((0, y), f, x, 2)
    on_solutions = dv.subs(diff(f, x, 2), (3 / x - 2 * x) * diff(f, x) + 4 * f)
    assert r == x and simplify(on_solutions - ((3 / r - 2 * r) * v + 4 - v**2)) == 0


def test_hydon_4_2_translation():
    """y'' = y'**2/y + (y - 1/y) y' with d/dx: r = y; Hydon takes v = y'
    (= 1/(ds/dr)) and gets the linear ODE dv/dr = v/r + r - 1/r (4.15)."""
    f = Function("y")(x)
    r, w, dw = differential_invariants((1, 0), f, x, 2)
    v, dv = 1 / w, -dw / w**2
    on_solutions = dv.subs(diff(f, x, 2), diff(f, x) ** 2 / f + (f - 1 / f) * diff(f, x))
    assert r == f and simplify(on_solutions - (v / r + r - 1 / r)) == 0


def test_hydon_5_1_rotations():
    """Rotations: r = x**2 + y**2 (up to a function) and a first order
    invariant functionally dependent on r and Hydon's v = (x y' - y)/(x + y y')."""
    f = Function("y")(x)
    p = Symbol("p")
    r, v = differential_invariants((-y, x), f, x, 1)
    hydon = (x * p - y) / (x + y * p)
    jet = {diff(f, x): p, f: y}
    ours = [e.subs(jet) for e in (r, v)]
    assert ours[0] == x**2 + y**2
    jacobian = Matrix([[e.diff(z) for z in (x, y, p)] for e in [*ours, hydon]])
    assert _is_zero(jacobian.det())


# Bluman and Anco, Symmetry and Integration Methods for Differential
# Equations, sections 2.3, 3.2 and 3.3


def test_bluman_2_56_scaling():
    assert canonical_coordinates((x, 2 * y), (x, y)) == ([y / x**2], sympify("log(x)"))


def test_bluman_2_63_rotations():
    """Polar coordinates (2.68): r = x**2 + y**2, s = asin(y/sqrt(r))."""
    r, s = canonical_coordinates((-y, x), (x, y))
    assert r == [x**2 + y**2]
    assert simplify(s - sympify("asin(y/sqrt(x**2 + y**2))")) == 0


@pytest.mark.parametrize(
    "generator",
    [(1, -y / x), (x, y), (x, -y), (x**2, y**2)],  # Exercises 2.3-2 and 2.3-4
)
def test_bluman_exercises_2_3(generator):
    X = VectorField(generator, (x, y))
    (r,), s = canonical_coordinates(generator, (x, y))
    assert simplify(X(r)) == 0 and _is_zero(X(s) - 1)


def test_bluman_3_2_linear_first_order():
    """y' + p(x) y = g(x): with y d/dy (g = 0) ds/dr = -p(r); with f(x) d/dy,
    f a solution of f' + p f = 0, ds/dr = g(r)/f(r)."""
    p, g, f = (Function(name)(x) for name in "pgf")
    assert _reduced(-p * y, (0, y))[1] == -p
    # p = -f'/f
    _, reduced = _reduced(g + diff(f, x) / f * y, (0, f))
    assert simplify(reduced - g / f) == 0


def test_bluman_3_3_3_scaling():
    """y'' + p y' + q y = 0 with y d/dy: the Riccati equation
    dz/dr + z**2 + p z + q = 0 (3.107)."""
    p, q = (Function(name)(x) for name in "pq")
    f = Function("y")(x)
    r, z, dz = differential_invariants((0, y), f, x, 2)
    on_solutions = dz.subs(diff(f, x, 2), -p * diff(f, x) - q * f)
    assert r == x and simplify(on_solutions + z**2 + p * z + q) == 0


def test_bluman_3_3_3_particular_solution():
    """y'' + p y' + q y = 0 with Q(x) d/dy, Q a solution: s = y/Q and
    Q dz/dr + (2 Q' + p Q) z = 0 for z = ds/dr."""
    p, Q = (Function(name)(x) for name in "pQ")
    q = -(diff(Q, x, 2) + p * diff(Q, x)) / Q
    f = Function("y")(x)
    r, z, dz = differential_invariants((0, Q), f, x, 2)
    on_solutions = dz.subs(diff(f, x, 2), -p * diff(f, x) - q * f)
    assert r == x and simplify(Q * on_solutions + (2 * diff(Q, x) + p * Q) * z) == 0


@pytest.mark.parametrize("generator", [(-x, y), (1, 0)])
def test_bluman_3_3_3_blasius(generator):
    """y''' + y y''/2 = 0 with the scalings and the translations: on its
    solutions the differential invariants up to order 3 are functionally
    dependent (an ODE of order 2 in them), elsewhere they are not."""
    f = Function("y")(x)
    jets = symbols("y0:4")
    found = differential_invariants(generator, f, x, 2)
    third = simplify(found[-1].diff(x) / found[0].diff(x))  # d^3 s/dr^3

    def in_jets(e):
        for k in (3, 2, 1):
            e = e.subs(diff(f, x, k), jets[k])
        return e.subs(f, jets[0])

    blasius = {jets[3]: -jets[0] * jets[2] / 2}
    rows = [in_jets(e) for e in [*found, third]]
    point = {x: Rational(3, 2), jets[0]: 2, jets[1]: Rational(1, 3), jets[2]: 5, jets[3]: 7}
    jacobian = Matrix([[e.diff(z) for z in (x, *jets)] for e in rows])
    assert jacobian.subs(point).rank() == 4
    on_solutions = Matrix([[e.subs(blasius).diff(z) for z in (x, *jets[:3])] for e in rows])
    assert on_solutions.subs(point).rank() == 3
