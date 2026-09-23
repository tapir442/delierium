import pytest
from sympy import Function, Integer, simplify

from delierium.higher_infinitesimals import JETS, determining_equations, main, t, u, x

X, T, U = (Function(name)(x, t, u) for name in "XTU")
u_x, u_t, u_xx, u_xxx = JETS[("x",)], JETS[("t",)], JETS[("x", "x")], JETS[("x", "x", "x")]


def satisfies(equations, xi, tau, eta):
    reps = {X: xi, T: tau, U: eta}
    return all(simplify(eq.subs(reps).doit()) == 0 for eq in equations)


HEAT = [
    (1, 0, 0),  # x translation
    (0, 1, 0),  # t translation
    (0, 0, u),  # scaling of u
    (x, 2 * t, 0),  # scaling
    (2 * t, 0, -x * u),  # Galilean boost
    (4 * x * t, 4 * t**2, -(x**2 + 2 * t) * u),  # projective
]

KDV = [
    (1, 0, 0),
    (0, 1, 0),
    (t, 0, 1),  # Galilean boost
    (x, 3 * t, -2 * u),  # scaling
]

DEFAULT = [(1, 0, 0), (0, 1, 0), (x, 2 * t, 0)]


@pytest.mark.parametrize(
    ("lhs", "rhs", "symmetries"),
    [(u_t, u_xx, HEAT), (u_t, -u * u_x - u_xxx, KDV), (u_xxx, u_t * u * u_x, DEFAULT)],
    ids=["heat", "kdv", "u_xxx=u*u_t*u_x"],
)
def test_known_symmetries(lhs, rhs, symmetries):
    equations = determining_equations(lhs, rhs)
    for symmetry in symmetries:
        assert satisfies(equations, *(Integer(0) + s for s in symmetry)), symmetry


def test_rejects_non_symmetry():
    equations = determining_equations(u_t, u_xx)
    assert not satisfies(equations, x**2, Integer(0), Integer(0))


def test_lhs_on_rhs():
    with pytest.raises(ValueError, match="must not appear"):
        determining_equations(u_t, u_t * u)


def test_cli(capsys):
    main(["u_t", "u_xx"])
    out = capsys.readouterr().out
    assert out.startswith("determining equations of u_t = u_xx:")
    assert out.count("= 0") == 9
