"""Invalid arguments of the public functions: clear errors instead of
crashes or silently wrong results."""

import pytest
from sympy import Eq, Function, S, Symbol, diff, symbols

from delierium import (
    JanetBasis,
    determining_janet_basis,
    group_classification,
    lie_symmetries,
    overdetermined_system_ode,
    overdetermined_system_odes,
    overdetermined_system_pde,
    verify_symmetry,
)

x, t = symbols("x t")
y = Function("y")(x)
u = Function("u")(x, t)


@pytest.mark.parametrize(
    ("call", "message"),
    [
        (lambda: determining_janet_basis(diff(y, x, 2), Symbol("y"), x), "write y\\(x\\)"),
        (
            lambda: determining_janet_basis(diff(u, t) - diff(u, x, 2), u, [x]),
            "depends on \\[t\\]",
        ),
        (lambda: determining_janet_basis(y**2 - x, y, x), "contains no derivative"),
        (lambda: determining_janet_basis(S(0), y, x), "an equation is 0"),
        (lambda: overdetermined_system_ode(diff(y, x, 2), [Symbol("y")], [x]), "write y"),
        (lambda: overdetermined_system_pde(diff(u, t) - diff(u, x, 2), [u], [x, x]), "distinct"),
        (lambda: overdetermined_system_pde(diff(u, t), [u], [x, Symbol("s") + 1]), "not a symbol"),
        (lambda: group_classification(diff(u, t), u, [x]), "depends on \\[t\\]"),
        (lambda: lie_symmetries(y**2, y, x), "contains no derivative"),
        (lambda: verify_symmetry(diff(y, x, 2), y, [], (1, 0)), "no independent"),
        (lambda: overdetermined_system_odes([diff(y, x)], [], [x]), "no dependent"),
    ],
)
def test_invalid_arguments(call, message):
    with pytest.raises(ValueError, match=message):
        call()


def test_derivative_with_respect_to_another_variable():
    """u(x, t) with independent [x, t], but a derivative in s."""
    s = Symbol("s")
    w = Function("w")(x, t, s)
    with pytest.raises(ValueError, match="depends on \\[s\\]"):
        determining_janet_basis(diff(w, s) - diff(w, x), w, [x, t])


def test_eq_is_accepted():
    """Eq(a, b) is the equation a - b = 0."""
    blasius = Eq(diff(y, x, 3), -y * diff(y, x, 2))
    assert determining_janet_basis(blasius, y, x).rank() == 2


def test_janet_basis_errors():
    """Nonlinear terms and unknowns not declared."""
    z, w = Function("z")(x), Function("w")(x)
    with pytest.raises(ValueError, match="not linear homogeneous"):
        JanetBasis([z**2], [z], [x])
    with pytest.raises(ValueError, match="not linear homogeneous"):
        JanetBasis([diff(w, x)], [z], [x])
    assert JanetBasis([], [z], [x]).rank() == S.Infinity
