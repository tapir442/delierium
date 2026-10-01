"""Tests for delierium.helpers"""

from sympy import *

from delierium.helpers import is_function, pairs_exclude_diagonal
from delierium.infinitesimals import create_infinitesimals, overdetermined_system_ode


def test_pairs_exclude_diagonal():
    it = range(5)
    for x, y in pairs_exclude_diagonal(it):
        assert x != y


def test_pairs_exclude_diagonal_empty_output():
    it = range(1)
    for _ in pairs_exclude_diagonal(it):
        # shouldn't happen
        assert False


def test_is_function():
    x = Symbol('x')
    f = Function('f')(x)
    assert is_function(f)
    assert not is_function(diff(f, x))
    assert not is_function(x * diff(f, x))
    assert not is_function(x * f)
    g = Function('g')
    assert is_function(g)


def test_derivative_patch_keeps_sympy_behaviour():
    # delierium replaces Derivative.__new__ for the whole process; diff
    # without a variable must still infer it (it used to return x**2)
    import pytest

    import delierium.helpers

    x, y = symbols('x y')
    assert diff(x**2) == 2 * x
    assert diff(sin(x) * x) == x * cos(x) + sin(x)
    assert diff(Integer(3)) == 0
    with pytest.raises(ValueError, match="more than one variable"):
        diff(x * y)
    with pytest.raises(ValueError, match="Can't calculate derivative wrt"):
        Derivative(x, 1 + x)


def test_lie_derivative_printer_notation_and_outputs(capsys):
    from delierium.helpers import lie_derivative_printer, lie_form

    x, t = Symbol('x'), Symbol('t')
    y = Function('y')(x)
    X, Y = Function('X')(x, y), Function('Y')(x, y)
    # an unknown of one variable gets primes, everything else subscripts
    assert str(lie_form(diff(y, x, 3) + y * diff(y, x, 2), [y], [x])) == "y*y'' + y'''"
    assert str(lie_form(diff(y, x, 5), [y], [x])) == "y^(5)"
    assert str(lie_form(Derivative(X, x, y) + Derivative(Y, y, 2), [y], [x])) == "X_xy + Y_yy"
    u = Function('u')(x, t)
    assert str(lie_form(Derivative(u, t, x), [u], [x, t])) == "u_xt"
    assert str(lie_form(Derivative(u, t, x), [u], [t, x])) == "u_tx"
    e = -9 * Derivative(X, x, y) + Derivative(Y, y) / x
    # in a terminal: text
    assert lie_derivative_printer([e], [y], [x]) is None
    assert capsys.readouterr().out == "-9*X_xy + Y_y/x\n"
    assert lie_derivative_printer(e, [y], [x], output="text") == ["-9*X_xy + Y_y/x"]
    assert lie_derivative_printer([e], [y], [x], output="latex") == [
        "- 9 X_{xy} + \\frac{Y_{y}}{x}"
    ]
    assert "Y_y" in lie_derivative_printer([e], [y], [x], output="pretty")[0]
    # the old calling convention with infinitesimals still works
    assert lie_derivative_printer([e], [y], [x], {x: "X", y: "Y"}, output="text") == [
        "-9*X_xy + Y_y/x"
    ]


def test_arbitrary_function_of_an_expression():
    # #36: y' = x F(y/x) + y/x (Kamke 1.610) failed with "Can't calculate
    # derivative wrt y(x)/x": the Subs for F'(y/x) has to stay. With v = y/x
    # it is v' = F(v), so (1, y/x) is a symmetry and (0, 1) is not
    x, Y = Symbol('x'), Symbol('y')
    y, F = Function('y')(x), Function('F')
    infinitesimals = create_infinitesimals([y], [x])
    det = overdetermined_system_ode(
        Derivative(y, x) - (x**2 * F(y / x) + y) / x, [y], [x], infinitesimals=infinitesimals
    )
    X_, Y_ = (infinitesimals[v].xreplace({y: Y}) for v in (x, y))

    def residues(xi, eta):
        solution = {X_.func: Lambda(X_.args, xi), Y_.func: Lambda(Y_.args, eta)}
        return [simplify(e.xreplace({y: Y}).subs(solution).doit()) for e in det]

    assert all(r == 0 for r in residues(1, Y / x))
    assert any(r != 0 for r in residues(0, 1))


def test_version():
    # the version is written only in pyproject.toml; the package reads it
    # from its metadata
    import tomllib
    from pathlib import Path

    import delierium

    pyproject = tomllib.loads((Path(__file__).parents[1] / "pyproject.toml").read_text())
    assert delierium.__version__ == pyproject["project"]["version"]
