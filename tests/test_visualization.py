import pytest
from sympy import Function, diff, symbols

# optional dependencies (delierium[plot]): skip without them, as in CI's test group
np = pytest.importorskip("numpy")
matplotlib = pytest.importorskip("matplotlib")
matplotlib.use("Agg")

from delierium import JanetBasis  # noqa: E402
from delierium.infinitesimals import _linear_system_ode  # noqa: E402
from delierium.visualization import (  # noqa: E402
    animate_flow,
    field_functions,
    flow,
    generator_latex,
    ode_solutions,
    rk4,
    staircase,
    vector_fields,
)

x, y, t = symbols("x y t")


def test_generator_latex():
    assert generator_latex(("1", "0"), (x, y)) == r"\partial_{x}"
    assert generator_latex(("-y", "x"), (x, y)) == r"- y\,\partial_{x} + x\,\partial_{y}"
    assert generator_latex(("0", "0"), (x, y)) == "0"


def test_rk4_exponential():
    path = rk4(lambda s: s, np.array([1.0, 2.0]), 1.0, 50)
    assert np.allclose(path[-1], [np.e, 2 * np.e])


def test_flow_of_rotation_and_translation():
    points = np.array([[1.0], [0.0]])
    moved = flow(("-y", "x"), (x, y), points, np.pi / 2)
    assert np.allclose(moved, [[0.0], [1.0]], atol=1e-6)
    assert np.allclose(flow(("1", "0"), (x, y), points, 2.0), [[3.0], [0.0]])


def test_parameters_and_fixed_coordinates():
    # a missing parameter is 1, a coordinate off the axes is fixed
    fx, fy = field_functions(("a*x", "t"), (x, y, t), axes=(0, 1), fixed=2.0, values={"a": 3})
    assert fx(np.array(1.0), np.array(0.0)) == 3.0
    assert fy(np.array(1.0), np.array(0.0)) == 2.0
    fx, _ = field_functions(("a*x", "0"), (x, y))
    assert fx(np.array(5.0), np.array(0.0)) == 5.0


def test_ode_solutions_are_solutions():
    # y'' = 0: straight lines
    Y = Function("y")(x)
    curves = ode_solutions(diff(Y, x, 2), Y, count=3)
    assert len(curves) == 3
    for c in curves:
        c = c[:, ~np.isnan(c).any(axis=0)]
        dx, dy = np.diff(c[0]), np.diff(c[1])
        slopes = dy[dx != 0] / dx[dx != 0]  # the two halves share their start
        assert np.allclose(slopes, slopes[0])


def test_ode_solutions_first_order_without_derivative():
    Y = Function("y")(x)
    assert ode_solutions(Y - x, Y) == []


def test_staircase_counts_the_dimension():
    # Kamke 6.57 with r = 3: dimension 3, i.e. three green (parametric) points
    Y = Function("y")(x)
    ode = diff(Y, x, 2) - (x * diff(Y, x) - Y) ** 3
    system, functions, variables, _ = _linear_system_ode(ode, Y, x)
    janet = JanetBasis(system, functions, variables)
    fig = staircase(janet, names={"H": "y"})
    green = [line for ax in fig.axes for line in ax.lines if line.get_color() == "C2"]
    assert len(green) == 3
    assert "order in y" in fig.axes[0].get_ylabel()
    matplotlib.pyplot.close(fig)


def test_vector_fields_and_animation():
    Y = Function("y")(x)
    curves = ode_solutions(diff(Y, x, 2), Y, count=2)
    fig = vector_fields([("1", "0"), ("x", "y"), ("0", "0")], (x, y), curves)
    assert len(fig.axes) >= 3
    matplotlib.pyplot.close(fig)
    animation = animate_flow(("x", "y"), (x, y), curves, frames=3)
    assert "<script" in animation.to_jshtml()
