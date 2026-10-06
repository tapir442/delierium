"""Pictures of Lie point symmetries and Janet bases.

Needs matplotlib (``pip install delierium[plot]``); ``import delierium`` does
not import this module, so delierium itself works without it.

* staircase: the leading and parametric derivatives of a Janet basis
* vector_fields, draw_field: generators as vector fields, with solution curves
* ode_solutions: solution curves of a scalar ODE, integrated numerically
* animate_flow, flow: the one-parameter group of a generator moving curves
* generator_latex, rk4, field_functions: the building blocks

A generator is a tuple of components (strings or SymPy expressions), one per
coordinate: the independent variables followed by the dependent ones, as
plain symbols, e.g. ``("x", "-y")`` with coordinates ``(x, y)`` is
x d/dx - y d/dy. Parameters get their numbers from ``values`` (a dict, keys
names or symbols); a parameter that is not in it is 1.
"""

from collections.abc import Callable, Iterable, Mapping, Sequence
from typing import TYPE_CHECKING, Any

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.animation import FuncAnimation
from matplotlib.axes import Axes
from matplotlib.colors import Normalize
from matplotlib.figure import Figure
from sympy import Basic, Derivative, Expr, Symbol, lambdify, latex, oo, solve, sympify

if TYPE_CHECKING:
    from delierium.janet_basis import JanetBasis

__all__ = [
    "animate_flow",
    "draw_field",
    "field_functions",
    "flow",
    "generator_latex",
    "ode_solutions",
    "rk4",
    "staircase",
    "vector_fields",
]

BOX = (-3, 3, -3, 3)

# a vector field: one component (a string or an expression) per coordinate
Generator = Sequence[str | Expr]
# numbers for the parameters, keyed by name or symbol
Values = Mapping[str | Basic, Any] | None
Box = tuple[float, float, float, float]
Axes2 = tuple[int, int]
FieldFunction = Callable[[np.ndarray, np.ndarray], np.ndarray]


def generator_latex(generator: Generator, coordinates: Sequence[Basic]) -> str:
    """The vector field sum c_i d/dv_i in LaTeX.

    >>> from sympy import symbols
    >>> x, y = symbols("x y")
    >>> generator_latex(("1", "0"), (x, y))
    '\\\\partial_{x}'
    >>> generator_latex(("x*y", "-y**2 - x"), (x, y))
    'x y\\\\,\\\\partial_{x} - \\\\left(x + y^{2}\\\\right)\\\\partial_{y}'
    """
    terms = []
    for c, v in zip(generator, coordinates, strict=True):
        c = sympify(c)
        if c == 0:
            continue
        sign, c = ("-", -c) if c.could_extract_minus_sign() else ("+", c)
        if c == 1:
            factor = ""
        elif c.is_Add:
            factor = rf"\left({latex(c)}\right)"
        else:
            factor = latex(c) + r"\,"
        terms.append(f"{sign} {factor}\\partial_{{{latex(v)}}}")
    text = " ".join(terms)
    return (text[2:] if text.startswith("+ ") else text) or "0"


def rk4(
    f: Callable[[np.ndarray], np.ndarray], state: np.ndarray, t_end: float, steps: int = 400
) -> np.ndarray:
    """Integrate state' = f(state) from 0 to t_end with the classical
    Runge-Kutta method; state may have columns (several solutions at once).
    Returns the states at all steps.

    >>> float(rk4(lambda s: s, np.array([1.0]), 1.0, 20)[-1][0])  # e
    2.71828...
    """
    h = t_end / steps
    path = [state]
    for _ in range(steps):
        k1 = f(state)
        k2 = f(state + h / 2 * k1)
        k3 = f(state + h / 2 * k2)
        k4 = f(state + h * k3)
        state = state + h / 6 * (k1 + 2 * k2 + 2 * k3 + k4)
        path.append(state)
    return np.array(path)


def _numbers(expr: Expr | str, keep: Iterable[Basic], values: Values) -> Expr:
    """expr with the values substituted and every other symbol not in keep 1."""
    e = sympify(expr).subs({sympify(k): sympify(v) for k, v in (values or {}).items()})
    return e.subs(dict.fromkeys(e.free_symbols - set(keep), 1))


def field_functions(
    generator: Generator,
    coordinates: Sequence[Basic],
    axes: Axes2 = (0, 1),
    fixed: float = 1.0,
    values: Values = None,
) -> list[FieldFunction]:
    """The components of the generator along the coordinates axes, as numpy
    functions of these two coordinates; the other coordinates are fixed."""
    a, b = (coordinates[i] for i in axes)
    rest = {c: fixed for i, c in enumerate(coordinates) if i not in axes}

    def component(i: int) -> FieldFunction:
        f = lambdify((a, b), _numbers(sympify(generator[i]).subs(rest), (a, b), values), "numpy")
        return lambda X, Y: np.broadcast_to(f(X, Y), np.shape(X)).astype(float)

    return [component(i) for i in axes]


def draw_field(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    ax: Axes,
    generator: Generator,
    coordinates: Sequence[Basic],
    box: Box = BOX,
    axes: Axes2 = (0, 1),
    fixed: float = 1.0,
    values: Values = None,
    n: int = 40,
    title: str | None = None,
) -> None:
    """Draw the generator, projected onto the coordinates axes, as streamlines
    colored by its length."""
    fx, fy = field_functions(generator, coordinates, axes, fixed, values)
    X, Y = np.meshgrid(np.linspace(box[0], box[1], n), np.linspace(box[2], box[3], n))
    with np.errstate(all="ignore"):
        U, V = np.nan_to_num(fx(X, Y)), np.nan_to_num(fy(X, Y))
    shade = np.log1p(np.hypot(U, V))
    if shade.max() > 0:
        # the scale starts below 0, so that a field of constant length is not white
        ax.streamplot(
            X, Y, U, V, color=shade, cmap="Blues",
            norm=Normalize(-0.3 * shade.max(), shade.max()),
            density=1.1, linewidth=0.8, arrowsize=0.8,
        )  # fmt: skip
    else:
        ax.text(0.5, 0.5, "zero in this projection", transform=ax.transAxes,
                ha="center", va="center", color="0.4")  # fmt: skip
    ax.set_xlim(box[:2])
    ax.set_ylim(box[2:])
    ax.set_xlabel(str(coordinates[axes[0]]))
    ax.set_ylabel(str(coordinates[axes[1]]))
    if title is None:
        title = "$" + generator_latex(generator, coordinates) + "$"
    ax.set_title(title, fontsize=9)


def flow(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    generator: Generator,
    coordinates: Sequence[Basic],
    points: np.ndarray,
    eps: float,
    axes: Axes2 = (0, 1),
    fixed: float = 1.0,
    values: Values = None,
    steps: int = 60,
) -> np.ndarray:
    """The points (2 x N, in the coordinates axes) moved by eps along the flow
    of the generator, computed numerically from its vector field."""
    if eps == 0:
        return points
    fx, fy = field_functions(generator, coordinates, axes, fixed, values)
    with np.errstate(all="ignore"):
        return rk4(lambda s: np.array([fx(s[0], s[1]), fy(s[0], s[1])]), points, eps, steps)[-1]


def ode_solutions(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    ode: Expr,
    y: Expr,
    box: Box = BOX,
    count: int = 8,
    values: Values = None,
    seed: int = 1,
    steps: int = 300,
) -> list[np.ndarray]:
    """Solution curves (2 x N arrays of x and y) of the scalar ODE ode = 0 for
    y = y(x), through random points of the box, with random values of the
    higher derivatives there; [] if it cannot be solved for its highest
    derivative."""
    x = y.args[0]
    n = max((len(d.variables) for d in ode.atoms(Derivative) if d.expr == y), default=0)
    if n == 0:
        return []
    jets = [Symbol(f"_p{i}") for i in range(n + 1)]
    flat = ode.subs({Derivative(y, (x, i)): jets[i] for i in range(n, 0, -1)}).subs(y, jets[0])
    flat = _numbers(flat, (x, *jets), values)
    roots = [r for r in solve(flat, jets[n]) if r.is_real is not False]
    if not roots:
        return []
    F = lambdify((x, *jets[:n]), roots[0], "numpy")

    def f(s: np.ndarray) -> np.ndarray:
        return np.array([np.ones_like(s[0]), *s[2:], F(*s)])

    rng = np.random.default_rng(seed)
    curves = []
    for _ in range(count):
        x0, y0 = rng.uniform(*box[:2]), rng.uniform(*box[2:])
        start = np.array([x0, y0, *rng.uniform(-1, 1, n - 1)])
        parts = []
        for length in (box[1] - x0, box[0] - x0):
            with np.errstate(all="ignore"):
                path = rk4(f, start, length, steps)[:, :2]
            path[~np.isfinite(path).all(axis=1)] = np.nan
            path[np.abs(path[:, 1]) > 10 * max(map(abs, box))] = np.nan
            parts.append(path)
        curves.append(np.concatenate([parts[1][::-1], parts[0]]).T)
    return curves


def vector_fields(
    generators: Sequence[Generator],
    coordinates: Sequence[Basic],
    curves: Iterable[np.ndarray] = (),
    box: Box = BOX,
    axes: Axes2 = (0, 1),
    fixed: float = 1.0,
    values: Values = None,
    columns: int = 4,
) -> Figure:
    """A figure with one panel per generator, with the curves (red) on top."""
    columns = min(len(generators), columns)
    rows = -(-len(generators) // columns)
    fig, panels = plt.subplots(rows, columns, squeeze=False, figsize=(4 * columns, 3.8 * rows))
    for ax, g in zip(panels.flat, generators, strict=False):
        draw_field(ax, g, coordinates, box, axes, fixed, values)
        for c in curves:
            ax.plot(c[0], c[1], color="C3", lw=1, alpha=0.8)
    for ax in panels.flat[len(generators) :]:
        ax.axis("off")
    fig.tight_layout()
    return fig


def animate_flow(  # pylint: disable=too-many-arguments,too-many-positional-arguments
    generator: Generator,
    coordinates: Sequence[Basic],
    curves: Sequence[np.ndarray],
    box: Box = BOX,
    axes: Axes2 = (0, 1),
    fixed: float = 1.0,
    values: Values = None,
    eps: float = 0.5,
    frames: int = 21,
) -> FuncAnimation:
    """An animation of the curves moved by the flow of the generator, for
    eps from -eps to eps; show it in Jupyter with
    HTML(animation.to_jshtml())."""
    fig, ax = plt.subplots(figsize=(5, 5), dpi=60)
    draw_field(ax, generator, coordinates, box, axes, fixed, values, n=30)
    drawn = [ax.plot([], [], color="C3", lw=2)[0] for _ in curves]
    label = ax.text(0.02, 0.96, "", transform=ax.transAxes, fontsize=11,
                    bbox={"facecolor": "white", "alpha": 0.8, "lw": 0})  # fmt: skip

    def frame(e: float) -> list[Any]:
        for line, c in zip(drawn, curves, strict=True):
            p = flow(generator, coordinates, c, e, axes, fixed, values)
            line.set_data(*np.where(np.abs(p) > 50, np.nan, p))
        label.set_text(f"ε = {e:+.2f}")
        return drawn

    animation = FuncAnimation(
        fig, frame, frames=np.linspace(-eps, eps, frames), interval=150, blit=True
    )
    plt.close(fig)
    return animation


def _orders(
    janet: "JanetBasis", derivatives: Iterable[Basic]
) -> set[tuple[Basic, tuple[int, ...]]]:
    """The derivatives as (function, orders by the context's variables)."""
    context = janet.context
    return {
        (d.expr, tuple(context.order_of_derivative(d)))
        if isinstance(d, Derivative)
        else (d, (0,) * len(context.independent))
        for d in derivatives
    }


def staircase(
    janet: "JanetBasis", names: Mapping[Any, Any] | None = None, title: str = ""
) -> Figure:
    """The staircase of a Janet basis: for each unknown function a grid of
    its derivatives, (i, j) meaning i times by the first and j times by the
    second variable. Red squares are the leading derivatives, grey points
    their derivatives, green points the parametric derivatives, whose number
    is the dimension of the solution space. With more than two variables,
    one row per order 0, 1, 2 in the third variable (0 in the others).

    names renames variables in the labels, e.g. {"H": "y"}.
    """
    names = {str(k): str(v) for k, v in (names or {}).items()}
    variables = [names.get(str(v), str(v)) for v in janet.context.independent]
    unknowns = list(janet.context.dependent)
    leading = _orders(janet, janet.type().leaders)
    top = max([sum(o) for _, o in leading] + [1]) + 2
    slices = [0] if len(variables) == 2 else [0, 1, 2]
    rest = len(variables) - 3
    # the largest total order a grid point has
    highest = 2 * top + (max(slices) if rest >= 0 else 0)
    principal = _orders(janet, janet.principal_derivatives(highest))
    # never None: max_order is given
    parametric = _orders(janet, janet.parametric_derivatives(highest) or [])

    fig, panels = plt.subplots(
        len(slices), len(unknowns), squeeze=False,
        figsize=(3.2 * len(unknowns), 3.2 * len(slices)),
    )  # fmt: skip
    for col, f in enumerate(unknowns):
        for row, k in enumerate(slices):
            ax = panels[row][col]
            for i in range(top + 1):
                for j in range(top + 1):
                    point = (f, (i, j) + (((k,) + (0,) * rest) if rest >= 0 else ()))
                    if point in leading:
                        ax.plot(i, j, "s", color="C3", ms=11)
                    elif point in principal:
                        ax.plot(i, j, "o", color="0.75", ms=6)
                    elif point in parametric:
                        ax.plot(i, j, "o", color="C2", ms=8)
            ax.set_xticks(range(top + 1))
            ax.set_yticks(range(top + 1))
            ax.set_xlabel(f"order in {variables[0]}")
            ax.set_ylabel(f"order in {variables[1]}")
            name = str(f.func)
            if rest >= 0:
                name += f", order {k} in {variables[2]}"
            ax.set_title(name, fontsize=10)
            ax.set_aspect("equal")
    dimension = janet.type().dimension
    fig.suptitle(f"{title}{': ' if title else ''}dimension {'∞' if dimension == oo else dimension}")
    fig.tight_layout()
    return fig
