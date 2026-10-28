"""Convenience functions"""

import builtins
import os
import random
from collections.abc import Callable, Iterable, Sequence
from typing import Any, cast

import sympy as sp
from sympy import (
    Basic,
    Derivative,
    Expr,
    Function,
    Piecewise,
    Subs,
    Symbol,
    cancel,
    default_sort_key,
    ilcm,
    sympify,
)
from sympy.core.function import AppliedUndef

__all__ = [
    "lie_derivative_printer",
    "lie_form",
    "ltf",
    "make_infinitesimal",
]

_in_ipython_session = hasattr(builtins, "__IPYTHON__")


# fast solution für Profiling:
def profile_if_enabled[F: Callable[..., Any]](func: F) -> F:
    """func, wrapped by line_profiler's profile if JANET_PROFILE=true.

    >>> def f():
    ...     return 1
    >>> profile_if_enabled(f) is f  # JANET_PROFILE not set
    True
    """
    if os.environ.get('JANET_PROFILE', 'false').lower() == 'true':
        from line_profiler import profile

        return cast(F, profile(func))
    return func


@profile_if_enabled
def func_diff(fun: Expr, var: Symbol | Function) -> Expr:
    # simplify=False: SymPy's factor_terms(signsimp(...)) after every higher
    # derivative costs time and is of no use here
    """d fun / d var, var also a function or a derivative (a jet coordinate).

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> func_diff(y.diff(x) ** 2 + x * y, y.diff(x))
    2*Derivative(y(x), x)
    >>> func_diff(x**2 * y, x)
    x**2*Derivative(y(x), x) + 2*x*y(x)
    """
    if var.is_Function or var.is_Derivative:
        d = Symbol('d')
        r = fun.xreplace({var: d}).diff(d, simplify=False).xreplace({d: var})
        r = r.doit(simplify=False)
    else:
        r = Derivative(fun, var).doit(simplify=False)
    return r


@profile_if_enabled
def finish_substitution(expr: Basic) -> Basic:
    """Put the points of the Subs in expr back in: Subs(Derivative(X(xi), xi),
    xi, y(x)) becomes Derivative(X(y(x)), y(x)). A Subs whose point is an
    expression, e.g. the derivative of F(y/x), stays: SymPy cannot build a
    derivative with respect to y/x, and differentiates the Subs correctly
    (#36).

    >>> x, xi = Symbol('x'), Symbol('xi')
    >>> y, F = Function('y')(x), Function('F')
    >>> finish_substitution(Subs(Derivative(F(xi), xi), xi, y))
    Derivative(F(y(x)), y(x))
    >>> finish_substitution(Subs(Derivative(F(xi), xi), xi, y / x))
    Subs(Derivative(F(xi), xi), xi, y(x)/x)
    """
    subs = set(expr.atoms(Subs))
    subs_dic = {}
    for s0 in subs:
        bound = s0.bound_symbols
        der = s0.args[0]
        var = s0.args[2]
        if all(v.is_Symbol or isinstance(v, AppliedUndef) for v in var):
            subs_dic[s0] = der.xreplace(dict(zip(bound, var, strict=True)))
    return expr.xreplace(subs_dic)


def ltf(  # pylint: disable=unused-argument
    expr: Basic,
    dep: Sequence[Basic],
    indep: Sequence[Basic],
    infinitesimals: object = None,
    printer: bool = True,
) -> Basic:
    """Lie Traditional Form: expr in the notation of Lie, see lie_form.

    Shows the result (as a formula in Jupyter, as text elsewhere) unless
    printer is False, and returns it. infinitesimals is accepted for
    compatibility and not needed.

    >>> from sympy import diff
    >>> x = Symbol("x")
    >>> y = Function("y")(x)
    >>> print(ltf(diff(y, x, 3) + y * diff(y, x, 2), [y], [x], printer=False))
    y*y'' + y'''
    """
    output = lie_form(expr, dep, indep)
    if printer:
        show_output(output)
    return output


def show_output(obj: object) -> None:
    """Rich display in IPython/Jupyter, print everywhere else.

    >>> show_output("Janet basis")
    Janet basis
    """
    if _in_ipython_session:
        from IPython.display import display

        display(obj)
    else:
        print(obj)


@profile_if_enabled
def make_infinitesimal(v: Basic, *variables: Basic, name: str = "") -> Expr:
    """
    >>> x = Symbol('x')
    >>> f = Function('f')(x)
    >>> i = make_infinitesimal(f, f, x, name="phi")
    >>> i
    phi(f(x), x)
    """
    return Function(f'{name or v.name.swapcase()}')(*variables)  # pylint: disable=not-callable


def is_jupyter_lab() -> bool:
    """True inside a Jupyter kernel (JupyterLab, Notebook, VS Code), where
    formulas can be displayed; False in a terminal, also in IPython there.

    >>> is_jupyter_lab()
    False
    """
    try:
        from IPython import get_ipython
    except ImportError:
        return False
    shell = get_ipython()
    return shell is not None and type(shell).__name__ == "ZMQInteractiveShell"


def plain_symbol(f: Basic) -> Symbol:
    """The plain symbol for the dependent variable f: u for u(x, t).

    >>> from sympy import Function, symbols
    >>> x, t = symbols("x t")
    >>> plain_symbol(Function("u")(x, t))
    u
    """
    return Symbol(f.func.__name__)


def generic_case(e: Expr) -> Expr:
    """e with every Piecewise replaced by its first case: generic values of
    the parameters (a != 0 for dsolve's and integrate's case splits).

    >>> from sympy import Ne, Piecewise, symbols
    >>> x, a = symbols("x a")
    >>> generic_case(Piecewise((x / a, Ne(a, 0)), (x, True)) + 1)
    1 + x/a
    """
    return e.replace(lambda a: isinstance(a, Piecewise), lambda a: a.args[0].expr)


def commensurable_families(
    parts: Iterable[tuple[Basic, Basic, Expr]],
) -> list[tuple[Basic, Expr, list[tuple[Basic, Expr]]]]:
    """The items (atom, key, part) grouped by equal keys and parts that are
    rational multiples of one another (b**n, b**(n/2), b**(-n): key b, parts
    n, n/2, -n). Per family its key, a unit u with every part an integer
    multiple k u, and the atoms with their k.

    >>> from sympy import symbols
    >>> b, n = symbols("b n")
    >>> commensurable_families([(b**n, b, n), (b ** (n / 2), b, n / 2), (b**-n, b, -n)])
    [(b, -n/2, [(b**(-n), 2), (b**(n/2), -1), (b**n, -2)])]
    """
    families: list[tuple[Basic, Expr, list[tuple[Basic, Expr]]]] = []
    for atom, key, part in sorted(parts, key=lambda p: default_sort_key(p[0])):
        for k, reference, members in families:
            if k == key and cancel(part / reference).is_Rational:
                members.append((atom, part))
                break
        else:
            families.append((key, part, [(atom, part)]))
    result = []
    for key, reference, members in families:
        ratios = [cancel(part / reference) for _, part in members]
        unit = reference / ilcm(1, 1, *[r.q for r in ratios])
        result.append((key, unit, [(atom, cancel(part / unit)) for atom, part in members]))
    return result


def random_point(symbols: Iterable[Basic], rng: random.Random) -> dict[Basic, Expr]:
    """Random positive values (1.1 to 9.7) for the symbols.

    >>> from sympy import symbols
    >>> x, t = symbols("x t")
    >>> random_point([x, t], random.Random(0))
    {x: 6, t: 32/5}
    """
    return {s: sympify(rng.randint(11, 97)) / 10 for s in symbols}


def numeric_value(e: Expr, point: dict[Basic, Expr]) -> complex | None:
    """The value of e at the point, None if it is not numeric there (an
    arbitrary function, its derivative: a number replaces the variable of
    differentiation, which SymPy rejects with a ValueError).

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> f = Function("f")(x)
    >>> numeric_value(x**2, {x: 3}), numeric_value(f, {x: 3}), numeric_value(f.diff(x), {x: 3})
    ((9+0j), None, None)
    """
    try:
        return complex(e.xreplace(point).evalf(30))
    except (TypeError, ValueError):
        return None


def _function_name(f: Basic) -> str:
    """y for y(x) or the symbol y: the name of a function or symbol.

    >>> from sympy import Function, symbols
    >>> x, y = symbols("x y")
    >>> _function_name(Function("u")(x)), _function_name(y)
    ('u', 'y')
    """
    if isinstance(f, AppliedUndef):
        return f.func.__name__
    return str(f)


def lie_form(
    expr: Basic | str,
    dependent_vars: Iterable[Basic] = (),
    independent_vars: Iterable[Basic] = (),
) -> Basic:
    """expr in the notation of Lie: derivatives as subscripts, arguments of
    functions omitted.

    Returns an expression in which every derivative and every undefined
    function is a symbol, so that any SymPy printer can print it (str,
    pretty, latex). A dependent variable of a single independent variable,
    y(x), gets primes (y', y'', y''', then y^(4), ...); every other function
    (a dependent variable of several variables, an infinitesimal, a
    coefficient) gets its variables as subscript: u_xy, X_xy. The subscript
    lists the variables in the order of independent_vars, then of
    dependent_vars, then alphabetically. A variable that is a function, as
    y(x) in X(x, y(x)), is written by its name.

    >>> from sympy import diff, sin
    >>> x, t = Symbol("x"), Symbol("t")
    >>> y = Function("y")(x)
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> lie_form(y.diff(x, 3) + y * y.diff(x, 2), [y], [x])
    y*y'' + y'''
    >>> # partial derivatives: X.diff(x, y) would be total, with a term in y'
    >>> lie_form(Derivative(X, x, y) - 3 * Y.diff(y, 2) + y * X.diff(y), [y], [x])
    X_xy + X_y*y - 3*Y_yy
    >>> u = Function("u")(x, t)
    >>> lie_form(u.diff(t) - u.diff(x, 2) + sin(u) * u.diff(x, t), [u], [x, t])
    u_t + u_xt*sin(u) - u_xx
    """
    expr = finish_substitution(sympify(expr))
    dependent_vars = list(dependent_vars)
    order = [_function_name(v) for v in (*independent_vars, *dependent_vars)]

    def position(name: str) -> tuple[int, str]:
        return (order.index(name), "") if name in order else (len(order), name)

    replacements = {}
    for d in expr.atoms(Derivative):
        f = d.expr
        name = _function_name(f)
        if f in dependent_vars and len(f.args) == 1:
            n = sum(k for _, k in d.variable_count)
            replacements[d] = Symbol(name + "'" * n if n <= 3 else f"{name}^({n})")
        else:
            subscript = sorted(
                (_function_name(v) for v, k in d.variable_count for _ in range(k)), key=position
            )
            replacements[d] = Symbol(f"{name}_{''.join(subscript)}")
    expr = expr.xreplace(replacements)
    return expr.xreplace({f: plain_symbol(f) for f in expr.atoms(AppliedUndef)})


def lie_derivative_printer(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    expressions: Basic | Iterable[Basic],
    dependent_vars: Iterable[Basic] = (),
    independent_vars: Iterable[Basic] = (),
    infinitesimals: object = None,
    *args: object,
    output: str | None = None,
    **kwargs: object,
) -> list[str] | None:
    """Print expressions in the notation of Lie, see lie_form.

    output=None prints: in a Jupyter notebook as formulas, in a terminal as
    text. output="text" (one line each, as str), "pretty" (unicode, two
    dimensional) or "latex" returns the strings instead of printing them.
    infinitesimals is accepted for compatibility and not needed: every
    function that is no dependent variable of a single variable is written
    with subscripts.

    >>> x = Symbol("x")
    >>> y = Function("y")(x)
    >>> X, Y = Function("X")(x, y), Function("Y")(x, y)
    >>> e = y * X.diff(y) - 9 * Derivative(X, x, y) + Y.diff(y, 2) / 3 + y.diff(x, 2)
    >>> lie_derivative_printer([e], [y], [x])
    -9*X_xy + X_y*y + Y_yy/3 + y''
    >>> for s in lie_derivative_printer([e], [y], [x], output="latex"):
    ...     print(s)
    - 9 X_{xy} + X_{y} y + \\frac{Y_{yy}}{3} + y''
    >>> print(lie_derivative_printer([Y.diff(y) / x], [y], [x], output="pretty")[0])
    Y_y
    ───
     x
    """
    if isinstance(expressions, Basic):
        expressions = [expressions]
    forms = [lie_form(e, dependent_vars, independent_vars) for e in expressions]
    if output == "text":
        return [str(e) for e in forms]
    if output == "pretty":
        return [sp.pretty(e, use_unicode=True) for e in forms]
    if output == "latex":
        return [sp.latex(e) for e in forms]
    if output is not None:
        raise ValueError(f"output={output!r}, expected None, 'text', 'pretty' or 'latex'")
    if is_jupyter_lab():
        from IPython.display import Math, display

        for e in forms:
            display(Math(sp.latex(e)))
    else:
        for e in forms:
            print(e)
    return None
