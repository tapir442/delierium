"""Convenience functions"""

import builtins
import itertools
import os
from collections.abc import Callable
from typing import Any, cast

import sympy as sp
from sympy import (
    Basic,
    Derivative,
    Function,
    Subs,
    Symbol,
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
    if os.environ.get('JANET_PROFILE', 'false').lower() == 'true':
        from line_profiler import profile

        return cast(F, profile(func))
    return func


@profile_if_enabled
def eq(d1, d2):
    if d1.__class__ != d2.__class__:
        return False
    return d1 == d2


@profile_if_enabled
def pairs_exclude_diagonal(it):
    for x, y in itertools.product(it, repeat=2):
        if x != y:
            yield (x, y)


@profile_if_enabled
def is_derivative(e):
    """checks whether an expression 'e' is a pure derivative
    >>> from sympy import diff
    >>> x = Symbol('x')
    >>> f = Function('f')(x)
    >>> is_derivative(f)
    False
    >>> is_derivative(diff(f, x))
    True
    >>> is_derivative(diff(f, x) * x)
    False
    """
    return e.is_Derivative


@profile_if_enabled
def is_function(e):
    """checks whether an expression 'e' is a pure function without any
    derivative as a factor
    """
    return e.is_Function


@profile_if_enabled
def func_diff(fun: Function, var: Symbol | Function) -> Derivative:
    # simplify=False: SymPy's factor_terms(signsimp(...)) after every higher
    # derivative costs time and is of no use here
    if var.is_Function or var.is_Derivative:
        d = Symbol('d')
        r = fun.xreplace({var: d}).diff(d, simplify=False).xreplace({d: var})
        r = r.doit(simplify=False)
    else:
        r = Derivative(fun, var).doit(simplify=False)
    return r


@profile_if_enabled
def finish_substitution(expr):
    subs = set(expr.atoms(Subs))
    subs_dic = {}
    for s0 in subs:
        bound = s0.bound_symbols
        der = s0.args[0]
        var = s0.args[2]
        subs_dic[s0] = der.xreplace(dict(zip(bound, var, strict=True)))
    return expr.xreplace(subs_dic)


def ltf(expr, dep, indep, infinitesimals=None, printer=True):  # pylint: disable=unused-argument
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


def show_output(obj):
    """Rich display in IPython/Jupyter, print everywhere else."""
    if _in_ipython_session:
        from IPython.display import display

        display(obj)
    else:
        print(obj)


@profile_if_enabled
def make_infinitesimal(v, *variables, name=""):
    """
    >>> x = Symbol('x')
    >>> f = Function('f')(x)
    >>> i = make_infinitesimal(f, f, x, name="phi")
    >>> i
    phi(f(x), x)
    """
    return Function(f'{name if name else v.name.swapcase()}')(*variables)  # pylint: disable=not-callable


def is_jupyter_lab() -> bool:
    """True inside a Jupyter kernel (JupyterLab, Notebook, VS Code), where
    formulas can be displayed; False in a terminal, also in IPython there."""
    try:
        from IPython import get_ipython
    except ImportError:
        return False
    shell = get_ipython()
    return shell is not None and type(shell).__name__ == "ZMQInteractiveShell"


def _function_name(f):
    """y for y(x) or the symbol y: the name of a function or symbol."""
    if isinstance(f, AppliedUndef):
        return f.func.__name__
    return str(f)


def lie_form(expr, dependent_vars=(), independent_vars=()):
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

    def position(name):
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
    return expr.xreplace({f: Symbol(f.func.__name__) for f in expr.atoms(AppliedUndef)})


def lie_derivative_printer(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    expressions,
    dependent_vars=(),
    independent_vars=(),
    infinitesimals=None,
    *args,
    output=None,
    **kwargs,
):
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


# ToDo (from AllTypes.de
# CommutatorTable
# DterminingSystem
# Free Resolution
# Gcd
# Groebner Basis
# In?
# Intersection
# JanetBasis
# Lcm
# LöwDecomposioipn
# Primary Decomposition
# Product
# Qutiont
# Radical
# Random
# Saturation
# Sum
# Symmetric Power
# # Syzygys
