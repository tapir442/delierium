"""Convenience functions"""

import builtins
import functools
import itertools
import os
from collections.abc import Iterable

import sympy as sp
from sympy import (
    Basic,
    Derivative,
    Dummy,
    Function,
    S,
    Subs,
    Symbol,
    Tuple,
    sympify,
)
from sympy.core.expr import Expr
from sympy.core.function import AppliedUndef, UndefinedFunction, _derivative_dispatch
from sympy.core.numbers import Integer
from sympy.utilities.misc import filldedent

__all__ = [
    "lie_derivative_printer",
    "lie_form",
    "ltf",
    "make_infinitesimal",
]

_in_ipython_session = hasattr(builtins, "__IPYTHON__")


# fast solution für Profiling:
def profile_if_enabled(func):
    if os.environ.get('JANET_PROFILE', 'false').lower() == 'true':
        from line_profiler import profile

        return profile(func)
    return func


@profile_if_enabled
@functools.lru_cache(maxsize=2**16)  # bounded: it sees every derivative
def is_zero(obj):
    return obj is not None and obj.is_zero


@profile_if_enabled
def _derivative_new(cls, expr, *variables, **kwargs):  # noqa: C901
    """Tweak from original sympy.core.function.Derivatice.__new__

    We removed some unnecessary steps to gain a lot of run time improvement.
    We (hopefully) don't need these checks as we use it only internally.

    Fun fact: the most time consuming step is 'expr.free_symbols', which needs
    80-90 % of the *whole* janet basis algorithm. If anyone has any idea hoe to get around
    it, you're welcome!

    PS:
    I cached the property 'Basic.free_symbols' (see obove), with a huge time gain.
    Now 80-90% of the whole runtime is in the line 'if obj is not None and not obj.is_zero'
    I factored it out into a cached function 'is_zero', with very little gain(5-10%)
    """
    expr = sympify(expr)
    if not isinstance(expr, Basic):
        raise TypeError(f"Cannot represent derivative of {type(expr)}")

    #    Removed from original sympy.core.function.Derivative.__new__
    #    because this 'free_symbol' access eats all CPU, and we don't need it
    #    here, as we use it only internally
    #    symbols_or_none = getattr(expr, "free_symbols", None)
    #    has_symbol_set = isinstance(symbols_or_none, set)
    #
    #    if not has_symbol_set:
    #        raise ValueError(filldedent('''
    #            Since there are no variables in the expression %s,
    #            it cannot be differentiated.''' % expr))

    # determine value for variables if it wasn't given. This patch replaces
    # Derivative.__new__ for everyone in the process, so this has to stay:
    # without it diff(x**2) returned x**2. It costs nothing internally,
    # where the variables are always given.
    if not variables:
        variables = expr.free_symbols
        if len(variables) != 1:
            if expr.is_number:
                return S.Zero
            if len(variables) == 0:
                raise ValueError(
                    filldedent(
                        f'''
                    Since there are no variables in the expression,
                    the variable(s) of differentiation must be supplied
                    to differentiate {expr}'''
                    )
                )
            raise ValueError(
                filldedent(
                    f'''
                Since there is more than one variable in the
                expression, the variable(s) of differentiation
                must be supplied to differentiate {expr}'''
                )
            )

    # Split the list of variables into a list of the variables we are diff
    # wrt, where each element of the list has the form (s, count) where
    # s is the entity to diff wrt and count is the order of the
    # derivative.
    variable_count = []
    array_likes = (tuple, list, Tuple)

    from sympy.tensor.array import Array, NDimArray

    for i, v in enumerate(variables):
        if isinstance(v, UndefinedFunction):
            raise TypeError(f"cannot differentiate wrt UndefinedFunction: {v}")

        if isinstance(v, array_likes):
            if len(v) == 0:
                # Ignore empty tuples: Derivative(expr, ... , (), ... )
                continue
            if isinstance(v[0], array_likes):
                # Derive by array: Derivative(expr, ... , [[x, y, z]], ... )
                if len(v) == 1:
                    v = Array(v[0])
                    count = 1
                else:
                    v, count = v
                    v = Array(v)
            else:
                v, count = v
            if count == 0:
                continue
            variable_count.append(Tuple(v, count))
            continue

        v = sympify(v)
        if isinstance(v, Integer):
            if i == 0:
                raise ValueError(f"First variable cannot be a number: {int(v)}")
            count = v
            prev, prevcount = variable_count[-1]
            if prevcount != 1:
                raise TypeError(f"tuple {(prev, prevcount)} followed by number {v}")
            if count == 0:
                variable_count.pop()
            else:
                variable_count[-1] = Tuple(prev, count)
        else:
            count = 1
            variable_count.append(Tuple(v, count))

    # light evaluation of contiguous, identical
    # items: (x, 1), (x, 1) -> (x, 2)
    merged = []
    for t in variable_count:
        v, c = t
        if c.is_negative:
            raise ValueError('order of differentiation must be nonnegative')
        if merged and merged[-1][0] == v:
            c += merged[-1][1]
            if not c:
                merged.pop()
            else:
                merged[-1] = Tuple(v, c)
        else:
            merged.append(t)
    variable_count = merged

    # sanity check of variables of differentation; we waited
    # until the counts were computed since some variables may
    # have been removed because the count was 0
    for v, _c in variable_count:
        # v must have _diff_wrt True
        if not v._diff_wrt:
            __ = ''  # filler to make error message neater
            raise ValueError(
                filldedent(
                    f'''
                Can't calculate derivative wrt {v}.{__}'''
                )
            )

    # We make a special case for 0th derivative, because there is no
    # good way to unambiguously print this.
    if len(variable_count) == 0:
        return expr

    evaluate = kwargs.get('evaluate', False)
    if evaluate:
        if isinstance(expr, Derivative):
            expr = expr.canonical
        variable_count = [
            (v.canonical if isinstance(v, Derivative) else v, c) for v, c in variable_count
        ]

        # Look for a quick exit if there are symbols that don't appear in
        # expression at all. Note, this cannot check non-symbols like
        # Derivatives as those can be created by intermediate
        # derivtives.
        zero = False
        free = expr.free_symbols  # XXX: 90 percent of the time goes here
        from sympy.matrices.expressions.matexpr import MatrixExpr

        for v, c in variable_count:
            vfree = v.free_symbols
            if c.is_positive and vfree:
                if isinstance(v, AppliedUndef):
                    # these match exactly since
                    # x.diff(f(x)) == g(x).diff(f(x)) == 0
                    # and are not created by differentiation
                    D = Dummy()
                    if not expr.xreplace({v: D}).has(D):
                        zero = True
                        break
                elif isinstance(v, MatrixExpr):
                    zero = False
                    break
                elif isinstance(v, Symbol) and v not in free:
                    zero = True
                    break
                else:
                    if not free & vfree:
                        # e.g. v is IndexedBase or Matrix
                        zero = True
                        break
        if zero:
            return cls._get_zero_with_shape_like(expr)

        # make the order of symbols canonical
        # TODO: check if assumption of discontinuous derivatives exist
        variable_count = cls._sort_variable_count(variable_count)

    # denest
    if isinstance(expr, Derivative):
        variable_count = list(expr.variable_count) + variable_count
        expr = expr.expr
        return _derivative_dispatch(expr, *variable_count, **kwargs)

    # we return here if evaluate is False or if there is no
    # _eval_derivative method
    if not evaluate or not hasattr(expr, '_eval_derivative'):
        # return an unevaluated Derivative
        if evaluate and variable_count == [(expr, 1)] and expr.is_scalar:
            # special hack providing evaluation for classes
            # that have defined is_scalar=True but have no
            # _eval_derivative defined
            return S.One
        return Expr.__new__(cls, expr, *variable_count)

    # evaluate the derivative by calling _eval_derivative method
    # of expr for each variable
    # -------------------------------------------------------------
    nderivs = 0  # how many derivatives were performed
    unhandled = []
    from sympy.matrices.matrixbase import MatrixBase

    for i, (v, count) in enumerate(variable_count):
        old_expr = expr
        old_v = None

        is_symbol = v.is_symbol or isinstance(v, (Iterable, Tuple, MatrixBase, NDimArray))
        if not is_symbol:
            old_v = v
            v = Dummy('xi')
            expr = expr.xreplace({old_v: v})
            # Derivatives and UndefinedFunctions are independent
            # of all others
            clashing = not (isinstance(old_v, (Derivative, AppliedUndef)))
            if v not in expr.free_symbols and not clashing:
                return expr.diff(v)  # expr's version of 0
            if not old_v.is_scalar and not hasattr(old_v, '_eval_derivative'):
                # special hack providing evaluation for classes
                # that have defined is_scalar=True but have no
                # _eval_derivative defined
                expr *= old_v.diff(old_v)

        obj = cls._dispatch_eval_derivative_n_times(expr, v, count)
        if is_zero(obj):
            return obj

        nderivs += count

        if old_v is not None:
            if obj is not None:
                # remove the dummy that was used
                obj = obj.subs(v, old_v)
            # restore expr
            expr = old_expr

        if obj is None:
            # we've already checked for quick-exit conditions
            # that give 0 so the remaining variables
            # are contained in the expression but the expression
            # did not compute a derivative so we stop taking
            # derivatives
            unhandled = variable_count[i:]
            break
        expr = obj
    # what we have so far can be made canonical
    # Removed from original __new__
    #    expr = expr.replace(
    #        lambda x: isinstance(x, Derivative),
    #        lambda x: x.canonical)

    if unhandled:
        if isinstance(expr, Derivative):
            unhandled = list(expr.variable_count) + unhandled
            expr = expr.expr
        expr = Expr.__new__(cls, expr, *unhandled)

    # removed from original __new__
    # if (nderivs > 1) == True and kwargs.get('simplify', True):
    #    from sympy.core.exprtools import factor_terms
    #    from sympy.simplify.simplify import signsimp
    #    expr = factor_terms(signsimp(expr))
    return expr


Derivative.__new__ = _derivative_new


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
def is_function(e) -> bool:
    """checks whether an expression 'e' is a pure function without any
    derivative as a factor
    """
    return e.is_Function


@profile_if_enabled
def func_diff(fun: Function, var: Symbol | Function) -> Derivative:
    if var.is_Function or var.is_Derivative:
        d = Symbol('d')
        r = fun.xreplace({var: d}).diff(d).xreplace({d: var}).doit()
    else:
        r = Derivative(fun, var).doit()
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


def ltf(expr, dep, indep, infinitesimals=None, printer=True):
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
    return Function(f'{name if name else v.name.swapcase()}')(*variables)


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


def lie_derivative_printer(
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
