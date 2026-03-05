"""Convenience functions"""

import itertools
import os

import re

from typing import Any, Generator, Iterable, Tuple, TypeAlias

import more_itertools
from IPython.core.debugger import set_trace  # type: ignore
from line_profiler import profile
from symengine import FunctionSymbol
from sympy import *
from sympy import ordered, sympify
from sympy.core.backend import *
from sympy.core.numbers import Half, Integer, NegativeOne, One, Rational, Zero
from sympy.core.relational import Equality


# Schnelle Lösung für Profiling:
def profile_if_enabled(func):
    if os.environ.get('JANET_PROFILE', 'false').lower() == 'true':
        return profile(func)
    return func


@profile_if_enabled
def eq(d1, d2):
    if d1.__class__ != d2.__class__:
        return False
    return d1 == d2


@profile_if_enabled
def is_numeric(e):
    return isinstance(e, (Integer, Rational, int, float, complex, Zero, One, NegativeOne, Half)) \
        and not isinstance(e, bool)


@profile_if_enabled
def expr_eq(e1, e2):
    res = e1 - e2 == 0
    return res


@profile_if_enabled
def expr_is_zero(e):
    return e == 0

@profile_if_enabled
def pairs_exclude_diagonal(it):
    for x, y in itertools.product(it, repeat=2):
        if x != y:
            yield (x, y)

@profile_if_enabled
def is_derivative(e):
    """checks whether an expression 'e' is a pure derivative

    >>> from delierium.helpers import is_derivative
    >>> x = symbols('x')
    >>> f = Function('f')(x)
    >>> is_derivative (f)
    False
    >>> is_derivative (diff(f,x))
    True
    >>> is_derivative (diff(f,x)*x)
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
def _adiff(f, *vars):
    return f.diff(*vars)


@profile_if_enabled
def adiff(f, context, *vars):
    return _adiff(f, *tuple(vars))
    return  f.diff(*vars)

    use_func_diff = any(isinstance(v, Function) for v in vars)
    for op in f.operands():
        if "NewSymbolicFunction" in op.operator().__class__.__name__:
            use_func_diff = True
            break
    if use_func_diff:
        for v in vars:
            if "NewSymbolicFunction" in v.__class__.__name__:
                f = func_diff(f, v(context._independent[1]))
            else:
                xx = SR.var("xx")
                gg = f.subs(
                    {context._dependent[0](context._independent[1]): xx})
                gg = diff(gg, v)
                f = gg.subs(
                    {xx: context._dependent[0](context._independent[1])})
    else:
        f = f.diff(*vars)
    return f

@profile_if_enabled
def finish_substitution(expr):
    subs = set(expr.atoms(Subs))
    subs_dic = {}
    for s0 in subs:
        bound = s0.bound_symbols
        der = s0.args[0]
        var = s0.args[2]
        subs_dic[s0] = der.xreplace(dict(zip(bound, var)))
    return subs_dic


def ltf(expr, dep, indep):
    """Lie Traditional Form."""
    try:
        functions = expr.atoms(Function)
    except AttributeError:
        functions = []
    reps = {}
    for fun in [_ for _ in functions if _ not in dep]:
        # Consider the case that some functions won't have the name
        # attribute e.g. Abs of an elementary function
        try:
            reps[fun] = Symbol(fun.name) # Otherwise functions with greek symbols aren't replaced
        except AttributeError:
            continue
    # first, resolve the dangling substitutions. Don't know why the
    # substitution is not done, but it seems that it has to do with
    # that a bound variable is within a function which is used as
    # a derivation argument
    subs_dic = finish_substitution(expr)
    output = expr
    output = output.xreplace(subs_dic)
    used_symbols = {}
    for deriv in output.atoms(Derivative):
        # there is room to improve: collect indices and sort
        subindex = []
        for func_or_symbol, count in deriv.args[1:]:
            if func_or_symbol.is_Function:
                subindex.extend([func_or_symbol.name] * count)
            elif func_or_symbol.is_Symbol:
                subindex.extend([f"{func_or_symbol}"] * count)
            else:
                raise ValueError(f"{func_or_symbol=} has class {func_or_symbol.__class__=}")
        subindex = "{" + "".join(sorted(subindex)) + "}"

        fluffi = f"{deriv.args[0].name}_{subindex}"
        if fluffi in used_symbols:
            output = output.xreplace({deriv: used_symbols[fluffi]})
        else:
            s = Symbol(fluffi)
            used_symbols[fluffi] = s
            output = output.xreplace({deriv: used_symbols[fluffi]})

    dreps2 = {}

    if len(indep) == 1:
        # the original dependent variables should be written with primes
        dreps2 = dict([(deriv, (Symbol(deriv.output.subs(reps) +
                                ' '.join("'" * deriv.args[-1][1]))))  \
                 for deriv in output.atoms(Derivative) if deriv.args[0] in dep])
    else:
        derivatives = [_ for _ in output.atoms(Derivative) if _.args[0] in dep]
        for dev in derivatives:
            s = ""
            for arg in dev.args[1:]:
                if isinstance(arg[0], Function):
                    n = arg[0].name
                elif isinstance(arg[0], Symbol):
                    n = str(arg[0])
                else:
                    raise ValueError(f"{arg[0]} is type {type(arg[0])}")
                s += n*arg[1]
            dreps2[dev] = Symbol(f"{dev.args[0].name}_"  + "{" +f"{s}" + "}")

    fundic = dict([(_, Symbol(_.name)) for _ in dep])
    output = output.xreplace(dreps2).xreplace(fundic)
    display(output)

@profile_if_enabled
def make_infinitesimal(v, *variables, name=""):
    return Function(f'{v.name.swapcase() if not name else name}')(*variables)



# ToDo (from AllTypes.de
#    cfdgfdgfd
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
