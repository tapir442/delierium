"""Convenience functions"""

import itertools
import os
from typing import Iterable, Callable
from IPython.core.debugger import set_trace  # type: ignore
from line_profiler import profile
from sympy import (Add, Basic, Derivative, Dummy, Expr, Function, Integer, Mul,
                   Pow, Rational, S, Subs, Symbol, Tuple, sympify)
from sympy.core.function import (AppliedUndef, UndefinedFunction,
                                 _derivative_dispatch)
from sympy.core.numbers import Half, Integer, NegativeOne, One, Rational, Zero

from sympy.core.backend import *

from functools import cache
from collections import OrderedDict

try:
    __IPYTHON__
    _in_ipython_session = True
except NameError:
    _in_ipython_session = False


import functools

#################################################################

# Global cache for free_symbols
_free_symbols_cache = {}

def make_cached_property(original_property: Callable) -> Callable:
    original_getter = original_property.fget

    @functools.wraps(original_getter)
    def cached_getter(self):
        obj_id = id(self)
        if obj_id not in _free_symbols_cache:
            _free_symbols_cache[obj_id] = original_getter(self)
        return _free_symbols_cache[obj_id]

    return property(cached_getter)


# Patch the free_symbols property
#Basic.free_symbols = make_cached_property(Basic.free_symbols)
#Basic.expr_free_symbols = make_cached_property(Basic.expr_free_symbols)
#Derivative.free_symbols = make_cached_property(Derivative.free_symbols)
#Expr.free_symbols = make_cached_property(Expr.free_symbols)
#Expr.expr_free_symbols = make_cached_property(Expr.expr_free_symbols)

###############################################

#fast solution für Profiling:
def profile_if_enabled(func):
    if os.environ.get('JANET_PROFILE', 'false').lower() == 'true':
        return profile(func)
    return func

@profile_if_enabled
@cache
def is_zero(obj):
    return obj is not None and obj.is_zero

@profile_if_enabled
def __new__(cls, expr, *variables, **kwargs):
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

    # determine value for variables if it wasn't given
#    Removed from original sympy.core.function.Derivative.__new__
#    because we don't need it, as we use it only internally

#    if not variables:
#         variables = expr.free_symbols
#         if len(variables) != 1:
#             if expr.is_number:
#                 return S.Zero
#             if len(variables) == 0:
#                 raise ValueError(filldedent('''
#                     Since there are no variables in the expression,
#                     the variable(s) of differentiation must be supplied
#                     to differentiate %s''' % expr))
#             else:
#                 raise ValueError(filldedent('''
#                     Since there is more than one variable in the
#                     expression, the variable(s) of differentiation
#                     must be supplied to differentiate %s''' % expr))

    # Split the list of variables into a list of the variables we are diff
    # wrt, where each element of the list has the form (s, count) where
    # s is the entity to diff wrt and count is the order of the
    # derivative.
    variable_count = []
    array_likes = (tuple, list, Tuple)

    from sympy.tensor.array import Array, NDimArray

    for i, v in enumerate(variables):
        if isinstance(v, UndefinedFunction):
            raise TypeError(
                "cannot differentiate wrt "
                "UndefinedFunction: %s" % v)

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
                raise ValueError("First variable cannot be a number: %i" % v)
            count = v
            prev, prevcount = variable_count[-1]
            if prevcount != 1:
                raise TypeError("tuple {} followed by number {}".format((prev, prevcount), v))
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
            raise ValueError(
                'order of differentiation must be nonnegative')
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
    for v, c in variable_count:
        # v must have _diff_wrt True
        if not v._diff_wrt:
            __ = ''  # filler to make error message neater
            raise ValueError(filldedent('''
                Can't calculate derivative wrt %s.%s''' % (v, __)))

    # We make a special case for 0th derivative, because there is no
    # good way to unambiguously print this.
    if len(variable_count) == 0:
        return expr

    evaluate = kwargs.get('evaluate', False)
    if evaluate:
        if isinstance(expr, Derivative):
            expr = expr.canonical
        variable_count = [
            (v.canonical if isinstance(v, Derivative) else v, c)
            for v, c in variable_count]

        # Look for a quick exit if there are symbols that don't appear in
        # expression at all. Note, this cannot check non-symbols like
        # Derivatives as those can be created by intermediate
        # derivtives.
        zero = False
        free = expr.free_symbols # XXX: 90 percent of the time goes here
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
        #TODO: check if assumption of discontinuous derivatives exist
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

        is_symbol = v.is_symbol or isinstance(v,
            (Iterable, Tuple, MatrixBase, NDimArray))
        if not is_symbol:
            old_v = v
            v = Dummy('xi')
            expr = expr.xreplace({old_v: v})
            # Derivatives and UndefinedFunctions are independent
            # of all others
            clashing = not (isinstance(old_v, (Derivative, AppliedUndef)))
            if v not in expr.free_symbols and not clashing:
                return expr.diff(v)  # expr's version of 0
            if not old_v.is_scalar and not hasattr(
                    old_v, '_eval_derivative'):
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

from sympy.core.cache import cacheit, __cacheit

Derivative.__new__ = __new__

def __mysetattr__(self, name, val):
    self.__dict__[name] = val
    self.__dict__.pop('value', None)


#Basic.free_symbols = make_cached_property(Basic.free_symbols)
#setattr(Basic, "__setattr__", __mysetattr__)

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
    >>> from sympy import diff
    >>> x = Symbol('x')
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
def func_diff(fun: Function, var: Symbol | Function) -> Derivative:
    if var.is_Function or var.is_Derivative:
        d = Symbol('d')
        r = fun.xreplace({var: d}).diff(d).xreplace({d: var}).doit()
    else:
        r = Derivative(fun, var).doit()
    return r


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


def ltf(expr, dep, indep, printer=True):
    """Lie Traditional Form."""
    try:
        functions = expr.atoms(Function)
    except AttributeError:
        functions = []
    coefficient_functions = isolate_cefficient_functions(functions, dep)
#    set_trace()
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
#            import pdb; pdb.set_trace()
            output = output.xreplace({deriv: used_symbols[fluffi]})
        else:
            s = Symbol(fluffi)
            used_symbols[fluffi] = s
#            import pdb; pdb.set_trace()
            output = output.xreplace({deriv: used_symbols[fluffi]})

    dreps2 = {}

    if len(indep) == 1:
        # the original dependent variables should be written with primes
        dreps2 = dict([(deriv, (Symbol(deriv.output.subs(coefficient_functions) +
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
    output = output.xreplace(dreps2).xreplace(fundic).xreplace(coefficient_functions)
    if printer:
        if _in_ipython_session:
            display(output)
        else:
            print(output)
    return output

@profile_if_enabled
def isolate_cefficient_functions(functions, dep):
    reps = OrderedDict()
    for fun in [_ for _ in functions if _ not in dep]:
        # Consider the case that some functions won't have the name
        # attribute e.g. Abs of an elementary function
        try:
            reps[fun] = Symbol(fun.name) # Otherwise functions with greek symbols aren't replaced
        except AttributeError:
            continue
    return reps

@profile_if_enabled
def make_infinitesimal(v, *variables, name=""):
    """
    >>> x = Symbol('x')
    >>> f = Function('f')(x)
    >>> i = make_infinitesimal(f, f, x, name="phi")
    >>> i
    phi(f(x), x)
    """
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
