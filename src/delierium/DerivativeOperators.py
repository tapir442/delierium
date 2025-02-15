#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Jan 18 13:45:11 2022

@author: tapir
"""
# from https://ask.sagemath.org/question/7929/computing-variational-derivatives/
from IPython.core.debugger import set_trace
from delierium.helpers import is_function, is_derivative
import functools
from operator import mul

from sympy import *
from sympy.core.backend import diff


from symengine.lib.symengine_wrapper import FunctionSymbol

def replace_function(expression,function,new_function):
    if expression.is_Atom:
        return expression
    else:
        replaced_args = (
		    replace_function(arg,function,new_function)
		    for arg in expression.args
	    )
        if (expression.__class__ == FunctionSymbol and expression.get_name() == function.name):
            return new_function(*replaced_args)
        else:
            return expression.func(*replaced_args)

# https://stackoverflow.com/questions/56584025/sympy-subs-vs-replace-vs-xreplace
#https://stackoverflow.com/questions/66175255/sympy-how-to-implement-a-general-substitution-for-several-look-alike-terms
#https://stackoverflow.com/questions/44169734/replacing-functions-in-a-sympy-expression-with-a-symbol-of-the-same-name
#https://stackoverflow.com/questions/36197283/recursive-substitution-in-sympy
#https://stackoverflow.com/questions/53687281/how-to-implement-a-function-with-pythonsympy-realizing-the-same-as-and-re
#https://stackoverflow.com/questions/73426255/why-does-substitution-into-a-sympy-derivative-only-partly-work
#https://stackoverflow.com/questions/69399155/defining-functions-of-symbols-and-other-functions-in-sympy
#https://stackoverflow.com/questions/40264977/sympy-equivalent-to-holdform-in-mathematica


def is_op_du(expr_op, u):
    """
    >>> x, y = symbols('x, y')
    >>> u = Function('u')(x)
    >>> v = Function('v')(x, y)
    >>> d = diff(u, x, x)
    >>> is_op_du(d, u)
    True
    >>> is_op_du(d, v)
    False
    >>> is_op_du(v, u)
    False
    """
    if not is_derivative(expr_op):
        return False
    return expr_op.args[0] == u


def iter_du_orders(expr, u):
    for sub_expr in expr.args:
        if sub_expr == []:
            # hit end of tree
            continue

        elif is_op_du(sub_expr.operator(), u):
            # yield order of differentiation
            yield len(sub_expr.operator().parameter_set())

        else:
            # iterate into sub expression
            for order in iter_du_orders(sub_expr, u):
                yield order


def func_diff(L, u_in):
    # `u` must be a callable symbolic expression
    # in one variable.
    set_trace()
    if len(u_in.variables()) == 1:
        x = u_in.variables()[0]
        u = u_in.function(x)
    else:
        raise TypeError

    # This variable name must not collide
    # with an existing one.
    # I use "tapir" in hopes that
    # nobody else does this...
    t = SR.var('t')
    result = SR(0)
    # `orders` is the set of all
    # orders of differentiation of `u`
    orders = set(iter_du_orders(L, u)).union((0,))

    for c in orders:
        du = u(x).diff(x, c)
        sign = Integer(-1)**c

        # Temporarily replace all `c`th derivatives of `u` with `t`;
        # differentiate; then substitute back.
        dL_du = L.subs({du: t}).diff(t).subs({t: du})
        # Append intermediate term to `result`
        result += sign * dL_du.diff(x, c)

    return result

#ar('x')
#= function('u')(x)
#
#g=SR.var('g')
#L = sqrt((1 + u.diff(x)**2)/(2*g*x))
#L
#set_trace()
#print(func_diff(L, u))
# Baumann pp 67
#1/2*sqrt(1/2)*(2*diff(u(x), x)*diff(u(x), x, x)/(g*x) - (diff(u(x), x)^2 + 1)/(g*x^2))*diff(u(x), x)/(g*x*((diff(u(x), x)^2 + 1)/(g*x))^(3/2)) - sqrt(1/2)*diff(u(x), x, x)/(g*x*sqrt((diff(u(x), x)^2 + 1)/(g*x))) + sqrt(1/2)*diff(u(x), x)/(g*x^2*sqrt((diff(u(x), x)^2 + 1)/(g*x)))
#
#s = var('s')
#q = function('q')(s)
#l = function("l")

#L = l(s, q(s), q.diff(s))
#print(func_diff(l(s, q(s), q.diff(s)), u))




def EulerD(density, depend, independ):
    r'''
    >>> t = symbols("t")
    >>> u= Function('u')
    >>> v= Function('v')
    >>> L=u(t)*v(t) + diff(u(t), t)**2 + diff(v(t), t)**2 - u(t)**2 - v(t)**2
    >>> EulerD(L, (u,v), t)
    [-2*u(t) + v(t) - 2*Derivative(u(t), (t, 2)), u(t) - 2*v(t) - 2*Derivative(v(t), (t, 2))]
    >>> L=u(t)*v(t) + Derivative(u(t), t)**2 + Derivative(v(t), t)**2 + 2*Derivative(u(t), t) * Derivative(v(t), t)
    >>> EulerD(L, (u,v), t)
    [v(t) - 2*Derivative(u(t), (t, 2)) - 2*Derivative(v(t), (t, 2)), u(t) - 2*Derivative(u(t), (t, 2)) - 2*Derivative(v(t), (t, 2))]
    '''
    wtable = [Function("w_%s" % i) for i in range(len(depend))]
    y = Function('y')(independ)
    w = Function('w')(independ)
    e = symbols('e')
    result = []
    for j in range(len(depend)):
        loc_result = 0
        def f0(*args):
            return y + e * w
        def dep(*args):
            return depend[j](independ)
        fh = density.replace(depend[j], f0)
        fh = fh.replace(y, dep)
        fh = fh.replace(w, wtable[j](independ))
        fh = fh.diff(e)
        fh = fh.subs({e:0}).expand()
        if fh.func == Mul:
            operands = [fh]
        else:
            operands = fh.args
        for operand in operands:
            d     = None
            coeff = []
            for _ops in operand.args:
                if is_op_du(_ops, wtable[j](independ)):
                    d = _ops.args[1][1]
                elif is_function(_ops) and _ops.func == wtable[j]:
                    pass
                else:
                    coeff.append(_ops)
            coeff = functools.reduce(mul, coeff, 1)
            if d is not None:
                coeff = ((-1)**d)*diff(coeff, independ, d)
            loc_result += coeff
        result.append(loc_result)
    return result


def FrechetD (support, dependVar, independVar, testfunction):
    """
    >>> x,t = symbols("x t")
    >>> v   = Function("v")
    >>> u   = Function("u")
    >>> w1  = Function("w1")
    >>> w2  = Function("w2")
    >>> eqsys = [diff(v(x,t), x) - u(x,t), diff(v(x,t), t) - diff(u(x,t), x)/(u(x,t)**2)]
    >>> dependent = [u,v]
    >>> independent = [x,t]
    >>> m = Matrix(FrechetD (eqsys, [u,v], [x,t], [w1,w2]))
    >>> print(m[0, 0])
    -w1(x, t)
    >>> print(m[0, 1])
    Derivative(w2(x, t), x)
    >>> print(m[1, 0])
    -Derivative(w1(x, t), x)/u(x, t)**2 + 2*w1(x, t)*Derivative(u(x, t), x)/u(x, t)**3
    >>> print(m[1, 1])
    Derivative(w2(x, t), t)
    """
    frechet = []
    eps = symbols("eps")
    for j in range (len(support)):
        deriv = []
        for i in range (len(support)):
            def r0(*args):
                return dependVar[i](*independVar)+ testfunction[i](*independVar) * eps
            #def _r0(*args):
            #    # this version has issues as it always uses w2 ?!? investigate further
            #    # when time and motivation. Online version on asksage works perfectly
            #    return dependVar[i](*independVar)+ testfunction[i](*independVar) * eps
            #r0 = function('r0', eval_func=_r0)
            _r0 = r0
            breakpoint()
            print(f"{support[j].__class__}")
            s  =  support[j].subs({dependVar[i](*independVar) :
                                   dependVar[i](*independVar)+ testfunction[i](*independVar) * eps})
            kk=s.subs({dependVar[i](*independVar) : Symbol('mausi')})
            kuku = kk.diff(eps)
            susu = kuku.subs({Symbol('mausi') : dependVar[i](*independVar)})
            lulu = susu.subs({eps : 0})

            deriv.append (susu)
        frechet.append (deriv)
    return frechet




def AdjointFrechetD(support, dependVar, independVar, testfunction):
    frechet = FrechetD(support, dependVar, independVar, testfunction)



if __name__ == "__main__":
    import doctest
    doctest.testmod()
