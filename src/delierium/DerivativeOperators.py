#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Jan 18 13:45:11 2022

@author: tapir (rewritten for SymPy by GitHub Copilot Chat Assistant)
"""
from sympy import symbols, Function, diff, Matrix, S
from sympy.core.function import UndefinedFunction
from sympy.core.compatibility import iterable
from sympy.abc import _clash1
from functools import reduce
from operator import mul

def is_function(expr):
    # Equivalent of Sage's is_function: checks if expr is a function application
    return expr.func.__class__ is UndefinedFunction or isinstance(expr, Function)

def is_op_du(expr, u):
    """
    Check if expr is a derivative of u.
    """
    if expr.func == diff:
        # In sympy, a derivative is represented as Derivative(f(x), x)
        f = expr.args[0]
        if f.func == u.func:
            return True
    return False

def iter_du_orders(expr, u):
    """
    Yield all derivative orders of u appearing in expr.
    """
    if hasattr(expr, 'args') and expr.args:
        for sub_expr in expr.args:
            if sub_expr == []:
                continue
            elif is_op_du(sub_expr, u):
                order = len(sub_expr.args) - 1  # first arg is function, rest are vars
                yield order
            else:
                yield from iter_du_orders(sub_expr, u)

def func_diff(L, u_in):
    """
    Compute the variational derivative (Euler-Lagrange operator) of L with respect to u.
    """
    if len(u_in.free_symbols) == 1:
        x = list(u_in.free_symbols)[0]
        u = Function(u_in.func.__name__)(x)
    else:
        raise TypeError("Input function must have exactly one variable.")
    t = symbols('tapir')  # dummy variable
    result = S(0)
    orders = set(iter_du_orders(L, u)).union((0,))
    for c in orders:
        du = diff(u, x, c)
        sign = (-1)**c
        # Replace all c-th derivatives of u with t, differentiate, then substitute back
        dL_du = L.subs({du: t}).diff(t).subs({t: du})
        result += sign * diff(dL_du, x, c)
    return result

def EulerD(density, depend, independ):
    r'''
    >>> from sympy import symbols, Function, diff
    >>> t = symbols("t")
    >>> u = Function('u')
    >>> v = Function('v')
    >>> L = u(t)*v(t) + diff(u(t), t)**2 + diff(v(t), t)**2 - u(t)**2 - v(t)**2
    >>> EulerD(L, (u, v), t)
    [-2*u(t) + v(t) - 2*diff(u(t), t, t), u(t) - 2*v(t) - 2*diff(v(t), t, t)]
    >>> L2 = u(t)*v(t) + diff(u(t), t)**2 + diff(v(t), t)**2 + 2*diff(u(t), t) * diff(v(t), t)
    >>> EulerD(L2, (u, v), t)
    [v(t) - 2*diff(u(t), t, t) - 2*diff(v(t), t, t), u(t) - 2*diff(u(t), t, t) - 2*diff(v(t), t, t)]
    '''
    wtable = [Function("w_%s" % i) for i in range(len(depend))]
    y = Function('y')
    w = Function('w')
    e = symbols('e')
    result = []
    for j in range(len(depend)):
        loc_result = 0
        def f0(x):
            return y(independ) + e * w(independ)
        def dep(x):
            return depend[j](independ)
        fh = density.replace(depend[j], f0)
        fh = fh.replace(y, dep)
        fh = fh.replace(w, wtable[j])
        fh = fh.diff(e).subs(e, 0).expand()
        operands = fh.args if fh.is_Mul else (fh,)
        for operand in operands:
            d = None
            coeff = []
            for _ops in operand.args if hasattr(operand, 'args') else ():
                if is_op_du(_ops, wtable[j](independ)):
                    d = sum(1 for a in _ops.args[1:] if a == independ)
                elif is_function(_ops) and _ops.func == wtable[j]:
                    pass
                else:
                    coeff.append(_ops)
            coeff = reduce(mul, coeff, 1) if coeff else 1
            if d is not None:
                coeff = ((-1)**d)*diff(coeff, independ, d)
            loc_result += coeff
        result.append(loc_result)
    return result

def FrechetD(support, dependVar, independVar, testfunction):
    """
    >>> from sympy import symbols, Function, diff, Matrix
    >>> x, t = symbols("x t")
    >>> v = Function("v")
    >>> u = Function("u")
    >>> w1 = Function("w1")
    >>> w2 = Function("w2")
    >>> eqsys = [diff(v(x, t), x) - u(x, t), diff(v(x, t), t) - diff(u(x, t), x)/(u(x, t)**2)]
    >>> m = Matrix(FrechetD(eqsys, [u, v], [x, t], [w1, w2]))
    >>> m[0, 0]
    -w1(x, t)
    >>> m[0, 1]
    diff(w2(x, t), x)
    >>> m[1, 0]
    2*w1(x, t)*diff(u(x, t), x)/u(x, t)**3 - diff(w1(x, t), x)/u(x, t)**2
    >>> m[1, 1]
    diff(w2(x, t), t)
    """
    frechet = []
    eps = symbols("eps")
    for j in range(len(support)):
        deriv = []
        for i in range(len(support)):
            def r0(*args):
                return dependVar[i](*independVar) + testfunction[i](*independVar) * eps
            s = support[j].replace(dependVar[i], r0)
            deriv.append(diff(s, eps).subs({eps: 0}))
        frechet.append(deriv)
    return frechet

def AdjointFrechetD(support, dependVar, independVar, testfunction):
    # Placeholder: in SymPy, adjoint computation is not built-in
    return FrechetD(support, dependVar, independVar, testfunction)

if __name__ == "__main__":
    import doctest
    doctest.testmod()


