#!/usr/bin/env python3
# -*- coding: utf-8 -*-
""" DPolynomial.
    Instead of a list use a tree
"""

import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.calculus.functional import diff
try :
    from delierium.helpers import (is_derivative, is_function, eq,
                                   order_of_derivative)
    from delierium.MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
except ModuleNotFoundError:
    from helpers import (is_derivative, is_function, eq,
                               order_of_derivative)
    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex

import functools
from operator import mul
from IPython.core.debugger import set_trace
from collections.abc import Iterable
from more_itertools import powerset, bucket, flatten
from itertools import product, combinations, islice
from sage.modules.free_module_element import vector

class OperatorNotFound(Exception):
    pass

class _DTerm:
    """Internal differential term, with arrays instead of real derivatives
    """
    def __init__(self, d, c):
        self._d = d
        self._c = c
    def diff(self, a):


class DTerm:
    def __init__ (self, term = None, derivative = None, coefficient = None, context = None):
        assert (term is not None or (derivative is not None and coefficient is not None))
        set_trace()
        self._context =  context
        if term is not None:
            self._analyze_term(term)
        else:
            self._derivative  = order_of_derivative(derivative)
            self._coefficient = coefficient
    def _analyze_term(self, term):
        ops         = term.operands()
        derivative  = [_ for _ in ops if is_derivative(_)]
        derivative  = derivative[0] if derivative else 1
        ops.remove(derivative)
        coefficient = functools.reduce(mul, ops, 1)
        self._coefficient = coefficient
        self._derivative  = order_of_derivative(derivative)
    def _analyze_dterm(self, dd):
        print("====>", dd)
        if is_derivative(dd):
            f = dd.operator().function()
        elif is_function(dd):
            f = dd.operator()
        else:
            f = [_ for _ in dd.operands() if is_function(_) or is_derivative(_)][0]
            if is_derivative(f):
                f = f.operator().function()
        return f
    def _compute_derivative_vector(self):
        self._derivative_vector = [0]*len(self._context._independent)
    def __lt__ (self, other):
        return 0
    def __str__ (self):
        return "%s" % self.__dict__
    def get_derivative_vector(self, d):
        def idx(d):
            # faster than functools.cache
            #set_trace()
            return self._context._independent.index(d[0])

        # XXX to helpers
        iv = [0]*len(self._context._independent)
        iv [idx(d)] += 1
        return vector(order_of_derivative(d, len(self._context._independent)) + iv)

    def diff(self, *vars):
        set_trace()
        if isinstance(vars[0], int):
            # tuple of derivatives
            pass
        else:
            v =  self.get_derivative_vector(vars)
        return [DTerm(derivative = v + self._derivative,
                      coefficient=self._coefficient, context=self._context),
                DTerm(derivative = self._derivative,
                      coefficient=diff(self._coefficient, *v), context=self._context)
                ]

x1,x2,x3, x4 = vars = var("x1 x2 x3 x4")
f = function("f")
g = function("g")
h = function("h")

mf = function('mf')(x4,x1,x2,x3)

print(mf.variables())



samples = [_p for _p in flatten(_ for _ in zip(vars, (randint(0,6) for i in range(len(vars)))))]
from pprint import pprint
pprint (samples)

bb = diff(f(*vars), *samples)
print(bb)
cc = diff(bb*(x1**3 + x3), x1,x2,x3)
print(cc)

ctx = Context([f,g], [x4,x3,x2,x1])

schmurki = DTerm(term=cc, context=ctx)
print("schmurki")
print(schmurki)


i = x1**2*x3**4
print(i.degrees(x1,x2))


p = diff(f(x1,x2,x3,x4), x1,x2,2,x3,x4)*((x1**2)/(x1**3))
q = diff(h(x1,x2,x3,x4), x1, x2)

d1=DTerm(term = diff(f(x1,x2,x3,x4), x1,x2,2,x3,x4)*((x1**2)/(x2**3)+x4**2), context = ctx)
print(d1)
print(d1.diff(x1))




def func(e):
    try:
        return e.operator().function()
    except AttributeError:
        try:
            return e.operator()
        except AttributeError:
            return e



def split_term(ops, context):
    d = [o for o in ops if func(o) and func(o) in context._dependent][0] or 1
    c = functools.reduce(mul, [o for o in ops if o != d], 1) or 1
    return d, c

import numbers

class DPolynomial:
    def __init__(self, p, context):
        self._context = context
        operands = p.operands()
        operator = p.operator()
        if operator.__name__ == 'mul_vararg':
            d, c = split_term(operands, context)
            print (order_of_derivative(d))
        elif operator.__name__ == 'add_vararg':
            for operand in operands:
                pprint(order_of_derivative(operand))
        else:
            raise OperatorNotFound()

class DPolynomial_System:
    pass





p = diff(f(x1,x2,x3,x4), x1,x2,2,x3,x4)*((x1**2)/(x1**3)) + \
    diff(h(x1,x2,x3,x4), x1, x2)
p.show()

DPolynomial(p, ctx)
DPolynomial(diff(f(x1,x2,x3,x4), x1,x2,2,x3,x4)*((x1**2)/(x1**3)), ctx)
DPolynomial(1, ctx)
