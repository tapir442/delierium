#!/usr/bin/env python
# coding: utf-8

from sage.all import *
from pylie import *
from pprint import pprint
import functools
from operator import mul
from IPython.core.debugger import set_trace

class DTerm:
    '''differential term'''
    def __init__ (self, e, context = None):
        self._coeff       = Rational(1)
        self._d           = Rational(1)
        self._context     = context
        if is_derivative(e) or is_function(e):
            # XXX put into _d only if in in context
            self._d = e
        else:
            r = []
            for o in e.operands ():
                if is_derivative (o):
                    self._d = o
                else:
                    if is_function(o) and o in context._dependent:
                        self._d = o  # zeroth derivative
                    else:
                        r.append (o)
            self._coeff = functools.reduce (mul, r, 1).simplify_full()
            if not r:
                raise ValueError("invalid expression '{}' for DTerm".format(e))
    def __str__ (self):
        return "{} * {}".format (self._coeff, self._d)
    def term(self):
        return self._coeff * self._d
    def order (self):
        if is_derivative(self._d):
            return order_of_derivative (self._d)
        else:
            return [0] * len (context._independent)
    def is_coefficient(self):
        # XXX nonsense
        return self._d == 1
    def is_monic(self):
        return self._d != 1 and self._coeff == 1
    def __lt__ (self, other):
        return higher (self, other,self._context) and not self == other
    def __le__ (self, other):
        return higher (self, other,self._context)
    def __ge__ (self, other):
        return higher (self, other,self._context) 
    def __gt__ (self, other):
        return higher (self, other,self._context) and not self == other
    def __eq__ (self, other):
        return self._d == other._d and self._coeff == other._coeff
    def __neq__ (self, other):
        return self._d != other._d
    def show(self):
        self.term().show()
    def expression (self):
        return self.term().expression()
        
    
class Differential_Polynomial:
    def __init__ (self, e, context):
        self._context = context
        self._init(e)

    def _init(self, e):
        set_trace()
        self._p = []
        res = []
        if is_derivative(e) or is_function(e):
            res = [DTerm(e, self._context)]
        else:
            for s in e.operands ():
                coeff = []
                d     = []
                if is_derivative (s):
                    d.append(s)
                else:
                    for item in s.operands():
                        (d if (is_derivative(item) or self.ctxfunc (item)) else coeff).append(item)
                coeff = functools.reduce (mul, coeff, 1)
                if bool (coeff == 0):
                    continue
                found = False
                for _p in self._p:
                    if not d:
                        continue
                    if d and _p._d == d[0]:
                        _p._coeff += coeff
                        found = True
                        break
                if not found:
                    if d:
                        self._p.append (DTerm(coeff * d[0], self._context))
                    else:
                        self._p.append (DTerm(coeff, self._context))
        self._p = sorted(self._p)
        self.normalize()
    
    def ctxfunc(self, e):
        def func(e):    
            try:
                return e.operator().function()
            except AttributeError:
                return e.operator()  
        return func(e) and func(e) in self._context._dependent    

    def _collect_terms (self, e):
        pass
        
    def Lterm (self):
        return self._p[0].term()

    def Lder (self):
        return self._p[0]._d

    def Lcoeff(self):
        return self._p[0]

    def terms (self):
        for p in self._p:
            yield p.term()

    def derivatives (self):
        for p in self._p:
            yield p._d

    def coefficients (self):
        for p in self._p:
            yield p._coeff
    def is_monic (self):
        if self._p:
            return self._p[0].is_monic()
        return True
    def normalize (self):
        if self._p:
            self._p = [_ for _ in self._p if _._coeff and not bool(_._coeff == 0)]
            c = self._p[0]._coeff
            self._p = [ DTerm((_._coeff / c) * _._d, self._context) for _ in self._p]
        else:
            self._p._d= 0
            self._d._coeff = 0
    def expression (self):
        return sum(_._coeff * _._d for _ in self._p)
    def __lt__ (self, other):
        return self._p[0] < other._p[0]
    def __le__ (self, other):
        return self._p[0] <= other._p[0]
    def __ge__ (self, other):
        return self._p[0] >= other._p[0]
    def __gt__ (self, other):
        return self._p[0] > other._p[0]
    def __eq__ (self, other):
        #todo pythonify
        for a, b in zip (self._p, other._p):
            if a != b: return False
        return True
    def __neq__ (self, other):
        return self._p[0] != other._p[0]
    def show(self):
        self.expression().show()
    def __sub__ (self, other):
        for o in other._p:
            found = False
            for s in self._p:
                if s._d == o._d:
                    s._coeff -= o._coeff
                    found = True
                    break
        if not found:
            self._p.append(o)
            self._p[-1]._coeff *= Integer(-1)
        return Differential_Polynomial(self.expression(), self._context)
    def __add__ (self, other):
        for o in other._p:
            found = False
            for s in self._p:
                if s._d == o._d:
                    s._coeff += o._coeff
                    found = True
                    break
            if not found:
                self._p.append(o)
        return Differential_Polynomial(self.expression(), self._context)        
    def __mul__ (self, other):
        for t in self._p:
             t._coeff *= other
        return Differential_Polynomial(self.expression(), self._context)    
    def __copy__(self):
        newone = type(self)(self.expression(), self._context)
        return newone

# ToDo: Janet_Basis as class as this object has properties like rank, order ....

