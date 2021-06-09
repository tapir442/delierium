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
        if self._d == 1:
            set_trace ()
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
        return self._d == other._d
    def __neq__ (self, other):
        return self._d != other._d
    def show(self):
        self.term().show()
    
class Differential_Polynomial:
    def __init__ (self, e, context):
        self._orig    = e
        self._context = context
        self._init()

    def _init(self):
        res = []
        e = self._orig
        if is_derivative(e.expand()) or is_function(e.expand()):
            res = [DTerm(self._orig, self._context)]
        else:
            res = [DTerm(_, self._context) for _ in self._orig.operands()]
        if len(res) > 1:
            res=sorted(res)
        self._p = res
        self.normalize()

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
        c = self._p[0]._coeff
        self._p = [ DTerm((_._coeff / c) * _._d, self._context) for _ in self._p]
        assert sum(_._coeff * _._d for _ in self._p) == self._orig / c
    def __str__ (self):
        return str(self._orig)
    def __lt__ (self, other):
        return self._p[0] < other._p[0]
    def __le__ (self, other):
        return self._p[0] <= other._p[0]
    def __ge__ (self, other):
        return self._p[0] >= other._p[0]
    def __gt__ (self, other):
        return self._p[0] > other._p[0]
    def __eq__ (self, other):
        return self._p[0] == other._p[0]
    def __neq__ (self, other):
        return self._p[0] != other._p[0]
    def show(self):
        sum(_._coeff * _._d for _ in self._p).show()