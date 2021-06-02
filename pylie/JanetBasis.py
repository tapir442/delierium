#!/usr/bin/env python
# coding: utf-8

from sage.all import *
import pylie.pylie
import pylie.MatrixOrder
from pprint import pprint
pprint (dir(pylie))
import functools
from operator import mul

class DTerm:
    '''differential term'''
    # XXX make it a local class within Derivative_Polynomial?
    # than we maybe can  skip the damne 'o' paramter in self.ordertder
    def __init__ (self, e, context = None):
        self._coeff       = 1
        self._d           = 1
        self._context     = context
        r = []
        if pylie.pylie.is_derivative(e):
            self._d = e
        else :
            for o in e.operands ():
                if pylie.pylie.is_derivative (o):
                    self._d = o
                else:
                    r.append (o)
            self._coeff = functools.reduce (mul, r, 1)
    def __str__ (self):
        return "{} * {}".format (self._coeff, self._d)
    def term(self):
        return self._coeff * self._d
    def order (self):
        if pylie.is_derivative(self._d):
            return pylie.pylie.order_of_derivative (self._d)
        else:
            return [0] * len (context._independent)
    def is_coefficient(self):
        return self._d == 1
    def is_monic(self):
        return self._d != 1 and self._coeff == 1
    def __lt__ (self, other):
        return pylie.MatrixOrder.higher (self._d, other._d,self._context) and not self._d == other._d
    def __le__ (self, other):
        return pylie.MatrixOrder.higher (self._d, other._d,self._context)
    def __ge__ (self, other):
        return pylie.MatrixOrder.higher (self._d, other._d,self._context) 
    def __gt__ (self, other):
        return pylie.MatrixOrder.higher (self._d, other._d,self._context) and not self._d == other._d
    def __eq__ (self, other):
        return self._d == other._d
    def __neq__ (self, other):
        return self._d != other._d
    
class Differential_Polynomial:
    def __init__ (self, e, context):
        self._orig    = e
        self._context = context
        self._init()

    def _init(self):
        res = []
        e = self._orig
        if pylie.is_derivative(e) or pylie.is_function(e):
            res = [DTerm(self._orig, self._context)]
        else:
            for operand in self._orig.operands():
                dterm = DTerm(operand, self._context)
                c, d  = dterm._coeff, dterm._d
                inserted = False
                for r in res:
                    if r._d == d:
                        r._coeff += c
                        inserted  = True
                        # not very elegant but enough in first order
                        break
                if not inserted :
                    res.append (dterm)
        if len(res) > 1:
            res=sorted(res,
                       key=functools.cmp_to_key(
                           lambda item1, item2:
                                MatrixOrder.sorter (item1, item2, self._context._weight,
                                                    tuple(context._dependent),
                                                    tuple(context._independent)
                                                   )
                       )
                      )
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
        self._p = [ DTerm((_._coeff / self._p[0]._coeff, self._context) * _._d) for _ in self._p]
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
