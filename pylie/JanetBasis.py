#!/usr/bin/env python
# coding: utf-8

from sage.all import *
from pylie import pylie
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
        if pylie.is_derivative(e):
            self._d = e
        else :
            for o in e.operands ():
                if pylie.is_derivative (o):
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
            return pylie.order_of_derivative (self._d)
        else:
            return [0] * len (context._independent)
    def is_coefficient(self):
        return self._d == 1
    def is_monic(self):
        return self._d != 1 and self._coeff == 1

class Differential_Polynomial:
    def __init__ (self, e, context):
        self._orig = e
        self._init(e, context)

    def _init(self, e, context):
        res = []
        if pylie.is_derivative(e) or pylie.is_function(e):
            print ()
            res = [DTerm(self._orig)]
        else:
            for operand in self._orig.operands():
                dterm = DTerm(operand)
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
                                MatrixOrder.sorter (item1._d, item2._d , context._weight,
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
        self._p = [ DTerm((_._coeff / self._p[0]._coeff) * _._d) for _ in self._p]
    def __str__ (self):
        return str(self._orig)
