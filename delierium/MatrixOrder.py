#!/usr/bin/env python
# coding: utf-8

from sage.all import *
from functools import lru_cache
import delirium.helpers as helpers
import doctest
#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#
@lru_cache()
def Mlex(f, v):
    '''Generates the "cotes" according to Riquier for the lex ordering
    '''
    m = len(f)
    n = len(v)
    i = matrix.identity(n)
    i = i.insert_row(0, [Integer(0)]*n)
    for j in range(m,0,-1):
        i = i.augment (vector([j] + [0]*n))
    return i

@lru_cache()
def Mgrlex(f, v):
    m = Mlex(f,v)
    m = m.insert_row(0, [Integer(1)]*len(v)+[Integer(0)]*len(f))
    return m

@lru_cache()
def Mgrevlex(f,v):
    m = len(f)
    n = len(v)
    # why is this integer conversion necessary?
    l = Matrix([Integer(1)]*n + [Integer(0)]*m)
    l = l.insert_row(1, vector([0]*n + [Integer(_) for _ in range(m,0,-1)]))
    for idx in range (n):
        _v = vector([0]*(n+m))
        _v [n-idx-1] = -1
        l = l.insert_row(2+idx, _v)
    return l

@lru_cache()
def idx (d, dependent, independent):
    '''helper function'''
    # this caching gains about 30 % of runtime,
    # but still pretty slow.
    if helpers.is_derivative (d):
        return dependent.index(d.operator().function()(*list(independent)))
    return -1

class Context:
    # XXX replace by named tuple? or attr.ib
    def __init__ (self, dependent, independent, weight = Mlex):
        """ sorting : (in)dependent [i] > dependent [i+i]        
        """
        # XXX maybe we can create the matrices here?
        self._independent = tuple(independent)
        self._dependent   = tuple(dependent)
        self._weight      = weight
        self._basefield   = PolynomialRing(QQ, independent)

def higher (d1 ,d2, context):
    '''Algorithm 2.3 from [Schwarz]'''
    if d1 == d2:
        return True
    d1 = d1._d
    d2 = d2._d
    d1idx = idx(d1, context._dependent, context._independent)
    d2idx = idx(d2, context._dependent, context._independent)
    
    i1v = [0]*len(context._dependent)
    i2v = [0]*len(context._dependent)
    # pure function corresponds with all zeros
    if d1idx >= 0:
        i1v[d1idx] = 1
        i1 = vector(helpers.order_of_derivative(d1) + i1v)
    else:
        i1 = vector([0]*len(context._independent) + i1v)
    if d2idx >= 0:
        i2v[d2idx] = 1
        i2 = vector(helpers.order_of_derivative(d2) + i2v)
    else:
        i2 = vector([0]*len(context._independent) + i2v)
    r = context._weight(context._dependent, context._independent) * vector(i1-i2)
    for entry in r:
        if entry:
            return entry > 0
    return False


if __name__ == "__main__":
    doctest.testmod()
