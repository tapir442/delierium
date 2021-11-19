#!/usr/bin/env python
# coding: utf-8

from sage.all import *
from sage.modules.free_module_element import vector
from sage.matrix.constructor import matrix
from sage.symbolic.function_factory import function
from sage.calculus.var import var
from .helpers import is_derivative, order_of_derivative

import functools 
    
#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#

# insert_row is only defined for integer matrices :(
def insert_row(M,k,row):
    return matrix(M.rows()[:k]+[row]+M.rows()[k:])


def Mlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the lex ordering
    INPUT : funcs: a tuple of functions (tuple for caching reasons)
            vars: a tuple of variables
            these are not used directly , just their lenght is interasting, but so the
            consumer doesn't has the burden of computing the length of list but
            the lists directly from context
    OUTPUT: a matrix which when multiplying an augmented vector (func + var) gives
            the vector in lex order
            
            same applies mutas mutandis for Mgrlex and Mgrevlex
            
    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
    >>> from delierium.MatrixOrder import Mlex
    >>> Mlex ((f,g), [x,y,z])
    [0 0 0 2 1]
    [1 0 0 0 0]
    [0 1 0 0 0]
    [0 0 1 0 0]    
    '''
    m = len(funcs)
    n = len(vars)
    i = matrix.identity(n)
    i = insert_row(i, 0, [0]*n)
    for j in range(m, 0, -1):
        i = i.augment(vector([j] + [0]*n))
    return i


def Mgrlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the grlex ordering
    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
    >>> from delierium.MatrixOrder import Mgrlex
    >>> Mgrlex ((f,g,h), [x,y,z])
    [1 1 1 0 0 0]
    [0 0 0 3 2 1]
    [1 0 0 0 0 0]
    [0 1 0 0 0 0]
    [0 0 1 0 0 0]    
    '''
    m = Mlex(funcs, vars)
    m = insert_row(m, 0, [1]*len(vars)+[0]*len(funcs))
    return m


def Mgrevlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the grevlex ordering
    >>> _ = var ("x y z")
    >>> f = function("f")(*_)
    >>> g = function("g")(*_)
    >>> h = function("h")(*_)
    >>> from delierium.MatrixOrder import Mgrevlex
    >>> Mgrevlex ((f,g,h), [x,y,z])
    [ 1  1  1  0  0  0]
    [ 0  0  0  3  2  1]
    [ 0  0 -1  0  0  0]
    [ 0 -1  0  0  0  0]
    [-1  0  0  0  0  0]
    '''
    
    m = len(funcs)
    n = len(vars)
    l = Matrix([1]*n + [0]*m)
    l = insert_row(l, 1, vector([0]*n + [_ for _ in range(m, 0, -1)]))
    for idx in range(n):
        _v = vector([0]*(n+m))
        _v[n-idx-1] = -1
        l = insert_row(l, 2+idx, _v)
    return l


class Context:
    # XXX replace by named tuple? or attr.ib
    def __init__ (self, dependent, independent, weight = Mlex):
        """ sorting : (in)dependent [i] > dependent [i+i]        
        """
        self._independent = tuple(independent)
        self._dependent   = tuple(dependent)
        self._weight      = weight (self._dependent, self._independent)
        self._basefield   = PolynomialRing(QQ, independent)

    @functools.cache
    def higher (self, d1 ,d2):
        '''Algorithm 2.3 from [Schwarz]    
        Given two derivatives d1 and d2 and a weight matrix it returns
        True if d2 does not preceed d1 
        '''
            
        @functools.cache
        def idx (d):
            if is_derivative (d):
                return self._dependent.index(d.operator().function()(*list(self._independent)))
            return -1
        if d1 == d2:
            return 0
        d1idx = idx(d1)
        d2idx = idx(d2)
    
        i1v = [0]*len(self._dependent)
        i2v = [0]*len(self._dependent)
        # pure function corresponds with all zeros
        if d1idx >= 0:
            i1v[d1idx] = 1
            i1 = vector(order_of_derivative(d1) + i1v)
        else:
            i1 = vector([0]*len(self._independent) + i1v)
        if d2idx >= 0:
            i2v[d2idx] = 1
            i2 = vector(order_of_derivative(d2) + i2v)
        else:
            i2 = vector([0]*len(self._independent) + i2v)
        r = self._weight * vector(i1-i2)
        for entry in r:
            if entry:
                if entry > 0:
                    return 1
                else:
                    return -1
        return -1


def sorter (d1, d2, context = Mlex):
    '''sorts two derivatives d1 and d2 using the weight matrix M
    according to the sort order given in the tuple of  dependent and independent variables
    
    >>> x, y, z = var("x y z")
    >>> u = function ("u")(x,y,z)
    >>> from functools import cmp_to_key
    >>> from delierium.MatrixOrder import higher, Context, Mgrevlex, Mlex, Mgrlex, sorter
    >>> from delierium.JanetBasis import DTerm
    >>> ctxMlex = Context((u,),(x,y,z), Mlex)
    >>> ctxMgrlex = Context((u,),(x,y,z), Mgrlex)
    >>> ctxMgrevlex = Context((u,),(x,y,z), Mgrevlex)
    >>> # this is the standard example stolen from wikipedia
    >>> u0 = diff(u,x,3)
    >>> u1 = diff(u,z,2)
    >>> u2 = diff(u,x,y,y,z)
    >>> u3 = diff(u, x,x,z,z)
    >>> l1 = [u0, u1,u2,u3]
    >>> shuffle(l1)
    >>> sorted(l1, key=cmp_to_key(lambda item1, item2: sorter (item1, item2, ctxMlex)))
    [diff(u(x, y, z), z, z),
     diff(u(x, y, z), x, y, y, z),
     diff(u(x, y, z), x, x, z, z),
     diff(u(x, y, z), x, x, x)]
    >>> sorted(l1, key=cmp_to_key(lambda item1, item2: sorter (item1, item2, ctxMgrlex)))
    [diff(u(x, y, z), z, z),
     diff(u(x, y, z), x, x, x),
     diff(u(x, y, z), x, y, y, z),
     diff(u(x, y, z), x, x, z, z)]    
    >>> sorted(l1, key=cmp_to_key(lambda item1, item2: sorter (item1, item2, ctxMgrevlex)))
    [diff(u(x, y, z), z, z),
     diff(u(x, y, z), x, x, x),
     diff(u(x, y, z), x, x, z, z),
     diff(u(x, y, z), x, y, y, z)]
    '''
    if higher (d1, d2, context):
        return 1
    return -1

if __name__ == "__main__":
    import doctest
    doctest.testmod()
