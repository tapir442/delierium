#!/usr/bin/env python
# coding: utf-8

from functools import lru_cache

from sage.all import *
from sage.modules.free_module_element import vector
from sage.matrix.constructor import matrix
from sage.symbolic.function_factory import function
from sage.calculus.var import var
try:
    from delierium.helpers import *
except (ImportError, ModuleNotFoundError):
    print ("damned")
    from helpers import *    

#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#

# insert_row is only defined for integer matrices :(
def insert_row(M,k,row):
    return matrix(M.rows()[:k]+[row]+M.rows()[k:])


def Mlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the lex ordering
    INPUT : funcs: a list of functions
            vars: a list of variables
            these are not used directly , just their lenght is interasting, but so the
            consumer doesn't has the burden of computing the length of list but
            the lists directly from contex
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
    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
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


def idx(d, dependent, independent):
    '''helper function'''
    # this caching gains about 30 % of runtime,
    # but still pretty slow.
    if is_derivative(d):
        return dependent.index(d.operator().function()(*list(independent)))
    return -1


class Context:
    # XXX replace by named tuple? or attr.ib
    def __init__(self, dependent, independent, weight=Mlex):
        """ sorting : (in)dependent [i] > dependent [i+i]        
        """
        # XXX maybe we can create the matrices here?
        self._independent = tuple(independent)
        self._dependent = tuple(dependent)
        self._weight = weight
        self._basefield = None # PolynomialRing(QQ, independent)


def higher(d1, d2, context):
    '''Algorithm 2.3 from [Schwarz]
    
    Given two derivatives d1 and d2 and a weight matrix it returns
    True if d2 does not preceed d1 
    '''
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
        i1 = vector(order_of_derivative(d1) + i1v)
    else:
        i1 = vector([0]*len(context._independent) + i1v)
    if d2idx >= 0:
        i2v[d2idx] = 1
        i2 = vector(order_of_derivative(d2) + i2v)
    else:
        i2 = vector([0]*len(context._independent) + i2v)
    r = context._weight(context._dependent,
                        context._independent) * vector(i1-i2)
    for entry in r:
        if entry:
            return entry > 0
    return False


if __name__ == "__main__":
    import doctest
    doctest.testmod()
