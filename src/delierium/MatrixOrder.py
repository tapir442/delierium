#!/usr/bin/env python
# coding: utf-8

import sage.all
from sage.matrix.constructor import identity_matrix, matrix, Matrix
from sage.calculus.var import var, function
from sage.calculus.functional import diff
from sage.modules.free_module_element import vector
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.rational_field import QQ
from sage.misc.prandom import shuffle
from functools import cmp_to_key
import doctest


import functools
from delierium.helpers import eq, order_of_derivative, is_derivative, \
        is_function



#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#


def insert_row(M, k, row):
    # insert_row is only defined for integer matrices :(
    return matrix(M.rows()[:k]+[row]+M.rows()[k:])


def Mlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the lex ordering
    INPUT : funcs: a tuple of functions (tuple for caching reasons)
            vars: a tuple of variables
            these are not used directly , just their lenght is interasting, but
            so the consumer doesn't has the burden of computing the length of
            list but the lists directly from context
    OUTPUT: a matrix which when multiplying an augmented vector (func + var)
            gives the vector in lex order

            same applies mutatiss mutandis for Mgrlex and Mgrevlex

    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
    >>> Mlex ((f,g), [x,y,z])
    [0 0 0 2 1]
    [1 0 0 0 0]
    [0 1 0 0 0]
    [0 0 1 0 0]
    '''
    no_funcs = len(funcs)
    no_vars = len(vars)
    i = identity_matrix(no_vars)
    i = insert_row(i, 0, [0]*no_vars)
    for j in range(no_funcs, 0, -1):
        i = i.augment(vector([j] + [0]*no_vars))
    return i


def Mgrlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the grlex ordering
    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
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
    >>> Mgrevlex ((f,g,h), [x,y,z])
    [ 1  1  1  0  0  0]
    [ 0  0  0  3  2  1]
    [ 0  0 -1  0  0  0]
    [ 0 -1  0  0  0  0]
    [-1  0  0  0  0  0]
    '''
    no_funcs = len(funcs)
    no_vars = len(vars)
    l = matrix([1]*no_vars + [0]*no_funcs)
    l = insert_row(l, 1, vector([0]*no_vars + list(range(no_funcs, 0, -1))))
    for idx in range(no_vars):
        _v = vector([0]*(no_vars+no_funcs))
        _v[no_vars-idx-1] = -1
        l = insert_row(l, 2+idx, _v)
    return l


class Context:
    __slots__ = ["_dependent", "_independent", "_weight"]
    def __init__ (self, dependent, independent, weight = Mgrevlex):
        """ sorting : (in)dependent [i] > dependent [i+i]
        """
        # XXX maybe we can create the matrices here?
        self._independent = tuple(independent)
        self._dependent   = tuple((_.operator() if is_function(_) else _
                                   for _ in dependent))
        self._weight      = weight (self._dependent, self._independent)

    def gt(self, v1: vector, v2: vector) -> int:
        """Computes the weigthed difference vector of v1 and v2
        and returns 'True' if the first nonzero entry is > 0
        """
        r = self._weight * vector(v1-v2)
        for entry in r:
            if entry:
                return entry > 0
        return False        
        
_cache={}

#@functools.cache
def higher(d1, d2, context):
    # XXX move to context?
    '''Algorithm 2.3 from [Schwarz].'''
    @functools.cache
    def analyze_dterm(dd):
        # XXX use "_order" from DTerm directly
        if is_derivative(dd):
            f = dd.operator().function()
        elif is_function(dd):
            f = dd.operator()
        else:
            f = [_ for _ in dd.operands() if is_function(_) or is_derivative(_)][0]
            if is_derivative(f):
                f = f.operator().function()
        return f

    def idx(d):
        # faster than functools.cache
        return context._dependent.index(analyze_dterm(d))

    @functools.cache
    def get_derivative_vector(d):
        iv = [0]*len(context._dependent)
        iv[idx(d)] += 1
        return vector(order_of_derivative(d, len(context._independent)) + iv)
        
    i1 = get_derivative_vector(d1)
    i2 = get_derivative_vector(d2)    
    return context.gt(i1, i2)


@functools.cache
def sorter(d1, d2, context=Mgrevlex):
    '''sorts two derivatives d1 and d2 using the weight matrix M
    according to the sort order given in the tuple of  dependent and
    independent variables

    >>> x, y, z = var("x y z")
    >>> u = function ("u")(x,y,z)
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
    >>> s = sorted(l1, key=cmp_to_key(lambda item1, item2: sorter (item1, item2, ctxMlex)))
    >>> for _ in s: print(_)
    diff(u(x, y, z), z, z)
    diff(u(x, y, z), x, y, y, z)
    diff(u(x, y, z), x, x, z, z)
    diff(u(x, y, z), x, x, x)
    >>> s = sorted(l1, key=cmp_to_key(lambda item1, item2: sorter (item1, item2, ctxMgrlex)))
    >>> for _ in s: print(_)
    diff(u(x, y, z), z, z)
    diff(u(x, y, z), x, x, x)
    diff(u(x, y, z), x, y, y, z)
    diff(u(x, y, z), x, x, z, z)
    >>> s = sorted(l1, key=cmp_to_key(lambda item1, item2: sorter (item1, item2, ctxMgrevlex)))
    >>> for _ in s: print(_)
    diff(u(x, y, z), z, z)
    diff(u(x, y, z), x, x, x)
    diff(u(x, y, z), x, x, z, z)
    diff(u(x, y, z), x, y, y, z)
    '''
    if eq(d1, d2):
        return 1
    if higher(d1, d2, context):
        return 1
    return -1

if __name__ == "__main__":
    import doctest
    doctest.testmod()
