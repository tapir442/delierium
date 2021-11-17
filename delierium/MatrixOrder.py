#!/usr/bin/env python
# coding: utf-8

from sage.all import *
from functools import cache
import delierium.helpers as helpers
import doctest
#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#

def Mlex(funcs, vars):
    '''Generates the "cotes" according to Riquier for the lex ordering
    '''
    m = len(funcs)
    n = len(vars)
    i = matrix.identity(n)
    i = i.insert_row(0, [Integer(0)]*n)
    for j in range(m, 0, -1):
        i = i.augment(vector([j] + [Integer(0)]*n))
    return i


def Mgrlex(funcs, vars):
    m = Mlex(funcs,vars)
    m = m.insert_row(0, [Integer(1)]*len(vars)+[Integer(0)]*len(funcs))
    return m

def Mgrevlex(funcs, vars):
    m = len(funcs)
    n = len(vars)
    l = Matrix([Integer(1)]*n + [Integer(0)]*m)
    l = l.insert_row(1, vector([0]*n + [Integer(_) for _ in range(m,0,-1)]))
    for idx in range(n):
        _v = vector([Integer(0)]*(n+m))
        _v[n-idx-1] = -1
        l = l.insert_row(2+idx, _v)
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


@cache
def higher (d1 ,d2, context):
    # XXX move to context?
    '''Algorithm 2.3 from [Schwarz]'''
    @cache        
    def idx (d):
        '''helper function
        returns the index of the function name of the given derivative 'd' within
        the tuple of dependent variables
    
        >>> from delierium.MatrixOrder import idx
        >>> vars = var("x y z")
        >>> f=function("f")(*vars)
        >>> g=function("g")(*vars)
        >>> h=function("h")(*vars)    
        >>> df = diff (f, x,y)
        >>> dg = diff (g, z,x)
        >>> dh = diff (h,x)
        >>> idx (df, (f,g,h))
        0
        >>> idx (df, (g,h,f))
        2
        >>> idx (df, (h,f,g))
        1
        >>> idx (f, (f,g,h))
        -1
        '''
        if helpers.is_derivative (d):
            return context._dependent.index(d.operator().function()(*list(context._independent)))
        return -1

    d1idx = idx(d1)
    d2idx = idx(d2)
    
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
    r = context._weight * vector(i1-i2)
    for entry in r:
        if entry:
            return entry > 0
    return False

@cache
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
    if d1 == d2:
        return 0
    if higher (d1, d2, context):
        return 1
    return -1

if __name__ == "__main__":
    import doctest
    doctest.testmod()
