#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan  7 18:49:33 2022

@author: tapir
"""

import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.matrix.constructor import identity_matrix, matrix, Matrix
from sage.calculus.functional import diff
#try :
#    from delierium.helpers import (is_derivative, is_function, eq,
#                               order_of_derivative)
#    from delierium.MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
#except ModuleNotFoundError:
#    from helpers import (is_derivative, is_function, eq,
#                               order_of_derivative)
#    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex

import functools
from operator import mul
from IPython.core.debugger import set_trace
from collections.abc import Iterable
from more_itertools import powerset, bucket, flatten
from itertools import product, combinations, islice


def prolongationFunction(f:list, x:list, order):
    result = f
    aux    = result[:]
    def outer(fun, l1, l2):
        return list(map(lambda v: fun(v[0], v[1]), product(l1,l2)))
    for i in range(order):
        aux = outer(diff, aux, x)[:]
        result += aux
    return(sorted(list(set(result))))

x,y,z=var("x y z")
f = function("f")(x,y,z)
print(prolongationFunction([f], (x, y,z), 2))


def FrechetD (support, dependVar, independVar, testfunction):
    """Computes Frechet derivative
    >>> t, x = var ("t x")
    >>> v  = function ("v")
    >>> u  = function ("u")
    >>> w1 = function ("w1")
    >>> w2 = function ("w2")
    >>> eqsys = [diff(v(x,t), x) - u(x,t), diff(v(x,t), t) - diff(u(x,t), x)/(u(x,t)**2)]
    >>> FrechetD (eqsys, [u,v], [x,t], [w1,w2])
    [                                                          -w1(x, t)                                                   diff(w2(x, t), x)]
    [2*w1(x, t)*diff(u(x, t), x)/u(x, t)^3 - diff(w1(x, t), x)/u(x, t)^2                                                   diff(w2(x, t), t)]
    """
    frechet = []
    eps = var("eps")
    for j in range(len(support)):
        deriv = []
        for i in range(len(support)):
            def r0(*args):
                return dependVar[i](*independVar) + testfunction[i](*independVar) * eps
            #def _r0(*args):
            #    # this version has issues as it always uses w2 ?!? investigate further
            #    # when time and motivation. Online version on asksage works perfectly
            #    return dependVar[i](*independVar)+ testfunction[i](*independVar) * eps
            #r0 = function('r0', eval_func=_r0)
            s = support[j].substitute_function(dependVar[i], r0)
            deriv.append(diff(s, eps).subs({eps: 0}))
        frechet.append(deriv)
    return frechet




t, x, y = var ("t x y")
v  = function ("v")(x,y,t)
u  = function ("u")(x,y,t)
z  = function ("z")(x,y,t)
w1 = function ("w1")(x,y,t)
w2 = function ("w2")(x,y,t)
w3 = function ("w3")(x,y,t)
print("A"*99)
expr1 = diff(v, x, y) - u
print(expr1)
eqsys1 = [expr1, diff(v, t, y) - diff(u, x)/(u**2), diff(z, t, t)- (z**2)-u]; eqsys1
nn=FrechetD (eqsys1, [u,v,z], [x,y,t], [w1,w2,w3])
print(nn)


def infini(eq):
    pass



def prolongation(eq, dependent, independent):
    """
    >>> x = var('x')
    >>> u = function('u')(x)
    >>> f = function("f")(x, u, diff(u,x))
    """
    mainrule = []
    subrule = []

    Depend = [d(*independent) for d in dependent]
    vars   = independent + Depend
    xi     = [function("xi_%s" % (j+1)) for j in range(len(independent))]
    eta    = []
    for i in range (len(dependent)):
        _ = function("phi_%s" % (i+1))
        eta.append(_(*vars) -
                   sum(xi[j](*vars) *
                       Depend[i].diff(independent[j])
                       for j in range(len(independent))))
    maus = []
    for i in range(len(Depend)):
        maus.append(var("t_%s" % i))
    subrule = []
    for i in range(len(eta)):
        subrule.append(function("_")(*([eta[i]] + independent)))
    print(subrule)
    prolong = FrechetD(eq, dependent, independent, testfunction=maus)
    print (prolong)
    prolong.extend(flatten(subrule))
    prolong = sum(_ for _ in prolong)
    prol = []
    for i in range(len(prolong)):
        prol.append(
            prolong[i] +
            sum(xi[i] * eq.diff(independent[i]))
            )
    return prol

x = var('x')
u = function('u')(x)
f = function("f")(x, u, diff(u,x))

#set_trace()
ppp = prolongation([f], [u], [x])
print(ppp)

if __name__ == "__main__":
    import doctest
    doctest.testmod()
