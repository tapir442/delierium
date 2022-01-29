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
try:
    from delierium.DerivativeOperators import FrechetD
except ImportError:
    from DerivativeOperators import FrechetD


def prolongationFunction(f:list, x:list, order):
    result = f
    aux    = result[:]
    def outer(fun, l1, l2):
        return list(map(lambda v: fun(v[0], v[1]), product(l1,l2)))
    for i in range(order):
        aux = outer(diff, aux, x)[:]
        result += aux
    return(sorted(list(set(result))))

x, y, z = var("x y z")
f = function("f")(x, y, z)
print(prolongationFunction([f], (x, y, z), 2))


def infini(eq):
    pass



def prolongation(eq, dependent, independent):
    """

    Doctest stolen from Baumann pp.92/93
    >>> x = var('x')
    >>> u = function('u')
    >>> u_x = u(x)
    >>> f = function("f")
    >>> f_x = f(x, u(x), diff(u(x),x))
    >>> ppp = prolongation([f_x], [u], [x])
    >>> print(ppp[0].expand())
    -D[2](f)(x, u(x), diff(u(x), x))*diff(u(x), x)^2*D[1](xi_1)(x, u(x)) + D[2](f)(x, u(x), diff(u(x), x))*D[1](phi_1)(x, u(x))*diff(u(x), x) - D[2](f)(x, u(x), diff(u(x), x))*diff(u(x), x)*D[0](xi_1)(x, u(x)) + xi_1(x, u(x))*D[0](f)(x, u(x), diff(u(x), x)) + phi_1(x, u(x))*D[1](f)(x, u(x), diff(u(x), x)) + D[2](f)(x, u(x), diff(u(x), x))*D[0](phi_1)(x, u(x))
    >>> # this one here is from Baumann, p.93
    >>> f_x = f(x, u(x), diff(u(x),x),  diff(u(x), x ,x))
    >>> secondProlongation =  prolongation([f_x], [u], [x])[0].expand()
    >>> print(secondProlongation)
    -D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x)^3*D[1, 1](xi_1)(x, u(x)) + D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*D[1, 1](phi_1)(x, u(x))*diff(u(x), x)^2 - 2*D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x)^2*D[0, 1](xi_1)(x, u(x)) - D[2](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x)^2*D[1](xi_1)(x, u(x)) - 3*D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x)*diff(u(x), x, x)*D[1](xi_1)(x, u(x)) + 2*D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*D[0, 1](phi_1)(x, u(x))*diff(u(x), x) + D[2](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*D[1](phi_1)(x, u(x))*diff(u(x), x) + D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*D[1](phi_1)(x, u(x))*diff(u(x), x, x) - D[2](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x)*D[0](xi_1)(x, u(x)) - 2*D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x, x)*D[0](xi_1)(x, u(x)) - D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*diff(u(x), x)*D[0, 0](xi_1)(x, u(x)) + xi_1(x, u(x))*D[0](f)(x, u(x), diff(u(x), x), diff(u(x), x, x)) + phi_1(x, u(x))*D[1](f)(x, u(x), diff(u(x), x), diff(u(x), x, x)) + D[2](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*D[0](phi_1)(x, u(x)) + D[3](f)(x, u(x), diff(u(x), x), diff(u(x), x, x))*D[0, 0](phi_1)(x, u(x))
    """
    Depend = [d(*independent) for d in dependent]
    vars   = independent + Depend
    xi     = [function("xi_%s" % (j+1)) for j in range(len(independent))]
    eta    = []
    for i in range (len(dependent)):
        phi = function("phi_%s" % (i+1))
        eta.append(phi(*vars) -
                   sum(xi[j](*vars) *
                       Depend[i].diff(independent[j])
                       for j in range(len(independent))))
    test = list(map(lambda _: function("t_%s" % _),  range(len(Depend))))
    prolong = FrechetD(eq, dependent, independent, testfunction=test)
    prol = []
    for p in prolong:
        _p = []
        for l in p:
            i = 0
            def r0(*args):
                return eta[i](*independent)
            # this kinda counting is not very nice
            _p.append(l.substitute_function(test[i], r0))
            i += 1
        prol.append(sum(_ for _ in _p))
    prolong = prol[:]
    prol = []
    for j in range(len(prolong)):
        for i in range(len(independent)):
            prol.append(
                (prolong[j] +
                 xi[i](*vars) * sum(_.diff(independent[i]) for _ in eq).expand())
            )
    return prol

if __name__ == "__main__":
    import doctest
    doctest.testmod()
