#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Jan 18 13:28:44 2022

@author: tapir
"""
#get_ipython().run_line_magic("display", " latex")
import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.calculus.functional import diff
try :
    from delierium.helpers import (is_derivative, is_function, eq,
                               order_of_derivative)
    from delierium.MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
except ModuleNotFoundError:
    from helpers import (is_derivative, is_function, eq,
                               order_of_derivative)
    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex

import functools
from operator import mul
from IPython.core.debugger import set_trace
from collections.abc import Iterable
from more_itertools import powerset, bucket, flatten
from itertools import product, combinations, islice


def FrechetD (support, dependVar, independVar, testfunction):
    frechet = []
    var ("eps")
    for j in range (len(support)):
        deriv = []
        for i in range (len(support)):
            def r0(*args):
                return dependVar[i](*independVar)+ testfunction[i](*independVar) * eps
            #def _r0(*args):
            #    # this version has issues as it always uses w2 ?!? investigate further
            #    # when time and motivation. Online version on asksage works perfectly
            #    return dependVar[i](*independVar)+ testfunction[i](*independVar) * eps
            #r0 = function('r0', eval_func=_r0)
            s  =  support[j].substitute_function (dependVar[i], r0)
            deriv.append (diff(s, eps).subs ({eps: 0}))
        frechet.append (deriv)
    return frechet



var ("t x")
v  = function ("v")
u  = function ("u")
w1 = function ("w1")
w2 = function ("w2")
eqsys = [diff(v(x,t), x) - u(x,t), diff(v(x,t), t) - diff(u(x,t), x)/(u(x,t)**2)]


eqsys


FrechetD (eqsys, [u,v], [x,t], [w1,w2])


var ("t x y")
v  = function ("v")
u  = function ("u")
z  = function ("z")
w1 = function ("w1")
w2 = function ("w2")
w3 = function ("w3")
eqsys1 = [diff(v(x,y,t), x, y) - u(x,y,t), diff(v(x,y,t), t, y) - diff(u(x,y,t), x)/(u(x,y,t)**2), diff(z(x,y,t), t, t)- (z(x,y,t)**2)-u(x,y,t)]; eqsys


print (FrechetD (eqsys1, [u,v,z], [x,y,t], [w1,w2,w3]))


def AdjointFrechetD(support, dependVar, independVar, testfunction):
    frechet = FrechetD(support, dependVar, independVar, testfunction)


