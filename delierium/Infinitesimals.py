#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan  7 18:49:33 2022

@author: tapir
"""

from itertools import product
from anytree import Node, RenderTree, AnyNode, NodeMixin, PreOrderIter

import sage.all
from sage.calculus.functional import diff
from sage.calculus.var import function, var
from sage.misc.html import html
from sage.symbolic.operators import FDerivativeOperator
from sage.symbolic.relation import solve

from delierium.DerivativeOperators import FrechetD
from delierium.helpers import latexer, ExpressionTree

from IPython.core.debugger import set_trace
from IPython.display import Math

def prolongationFunction(f: list, x: list, order) -> list:
    '''
    >>> x, y, z = var("x y z")
    >>> f = function("f")(x, y, z)
    >>> set(prolongationFunction([f], [x, y, z], 2)) == set(
    ... [diff(f, z, z), diff(f, y), diff(f, x),
    ... diff(f, z), f, diff(f, x, z),
    ... diff(f, x, y), diff(f, x, x),
    ... diff(f, y, y), diff(f, y, z)])
    True
    '''
    result = f
    aux    = result[:]

    def outer(fun, l1, l2):
        return list(map(lambda v: fun(v[0], v[1]), product(l1, l2)))
    for i in range(order):
        result += (aux:= outer(diff, aux, x)[:])
    return(sorted(list(set(result))))

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
    >>> # Baumann's example p. 94
    >>> x = var('x')
    >>> y = function('y')
    >>> print(prolongation([diff(y(x),x,2)], [y], [x])[0].expand())
    -D[1, 1](xi_1)(x, y(x))*diff(y(x), x)^3 + D[1, 1](phi_1)(x, y(x))*diff(y(x), x)^2 - 2*D[0, 1](xi_1)(x, y(x))*diff(y(x), x)^2 - 3*D[1](xi_1)(x, y(x))*diff(y(x), x)*diff(y(x), x, x) + 2*D[0, 1](phi_1)(x, y(x))*diff(y(x), x) - D[0, 0](xi_1)(x, y(x))*diff(y(x), x) + D[1](phi_1)(x, y(x))*diff(y(x), x, x) - 2*D[0](xi_1)(x, y(x))*diff(y(x), x, x) + D[0, 0](phi_1)(x, y(x))
    """
    Depend = [d(*independent) for d in dependent]
    vars   = independent + Depend
    xi     = [function("xi_%s" % (j+1), latex_name = r"\xi_{i+1}") for j in range(len(independent))]
    eta    = []
    for i in range(len(dependent)):
        phi = function("phi_%s" % (i+1), latex_name = r"\phi_{i+1}")
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
            _p.extend([l.substitute_function(test[i], _e.function()) for _e in  eta])
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

def prolongationODE(equations, dependent, independent):
    """
    Baumann, ex 1, pp.136
    >>> x    = var("x")
    >>> u    = function('u')
    >>> F    = function("F")
    >>> ode3 = diff(u(x), x) - F(u(x),x)
    >>> prolongationODE(ode3,u,x)
    [xi(u(x), x)*D[0](F)(u(x), x)*diff(u(x), x) - diff(u(x), x)^2*D[0](xi)(u(x), x) - (D[0](F)(u(x), x)*diff(u(x), x) + D[1](F)(u(x), x) - diff(u(x), x, x))*xi(u(x), x) - phi(u(x), x)*D[0](F)(u(x), x) + D[0](phi)(u(x), x)*diff(u(x), x) - xi(u(x), x)*diff(u(x), x, x) - diff(u(x), x)*D[1](xi)(u(x), x) + D[1](phi)(u(x), x)]
    """
    vars     = [dependent(independent), independent]
    xi       = function("xi", latex_name=r"\xi")
    phi      = function("phi", latex_name=r"\phi")
    eta      = phi(*vars) - xi(*vars) * diff(dependent(independent), independent)
    test     = function('test')
    prolong  = FrechetD([equations], [dependent], [independent], testfunction=[test])
    prol     = []
    for p in prolong:
        _p = [l.substitute_function(test, eta.function()).expand() for l in p]
        prol.append(sum(_ for _ in _p))
    prolong = prol[:]
    prol = []
    prol    = [prolong[j] + xi(*vars) * equations.diff(independent)
               for j in range(len(prolong))
               ]
    return prol


from collections import namedtuple

term = namedtuple("term", ["power", "coeff"])
import types

def infinitesimalsODE (ode, dependent, independent, *args, **kw):
    """
    Computes the overdetermined system which is computed from the prolongation
    of an ODE of order > 1
    
    Only the left hand sides of the equations is returned, for further manipulation
    one has to add ' == 0' herself
    
    Real infinitesimals will follow soon
    
    >>> # Arrigo Example 2.20
    >>> x   = var('x')
    >>> y   = function('y')
    >>> ode = diff(y(x), x, 3) + y(x) * diff(y(x), x, 2)
    >>> inf = infinitesimalsODE(ode, y, x)
    >>> for _ in inf: 
    ...     print(_)
    -3*D[0](xi)(y(x), x)
    -6*D[0, 0](xi)(y(x), x)
    y(x)*D[0](xi)(y(x), x) + 3*D[0, 0](phi)(y(x), x) - 9*D[0, 1](xi)(y(x), x)
    y(x)*D[1](xi)(y(x), x) + phi(y(x), x) + 3*D[0, 1](phi)(y(x), x) - 3*D[1, 1](xi)(y(x), x)
    -D[0, 0, 0](xi)(y(x), x)
    -y(x)*D[0, 0](xi)(y(x), x) + D[0, 0, 0](phi)(y(x), x) - 3*D[0, 0, 1](xi)(y(x), x)
    y(x)*D[0, 0](phi)(y(x), x) - 2*y(x)*D[0, 1](xi)(y(x), x) + 3*D[0, 0, 1](phi)(y(x), x) - 3*D[0, 1, 1](xi)(y(x), x)
    2*y(x)*D[0, 1](phi)(y(x), x) - y(x)*D[1, 1](xi)(y(x), x) + 3*D[0, 1, 1](phi)(y(x), x) - D[1, 1, 1](xi)(y(x), x)
    y(x)*D[1, 1](phi)(y(x), x) + D[1, 1, 1](phi)(y(x), x)
    """
    prolongation = prolongationODE(ode, dependent, independent)[0].expand()
    tree = ExpressionTree(prolongation)         
    mine = [_ for _ in tree.diffs if _.operator().function() in [dependent]]
    order= max([len(_.operator().parameter_set()) for _ in mine])
    #display(Math(latexer(prolongation)))
    s1  = solve(ode==0, diff(dependent(independent),independent, order))
    ode1 = prolongation.subs({s1[0].lhs() : s1[0].rhs()}).simplify()
    #display(Math(latexer(ode1)))
    tree = ExpressionTree(ode1)    
    l = [_ [0] for _ in ode1.coefficients(diff(dependent(independent), independent, order))]
    equations = []
    e         = l[0]
    all_this_stuff = set()
    for node in PreOrderIter(tree.root):
        # powercollector: an array which stores powers of derivatives
        # the index is the(reversed) order, the value is the power
        # of the derivative.
        # Example: we have an ODE of order three. The prolongation and 
        # substitution step produces 'ode1' which is now of reduced order
        # two. So we can have differentials of order one and to, so we need an
        # array of lenght two which is initialized with zeroes. A term like
        #    diff(y, x)^5 * diff(y, x, x)^2 
        # will create the entry 
        #    [2,5]
        # The higher order (=2) has power 2, so the first entry (=highest order)
        # will be set to 2, the lowest order(=1) has power 5, so the index 1 contains
        # the power 5. This way we now have on ordered list which than can be 
        # looped over from highest_order^highest_power to lowest_order^lowest_power
        # to factor out the derivatives to get the determining equations
        powercollector = [0]*(order-1)
        v = node.value
        if v.operator() == sage.symbolic.operators.add_vararg:
            continue
        if v.operator() is None:
            continue
        if isinstance(v.operator(), FDerivativeOperator):
            # standalone diff operator
            if v.operands()[0] != independent:
                # differential coming from prolongation, ignore
                continue           
            powercollector[order - len(v.operator().parameter_set())-1] = 1
            all_this_stuff.add(term(tuple(powercollector), v))
            continue
        if v.operator() is sage.symbolic.operators.mul_vararg:
            # the factors containing derivatives can be combined multiplicatively
            # We will analize them factor by factor, put powers and orders into
            # 'power_collector', and multiply these factors together into 'local_term',
            # ans store both together into 'all_this_stuff'
            local_term    = 1
            for w in v.operands():
                if isinstance(w.operator(), FDerivativeOperator):
                    if w.operands()[0] != independent:
                        # differential coming from prolongation, ignore                        
                        continue
                    powercollector[order - len(w.operator().parameter_set())-1] = 1
                    local_term *= w
                if isinstance(w.operator(), types.BuiltinFunctionType):
                    if w.operator().__qualname__ != 'pow':
                        continue
                    if isinstance (w.operands()[0].operator(), FDerivativeOperator):
                        if w.operands()[0].operands()[0] != independent:
                            # differential coming from prolongation, ignore                            
                            continue
                        local_term *= w
                        powercollector[order - len(w.operands()[0].operator().parameter_set())-1] = w.operands()[-1]
                        
            if powercollector != [0]*(order-1):
                all_this_stuff.add(term(tuple(powercollector), local_term))
    for _ in reversed(sorted(all_this_stuff)):
        new = e.coefficient(_.coeff)
        equations.append(new)
        e = (e - new * _.coeff).expand()
    equations.append(e)
    return equations




if __name__ == "__main__":
    import doctest
    doctest.testmod()
