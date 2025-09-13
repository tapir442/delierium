#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan  7 18:49:33 2022

@author: tapir
"""

import types, os
from collections import namedtuple
from itertools import product




from sympy import srepr

from sympy.simplify import collect

from delierium.DerivativeOperators import FrechetD
from delierium.JanetBasis import Janet_Basis
from delierium.helpers import ExpressionTree

from more_itertools import bucket, flatten, powerset


os.environ["USE_SYMENGINE"] = "1"
from sympy.core.backend import *

def prolongationFunction(f: list, x: list, order) -> list:
    '''
    >>> x, y, z = symbols("x y z")
    >>> f = Function("f")(x, y, z)
    >>> set(prolongationFunction([f], [x, y, z], 2)) == set(
    ... [diff(f, z, z), diff(f, y), diff(f, x),
    ... diff(f, z), f, diff(f, x, z),
    ... diff(f, x, y), diff(f, x, x),
    ... diff(f, y, y), diff(f, y, z)])
    True
    '''
    result = f
    aux = result[:]

    def outer(fun, l1, l2):
        return list(map(lambda v: fun(v[0], v[1]), product(l1, l2)))
    for i in range(order):
        result += (aux := outer(diff, aux, x)[:])
    return set(result)


def infini(eq):
    pass


def prolongation(eq, dependent, independent):
    """

    Doctest stolen from Baumann pp.92/93
    >>> x = symbols('x')
    >>> u = Function('u')
    >>> u_x = u(x)
    >>> f = Function("f")
    >>> fx = f(x, u(x), Derivative(u(x), x))
    >>> ppp = prolongation([fx], [u], [x])
    >>> print(ppp[0].expand())
    -D[2](f)(x, u(x), Derivative(u(x), x))*Derivative(u(x), x)^2*D[1](xi_1)(x, u(x)) + D[2](f)(x, u(x), Derivative(u(x), x))*D[1](phi_1)(x, u(x))*Derivative(u(x), x) - D[2](f)(x, u(x), Derivative(u(x), x))*Derivative(u(x), x)*D[0](xi_1)(x, u(x)) + xi_1(x, u(x))*D[0](f)(x, u(x), Derivative(u(x), x)) + phi_1(x, u(x))*D[1](f)(x, u(x), Derivative(u(x), x)) + D[2](f)(x, u(x), Derivative(u(x), x))*D[0](phi_1)(x, u(x))
    >>> # this one here is from Baumann, p.93
    >>> f_x = f(x, u(x), diff(u(x),x),  diff(u(x), x ,x))
    >>> # Baumann's example p. 94
    >>> x = symbols('x')
    >>> y = Function('y')
    >>> print(prolongation([diff(y(x),x,2)], [y], [x])[0].expand())
    -D[1, 1](xi_1)(x, y(x))*Derivative(y(x), x)^3 + D[1, 1](phi_1)(x, y(x))*Derivative(y(x), x)^2 - 2*D[0, 1](xi_1)(x, y(x))*Derivative(y(x), x)^2 - 3*D[1](xi_1)(x, y(x))*Derivative(y(x), x)*Derivative(y(x), x, x) + 2*D[0, 1](phi_1)(x, y(x))*Derivative(y(x), x) - D[0, 0](xi_1)(x, y(x))*Derivative(y(x), x) + D[1](phi_1)(x, y(x))*Derivative(y(x), x, x) - 2*D[0](xi_1)(x, y(x))*Derivative(y(x), x, x) + D[0, 0](phi_1)(x, y(x))
    """
    Depend = [d(*independent) for d in dependent]
    vars = independent + Depend
    print(Function.__doc__)
    xi = [Function("xi_%s" % (j+1), latex_name = r"\xi_{i+1}")(*vars) for j in range(len(independent))]
    eta = []
    for i in range(len(dependent)):
        phi = Function(f"phi_{i+1}", latex_name = fr"\phi_{i+1}")(*vars)
        eta.append(phi -
                   sum(xi[j] *
                       Depend[i].diff(independent[j])
                       for j in range(len(independent))))
    test = list(map(lambda _: Function("t_%s" % _)(*independent),  range(len(Depend))))
    print("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")
    from pprint import pprint
    pprint(locals())
    print(f"{Function=}")
    for _ in locals():
        print(f"{_=}, {_.__class__=}")
    print(f"{eq=}")
    prolong = FrechetD(eq, dependent, independent, testfunction=test)
    prol = []
    for p in prolong:
        _p = []
        for l in p:
            print(f"   ===> {l=}, {l.__class__=}")
            print(f"   ===> {test[i]=}")
            _p.extend([l.doit().xreplace({test[i]:  _e}) for _e in eta])
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


def prolongationODE(equations,
                    dependent,
                    independent,
                    infinitesimals=None):
    """
    >>> # Baumann, ex 1, pp.136
    >>> x    = symbols("x")
    >>> u    = Function('u')
    >>> F    = Function("F")
    >>> ode3 = diff(u(x), x) - F(u(x),x)
    >>> X=Function('X')
    >>> Y=Function('Y')
    >>> prolongationODE(ode3,u,x, infinitesimals=(X,Y))
    [X(u(x), x)*D[0](F)(u(x), x)*diff(u(x), x) - D[0](X)(u(x), x)*diff(u(x), x)^2 - (D[0](F)(u(x), x)*diff(u(x), x) + D[1](F)(u(x), x) - diff(u(x), x, x))*X(u(x), x) - Y(u(x), x)*D[0](F)(u(x), x) - D[1](X)(u(x), x)*diff(u(x), x) + D[0](Y)(u(x), x)*diff(u(x), x) - X(u(x), x)*diff(u(x), x, x) + D[1](Y)(u(x), x)]
    >>> # Baumann, ex 2, p.137
    >>> g = Function("g")
    >>> f = Function("f")
    >>> ode4 = diff(u(x),x)-g(u(x))*f(x)
    >>> p = prolongationODE(ode4,u,x)[0].expand()
    >>> sol = solve(ode4, diff(u(x), x))
    >>> p = p.subs({sol[0].lhs() : sol[0].rhs()})
    >>> print(p.expand())
    -f(x)^2*g(u(x))^2*D[0](xi)(u(x), x) - g(u(x))*xi(u(x), x)*diff(f(x), x) - f(x)*phi(u(x), x)*D[0](g)(u(x)) + f(x)*g(u(x))*D[0](phi)(u(x), x) - f(x)*g(u(x))*D[1](xi)(u(x), x) + D[1](phi)(u(x), x)
    """
    from IPython.core.debugger import set_trace; set_trace()
    vars     = [dependent(independent), independent]
    if infinitesimals is None:
        infinitesimals = (Function("xi", latex_name=r"\xi"), Function("phi", latex_name=r"\phi"))
    xi, phi = infinitesimals
    eta=phi(*vars) - xi(*vars) * diff(dependent(independent), independent)
    test=Function('test')
    prolong=FrechetD([equations], [dependent], [independent], testfunction=[test])
    prol=[]
    for p in prolong:
        _p = (_.subs({test(independent): eta}).expand() for _ in p)
        prol.append(sum(_ for _ in _p))
    result = list(map (lambda _ : _ + xi(*vars) * equations.diff(independent), prol))
    return result

term = namedtuple("term", ["power", "coeff"])

def overdeterminedSystemODE (ode,
                       dependent,
                       independent,
                       infinitesimals=None
                       , *args, **kw):
    """Computes the overdetermined system which is computed from the prolongation
    of an ODE of order > 1

    Parameters
    ----------
    ode: a sympy expression as the left side of '<expr> == 0'. No need to
        add " == 0'!!
    dependent: the name of the dependent variable, i.e. the unknown function
    independent:
        the name of the independent variable
    infinitesimals: ordered pair of sympy variables, to be used as the names
        for the infinitesimals, to avoid potential name clashes with  variables in your
        application. If not specified, 'xi' and 'phi' are used as the defaults

    Returns
    -------
    list
        a list of expressions, each expression to be interpreted as left side of an
        'expr' == 0. For further manipulation ane has to add ' == 0'.


    >>> # Arrigo Example 2.20
    >>> x   = symbols('x')
    >>> y   = Function('y')
    >>> ode = diff(y(x), x, 3) + y(x) * diff(y(x), x, 2)
    >>> X=Function('X')
    >>> Y=Function('Y')
    >>> inf = overdeterminedSystemODE(ode, y, x, infinitesimals=(X,Y))
    >>> print(f"{inf=}")
    >>> for _ in inf:
    ...     print(_)
    -3*D[0](X)(y(x), x)
    -6*D[0, 0](X)(y(x), x)
    y(x)*D[0](X)(y(x), x) - 9*D[0, 1](X)(y(x), x) + 3*D[0, 0](Y)(y(x), x)
    y(x)*D[1](X)(y(x), x) + Y(y(x), x) - 3*D[1, 1](X)(y(x), x) + 3*D[0, 1](Y)(y(x), x)
    -D[0, 0, 0](X)(y(x), x)
    -y(x)*D[0, 0](X)(y(x), x) - 3*D[0, 0, 1](X)(y(x), x) + D[0, 0, 0](Y)(y(x), x)
    -2*y(x)*D[0, 1](X)(y(x), x) + y(x)*D[0, 0](Y)(y(x), x) - 3*D[0, 1, 1](X)(y(x), x) + 3*D[0, 0, 1](Y)(y(x), x)
    -y(x)*D[1, 1](X)(y(x), x) + 2*y(x)*D[0, 1](Y)(y(x), x) - D[1, 1, 1](X)(y(x), x) + 3*D[0, 1, 1](Y)(y(x), x)
    y(x)*D[1, 1](Y)(y(x), x) + D[1, 1, 1](Y)(y(x), x)
    """

    if infinitesimals is None:
        infinitesimals = (Function("xi", latex_name=r"\xi"), Function("phi", latex_name=r"\phi"))
    prolongation = prolongationODE(ode, dependent, independent, infinitesimals=infinitesimals)[0].expand()
    print(f"{prolongation=}")
    os.environ["USE_SYMENGINE"] = "1"    
    from sympy import preorder_traversal
    from sympy.core.function import Derivative
    from sympy import solve
    from sympy.solvers.deutils import ode_order
    lhs = diff(dependent(independent),independent, ode_order(ode, dependent))
    print(f"{lhs=}")
    
    s1 = solve(ode, diff(dependent(independent),independent, ode_order(ode, dependent)))
    print(f"{s1=}")

    ode1 = prolongation.subs({ diff(dependent(independent),independent, ode_order(ode, dependent)) : s1[0]}).simplify()
    from IPython.core.debugger import set_trace
    l = [diff(dependent(independent), independent, i)
                                           for i in range(ode_order(ode, dependent), 0, -1)] + [dependent(independent)]
    print(f"{l=}")
    equations = []
    for i in l:
        k = collect(ode1, i, evaluate=False, exact=True)
        from pprint import pprint
        pprint(k.__class__)
        for j in k.items():
            print(f"{j=}")
    from IPython.core.debugger import set_trace; set_trace()
    for _ in reversed(sorted(all_this_stuff)):
        new = e.coefficient(_.coeff)
        if new != 0:
            equations.append(new)
        e = (e - new * _.coeff).expand()
    if e != 0:
        equations.append(e)
    return equations

def Janet_Basis_from_ODE(ode, dependent, independent, order = "Mgrevlex", *args, **kw):
    overdetermined_system = overdeterminedSystemODE(ode, dependent, independent)
    #ToDo: 2 way:
    #    * either as Janet_Basis
    #    * or try to solve the undetermined system
    Y = symbols('Y')
    intermediate_system = []
    for e in overdetermined_system:
        # ToDo: make the next three lines into a function for helpers(code duplication
        #       with overdeterminedSystemODE. Idea: return a dict with {function: order}#
        tree = ExpressionTree(e)
        mine = [_ for _ in tree.diffs if _.operator().Function() in [dependent]]
        order= max([len(_.operator().parameter_set()) for _ in mine]) if mine else 0
        e = e.subs({dependent(independent): Y})
        for j in range(1, order+1):
            d = diff(dependent(independent), independent, j)
            e = e.subs({d: 0})
        intermediate_system.append(e)
    # ToDo: get rid of hardcoded phi and xi

    print("Overdeterminedsystemode")
    for _ in intermediate_system:
        _.show()


    janet = Janet_Basis(intermediate_system, [phi, xi], [Y, independent])
    pols = list(map(lambda _ : _.expression().subs({Y : dependent(independent)}), janet.S))
    return pols


if __name__ == "__main__":
    import doctest
    doctest.testmod()
