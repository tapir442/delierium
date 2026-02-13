#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan  7 18:49:33 2022

@author: tapir
"""

import types, os
from collections import namedtuple
from itertools import product


import delierium.functional_style

from collections import ChainMap
from functools import reduce
from itertools import combinations_with_replacement
from typing import Any
from sympy import srepr, pprint
from sympy.simplify import collect

from delierium.DerivativeOperators import FrechetD
from delierium.JanetBasis import Janet_Basis
from delierium.helpers import ExpressionTree, finish_substitution

from more_itertools import bucket, flatten, powerset

from IPython.core.debugger import set_trace

os.environ["USE_SYMENGINE"] = "1"
from sympy import *
init_printing()

import sympy as sp


def variable_combinations(variables: list[sp.Symbol], order:int) -> list(tuple[sp.Symbol]):
    return reduce(
        lambda acc, i: acc + list(map(list, combinations_with_replacement(variables, i))),
        range(1, order + 1),
        [])

def order(expr, dep, indep):
    max_order = 0
    max_deriv = set()
    k = expr.expand().atoms(sp.Derivative)
    for atom in k:
        if atom.args[0].name in [_.name for _ in dep]:
            _order = sum(cnt[1] for cnt in atom.args[1:])
            if max_order == _order:
                max_deriv |= set([atom])
            elif max_order < _order:
                max_deriv = set([atom])
                max_order = _order
    # XXX: return coefficients, too. When some coefficients are -1, or 1, or numerical
    # return only those derivs
    return (max_order, max_deriv)

def func_diff(fun:sp.Function, var:sp.Symbol | sp.Function) -> sp.Derivative:
    if var.is_Function or var.is_Derivative:
        d = sp.Symbol('d')
        r = fun.xreplace({var: d}).diff(d).xreplace({d: var}).doit()
    else:
        r = sp.Derivative(fun, var).doit()
    return r


def compute_level(deriv_vars_order: list[Any], dep, indep, infinitesimals):
    """Compute all derivatives and infinitesimals for a given derivative order.
    Extended Gamma operator (Arrigo, eq 2.85, or Schwarz, eq. 5.10)
    """
    v = deriv_vars_order[-1]
    # Base case (first order)
    if len(deriv_vars_order) == 1:
        funcs = dep
        etas = [infinitesimals[f] for f in funcs]
    else:
        prev_order = deriv_vars_order[:-1]
        funcs, etas = compute_level(prev_order, dep, indep, infinitesimals)
    # Compute current derivatives and infinitesimals functionally
    results = [
                (
                    func_diff(func, v),
                    reduce(
                        lambda acc, var: acc - func_diff(func, var)
                        * func_diff(infinitesimals[var], v),
                        indep,
                        func_diff(eta, v)
                    )
                )
                for func, eta in zip(funcs, etas)
            ]
    # Split result into separate lists
    funcs_next, etas_next = zip(*results)
    return list(funcs_next), list(etas_next)

def prolongation(expr, n, infinitesimals, dep, indep, dummies):
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

    for inf in infinitesimals:
        d = finish_substitution(infinitesimals[inf])
        infinitesimals[inf] = infinitesimals[inf].xreplace(d)
    acc = 0
    reverse_dummies = {}
    for k, v in dummies.items():
        reverse_dummies[v] = k
    for _ in infinitesimals:
        acc += infinitesimals[_] * func_diff(expr.xreplace(dummies), _.xreplace(dummies)).xreplace(reverse_dummies)

    return acc

def extract_coeffs(expr, dep, indep):
    def analyze_power(factor):
        base = factor.as_base_exp()[0]
        if base.is_Derivative:
            if base.args[0] in dep:
                return factor
        #if base.is_Function:
        #    if base in dep:
        #        return factor
        return 1
    args = expr.expand().args
    all_i_need = set()
    for term in args:
        local_term = term.args
        f = 1
        for factor in local_term:
            if factor.is_Pow:
                f *= analyze_power(factor)
            elif factor.is_Derivative:
                if factor.args[0] in dep:
                    f *= factor
            elif factor.is_Function:
                #if factor in dep:
                #    f *= factor
                pass
            elif factor.is_number:
                pass
            else:
                # XXx: explore with heateq
                pass
        if f != 1:
            all_i_need.add(f)
    return list(all_i_need)

def get_coeff_order(expr):
    acc = 0
    if expr.is_Pow:
        acc += expr.as_base_exp()[1]
    elif expr.is_Mul:
        for a in expr.args:
            if a.is_Pow:
                acc += a.as_base_exp()[1]
            else:
                acc += 1
    else:
        acc += 1
    return acc

def compute_determining_equations(expr, coeffs):
    acc = []
    for coeff in coeffs:
        termsum = sum(term/coeff for term in expr.expand().args if term.has(coeff))
        acc.append(termsum)
        expr -= termsum * coeff
    acc.append(expr.expand())
    return acc

def compute_overdetermined_system_of_infinitesimals(eq, dep, indep, infinitesimals):
    
    eq_order, highest_term = order(eq, dep, indep)
    highest_term = list(highest_term)[0]
    combos = variable_combinations(indep, eq_order)
    from IPython.core.debugger import set_trace; set_trace()
    dummies = {}

    for comb in combos:
        funcs, etas = compute_level(comb, dep, indep, infinitesimals)
        infinitesimals[funcs[0]] = etas[0]
        dummies[funcs[0]] = sp.Symbol(f"{dep[0].name}_{"".join([str(v) for v in comb])}")

    vdummies = {}
    for i in dep + indep:
        vdummies[i] = sp.Symbol(i.name)
    
    _dummies = ChainMap(dummies, vdummies)
    r = prolongation(eq, eq_order, infinitesimals, dep, indep, _dummies)
    
    sol = sp.solve(eq, highest_term)[0]
    r = r.xreplace(finish_substitution(r))
    r = r.xreplace({highest_term: sol})
    coeffs = sorted(
        extract_coeffs(r, dep, indep),
        key=get_coeff_order,
        reverse=True,
    )
    return compute_determining_equations(r, coeffs)


term = namedtuple("term", ["power", "coeff"])

"""
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

def overdeterminedSystemODE (ode,
                       dependent,
                       independent,
                       infinitesimals=None
                       , *args, **kw):
    return compute_overdetermined_system_of_infinitesimals(ode, dependent, independent, infinitesimals)

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
