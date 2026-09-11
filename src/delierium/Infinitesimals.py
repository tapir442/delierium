"""Infinitesimals."""

from collections import ChainMap, OrderedDict
from collections.abc import Iterable
from functools import reduce
from itertools import combinations_with_replacement
from typing import Any, List, Set

from sympy import (Derivative, Dummy, Expr, Function, Symbol, diff,
                   init_printing, solve)
from sympy.core.backend import (Derivative, Function, Symbol,  # pyflakes: F811
                                diff)

from delierium.helpers import (finish_substitution, func_diff,
                               make_infinitesimal, profile_if_enabled)
from delierium.JanetBasis import LHDP, Janet_Basis, Reorder, _Dterm
from delierium.matrix_order import Context, Mgrevlex

init_printing()


def variable_combinations(variables: list[Symbol], order: int) -> list[tuple[Symbol, ...]]:
    return reduce(
        lambda acc, i: acc +
        list(map(list, combinations_with_replacement(variables, i))),
        range(1, order + 1),
        [])


def order(expr: Expr, dep: list[Function], indep: list[Symbol]) -> tuple[int, Set[Expr]]:
    max_order = 0
    max_deriv = set()
    # XXX: code duplication
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    k = expr.expand().atoms(Derivative)
    for atom in k:
        if atom.args[0].name in [_.name for _ in dep]:
            _order = sum(cnt[1] for cnt in atom.args[1:])
            if max_order == _order:
                max_deriv |= set([atom])
            elif max_order < _order:
                max_deriv = set([atom])
                max_order = _order
    # XXX: return coefficients, too. When some coefficients are -1, or 1,
    # or numerical
    # return only those derivs
    return (max_order, max_deriv)


@profile_if_enabled
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


@profile_if_enabled
def prolongation(expr, n, infinitesimals, dep, indep, dummies):
    """
    Doctest stolen from Baumann pp.92/93
    >>> x = Symbol('x')
    >>> u = Function('u')
    >>> u_x = u(x)
    >>> f = Function("f")
    >>> fx = f(x, u_x, Derivative(u_x, x))
    >>> inf = {x: make_infinitesimal(x, x, fx, name=r"phi"), fx: make_infinitesimal(fx, x, fx, name=r"xi")}
    >>> ppp = prolongation(fx, 2, inf, [u_x], [x], dummies={}).expand()
    >>> d = finish_substitution(ppp)
    >>> ppp = ppp.xreplace(d)
    >>> print(ppp.expand())
    -D[2](f)(x, u(x), Derivative(u(x), x))*Derivative(u(x), x)^2*D[1](xi_1)(x, u(x)) + D[2](f)(x, u(x), Derivative(u(x), x))*D[1](phi_1)(x, u(x))*Derivative(u(x), x) - D[2](f)(x, u(x), Derivative(u(x), x))*Derivative(u(x), x)*D[0](xi_1)(x, u(x)) + xi_1(x, u(x))*D[0](f)(x, u(x), Derivative(u(x), x)) + phi_1(x, u(x))*D[1](f)(x, u(x), Derivative(u(x), x)) + D[2](f)(x, u(x), Derivative(u(x), x))*D[0](phi_1)(x, u(x))
    >>> # this one here is from Baumann, p.93
    >>> f_x = f(x, u(x), diff(u(x),x),  diff(u(x), x ,x))
    >>> # Baumann's example p. 94
    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> inf = {x: make_infinitesimal(x, x, y, name=r"phi"), fx: make_infinitesimal(y, x, y, name=r"xi")}
    >>> print(prolongation(diff(y,x,2), 2, inf, [y], [x], dummies={}).expand())
    -D[1, 1](xi_1)(x, y(x))*Derivative(y(x), x)^3 + D[1, 1](phi_1)(x, y(x))*Derivative(y(x), x)^2 - 2*D[0, 1](xi_1)(x, y(x))*Derivative(y(x), x)^2 - 3*D[1](xi_1)(x, y(x))*Derivative(y(x), x)*Derivative(y(x), x, x) + 2*D[0, 1](phi_1)(x, y(x))*Derivative(y(x), x) - D[0, 0](xi_1)(x, y(x))*Derivative(y(x), x) + D[1](phi_1)(x, y(x))*Derivative(y(x), x, x) - 2*D[0](xi_1)(x, y(x))*Derivative(y(x), x, x) + D[0, 0](phi_1)(x, y(x))
    """  # noqa: ignore=E501
    for inf in infinitesimals:
        d = finish_substitution(infinitesimals[inf])
        infinitesimals[inf] = infinitesimals[inf].xreplace(d)

    reverse_dummies = {}
    for k, v in dummies.items():
        reverse_dummies[v] = k
    acc = sum(infinitesimals[_] *
              func_diff(expr.xreplace(dummies), _.xreplace(
                  dummies)).xreplace(reverse_dummies)
              for _ in infinitesimals)
    return acc


@profile_if_enabled
def extract_coeffs(expr, dep, indep):
    def analyze_power(factor):
        base = factor.as_base_exp()[0]
        if base.is_Derivative:
            if base.args[0] in dep:
                return factor
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
                pass
            elif factor.is_number:
                pass
            else:
                # XXx: explore with heateq
                pass
        if f != 1:
            all_i_need.add(f)
    return list(all_i_need)


def get_coeff_order(expr) -> Expr:
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
        termsum = sum(
            term/coeff for term in expr.expand().args if term.has(coeff))
        acc.append(termsum)
        expr -= termsum * coeff
    acc.append(expr.expand())
    acc = [_.xreplace(finish_substitution(_)) for _ in acc]
    return acc


def convert_to_iterable(item):
    if not isinstance(item, Iterable):
        item = [item]
    return item


def create_infinitesimals(dep, indep, inf=None):
    infinitesimals = OrderedDict()
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    if inf is None:
        infinitesimals = OrderedDict()
        for d in dep + indep:
            infinitesimals[d] = make_infinitesimal(
                d, *(dep + indep), name=d.name.swapcase())
    else:
        for v, i in inf.items():
            if isinstance(i, str):
                infinitesimals[v] = make_infinitesimal(
                    v, *(dep + indep), name=i)
            else:
                infinitesimals[v] = i
    return infinitesimals


def compute_overdetermined_system_of_infinitesimals(
        eq: Expr,
        dep: Symbol,
        indep: Symbol,
        infinitesimals=None):
    """
    infinitesimals : dict{Function/Symbol : new name}
    """
    # XXX: code duplication
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)

    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    eq_order, highest_term = order(eq, dep, indep)
    highest_term = list(highest_term)[0]

    combos = variable_combinations(indep, eq_order)
    dummies = OrderedDict()

    for comb in combos:
        funcs, etas = compute_level(comb, dep, indep, infinitesimals)
        infinitesimals[funcs[0]] = etas[0]
        dummies[funcs[0]] = Symbol(
            f"{dep[0].name}_{"".join([str(v) for v in comb])}")

    vdummies = OrderedDict()
    for i in dep + indep:
        vdummies[i] = Symbol(i.name)

    _dummies = ChainMap(dummies, vdummies)
    r = prolongation(eq, eq_order, infinitesimals,
                     dep, indep, _dummies).expand()
    sol = solve(eq, highest_term)[0]
    r = r.xreplace(finish_substitution(r))
    r = r.xreplace({highest_term: sol})
    coeffs = sorted(
        extract_coeffs(r, dep, indep),
        key=get_coeff_order,
        reverse=True,
    )
    return compute_determining_equations(r, coeffs)


def overdeterminedSystemODE(ode,
                            dependent,
                            independent,
                            infinitesimals=None,
                            *args, **kw):
    """
    >>> # Arrigo Example 2.20
    >>> from delierium.helpers import ltf
    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> ode = diff(y, x, 3) + y * diff(y, x, 2)
    >>> infinitesimals = OrderedDict({x: make_infinitesimal(x, x, y, name='X'), y: make_infinitesimal(y, x, y, name='Y')})
    >>> inf = overdeterminedSystemODE(ode, [y], [x], infinitesimals=infinitesimals)
    >>> inf = [str(ltf(_, [infinitesimals[y]], [infinitesimals[x]], printer=False)) for _ in inf]
    >>> for _ in sorted(inf):
    ...    print(_)
    -3*X_{xxy} - 2*X_{xy}*y + 3*Y_{xyy} + Y_{yy}*y
    -3*X_{xx} + X_{x}*y + Y + 3*Y_{xy}
    -3*X_{xyy} - X_{yy}*y + Y_{yyy}
    -3*X_{y}
    -6*X_{yy}
    -9*X_{xy} + X_{y}*y + 3*Y_{yy}
    -X_{xxx} - X_{xx}*y + 3*Y_{xxy} + 2*Y_{xy}*y
    -X_{yyy}
    Y_{xxx} + Y_{xx}*y
    """  # noqa: ignore=E501
    return compute_overdetermined_system_of_infinitesimals(
        ode,
        dependent,
        independent,
        infinitesimals=infinitesimals)


def overdeterminedSystemODEs(eqs: List[Expr],
                             dependent: Symbol,
                             independent: Symbol,
                             infinitesimals=None,
                             *args, **kw) -> List[Expr]:
    from more_itertools import flatten
    res = []
    for _ in eqs:
        gugu = overdeterminedSystemODE(_, dependent, independent, infinitesimals, *args, **kw)
        print("===="*30)
        print(f"{_=}")
        print(f"{gugu=}")
        res.extend(gugu)
    return res


def overdeterminedSystemPDE(pde,
                            dependent,
                            independent,
                            infinitesimals=None,
                            *args, **kw):
    pass


def janet_basis_from_ODE(ode: Expr,
                         dependent: Symbol,
                         independent: Symbol,
                         sort_order=Mgrevlex,
                         infinitesimals=None, *args, **kw):
    infinitesimals = create_infinitesimals(
        [dependent], [independent], infinitesimals)
    overdetermined_system = overdeterminedSystemODE(
        ode, [dependent], [independent], infinitesimals=infinitesimals)
    Y = Dummy()
    Y = Symbol("H")
    inf = [infinitesimals[_] for _ in [dependent, independent]]

    r1 = [Y, independent]
    # ToDo: 2 way:
    #    * either as Janet_Basis
    #    * or try to solve the undetermined system

    inf = [_.xreplace({dependent: Y}) for _ in inf]
    r1 = [_.xreplace({dependent: Y}) for _ in r1]
    intermediate_system = []
    for e in overdetermined_system:
        e = e.replace(dependent, Y)
        mine = [_ for _ in e.atoms(Derivative) if _.args[0].func == dependent]

        order = max((len(_.operator().parameter_set())
                    for _ in mine)) if mine else 0

        for j in range(1, order+1):
            d = diff(dependent(independent), independent, j)
            e = e.subs({d: 0})
        intermediate_system.append(e)

    janet = Janet_Basis(intermediate_system, reversed(inf),
                        reversed(r1), sort_order=sort_order)
    res = []
    def backsubstition(e): return e.xreplace({Y: dependent})
    for lhdp in janet.S:
        p = []
        for term in lhdp.p:
            coeff = backsubstition(term.coeff)
            d = backsubstition(term.derivative)
            ctx = Context(dependent=[backsubstition(_) for _ in term.context.dependent],
                          independent=[backsubstition(
                              _) for _ in term.context.independent],
                          weight=sort_order)
            p.append(_Dterm(derivative=d, coeff=coeff, context=ctx))
        res.append(LHDP(e=0, context=ctx, dterms=p))
    res = Reorder(res, context=ctx)
    return res


if __name__ == "__main__":
    import doctest
    doctest.testmod()
