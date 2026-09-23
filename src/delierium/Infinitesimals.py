"""Infinitesimals.

Computes the overdetermined system of determining equations for the
infinitesimal generators of the Lie point symmetry group of an ODE/PDE,
via prolongation of the vector field and extraction of coefficients.
"""

from collections import OrderedDict
from collections.abc import Iterable
from functools import reduce
from itertools import combinations_with_replacement
from typing import Any

from sympy import (  # noqa: F401
    Derivative,
    Dummy,
    Expr,
    Function,
    Integer,
    Poly,
    Symbol,
    cancel,
    default_sort_key,
    diff,
    exp,
    fraction,
    init_printing,
    numer,
    prem,
    solve,
    together,
)
from sympy.core.backend import Derivative, Function, Symbol, diff  # noqa: F811

from delierium.helpers import finish_substitution, func_diff, make_infinitesimal, profile_if_enabled
from delierium.JanetBasis import LHDP, Janet_Basis, Reorder, _Dterm, is_janet_basis_of
from delierium.matrix_order import Context, Mgrevlex

init_printing()


def variable_combinations(variables: list[Symbol], max_order: int) -> list[list[Symbol]]:
    """All non-decreasing multi-indices of `variables` of length 1..max_order.

    >>> x, t, u = Symbol('x'), Symbol('t'), Symbol('u')
    >>> variable_combinations([x, t], 2)
    [[x], [t], [x, x], [x, t], [t, t]]
    >>> variable_combinations([x], 3)
    [[x], [x, x], [x, x, x]]
    >>> variable_combinations([x, t], 0)
    []
    >>> variable_combinations([u, t, x], 4)  # doctest: +NORMALIZE_WHITESPACE
    [[u], [t], [x], [u, u], [u, t], [u, x], [t, t], [t, x], [x, x], [u, u, u], [u, u, t], [u, u, x],
    [u, t, t], [u, t, x], [u, x, x], [t, t, t], [t, t, x], [t, x, x], [x, x, x], [u, u, u, u], [u,
    u, u, t], [u, u, u, x], [u, u, t, t], [u, u, t, x], [u, u, x, x], [u, t, t, t], [u, t, t, x],
    [u, t, x, x], [u, x, x, x], [t, t, t, t], [t, t, t, x], [t, t, x, x], [t, x, x, x], [x, x, x,
    x]]

    """
    return [
        list(combo)
        for i in range(1, max_order + 1)
        for combo in combinations_with_replacement(variables, i)
    ]


def order(expr: Expr, dep: list[Function], indep: list[Symbol]) -> tuple[int, set[Expr]]:
    """Highest derivative order of a dependent variable occurring in expr,
    and the set of derivatives attaining that order.

    `dep` and `indep` must already be lists (see convert_to_iterable).
    """
    max_order = 0
    max_deriv = set()
    dep_names = [_.name for _ in dep]
    for atom in expr.expand().atoms(Derivative):
        if atom.args[0].name in dep_names:
            _order = len(atom.variables)
            if max_order == _order:
                max_deriv |= {atom}
            elif max_order < _order:
                max_deriv = {atom}
                max_order = _order
    return (max_order, max_deriv)


@profile_if_enabled
def compute_level(deriv_vars_order: list[Any], dep, indep, infinitesimals):
    """Compute all derivatives and infinitesimals for a given derivative order.
    Extended Gamma operator (Arrigo, eq 2.85, or Schwarz, eq. 5.10)

    >>> from delierium.helpers import ltf
    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> X = make_infinitesimal(x, x, y, name='X')
    >>> Y = make_infinitesimal(y, x, y, name='Y')
    >>> infinitesimals = {x: X, y: Y}

    First prolongation eta^(x) = Y_x + (Y_y - X_x) y_x - X_y y_x^2:

    >>> funcs, etas = compute_level([x], [y], [x], infinitesimals)
    >>> funcs
    [Derivative(y(x), x)]
    >>> eta = finish_substitution(etas[0]).expand()
    >>> print(ltf(eta, [Y], [X], printer=False))
    -X_{x}*y_{x} - X_{y}*y_{x}**2 + Y_{x} + Y_{y}*y_{x}

    Second prolongation eta^(xx), computed recursively from the first:

    >>> funcs, etas = compute_level([x, x], [y], [x], infinitesimals)
    >>> funcs
    [Derivative(y(x), (x, 2))]
    >>> eta = finish_substitution(etas[0]).expand()
    >>> print(ltf(eta, [Y], [X], printer=False))  # doctest: +NORMALIZE_WHITESPACE
    -X_{xx}*y_{x} - 2*X_{xy}*y_{x}**2 - 2*X_{x}*y_{xx} - X_{yy}*y_{x}**3 - 3*X_{y}*y_{xx}*y_{x} +
    Y_{xx} + 2*Y_{xy}*y_{x} + Y_{yy}*y_{x}**2 + Y_{y}*y_{xx}

    Two independent variables (PDE case): eta^t for u(x, t):

    >>> t = Symbol('t')
    >>> u = Function('u')(x, t)
    >>> Xi = make_infinitesimal(x, x, t, u, name='X')
    >>> T = make_infinitesimal(t, x, t, u, name='T')
    >>> U = make_infinitesimal(u, x, t, u, name='U')
    >>> infinitesimals = {x: Xi, t: T, u: U}
    >>> funcs, etas = compute_level([t], [u], [x, t], infinitesimals)
    >>> funcs
    [Derivative(u(x, t), t)]
    >>> eta = finish_substitution(etas[0]).expand()
    >>> print(ltf(eta, [U], [Xi, T], printer=False))
    -T_{t}*u_{t} - T_{u}*u_{t}**2 + U_{t} + U_{u}*u_{t} - X_{t}*u_{x} - X_{u}*u_{t}*u_{x}
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
                lambda acc, var: acc - func_diff(func, var) * func_diff(infinitesimals[var], v),
                indep,
                func_diff(eta, v),
            ),
        )
        for func, eta in zip(funcs, etas, strict=True)
    ]
    funcs_next, etas_next = zip(*results, strict=True)
    return list(funcs_next), list(etas_next)


@profile_if_enabled
def prolongation(expr, infinitesimals, dep, indep):
    """Apply the prolonged vector field Gamma to expr.

    Gamma = sum_w infinitesimals[w] * d/dw, where w runs over the
    independent and dependent variables and every derivative of a
    dependent variable up to the order of expr, all treated as
    independent jet coordinates. The extended infinitesimals of the
    derivatives are computed here from the ones for dep and indep, so
    `infinitesimals` only needs those; it is not modified.

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> X = make_infinitesimal(x, x, y, name='X')
    >>> Y = make_infinitesimal(y, x, y, name='Y')
    >>> inf = {x: X, y: Y}

    On the base variables Gamma just picks the infinitesimal:

    >>> prolongation(x, inf, [y], [x])
    X(x, y(x))
    >>> prolongation(y, inf, [y], [x])
    Y(x, y(x))

    A constant is annihilated:

    >>> prolongation(Integer(3), inf, [y], [x])
    0

    Product and chain rule:

    >>> print(prolongation(x * y, inf, [y], [x]).expand())
    x*Y(x, y(x)) + X(x, y(x))*y(x)
    >>> print(prolongation(y**2, inf, [y], [x]).expand())
    2*Y(x, y(x))*y(x)

    On y' it yields the first extension
    eta^(1) = eta_x + (eta_y - xi_x) y' - xi_y y'^2:

    >>> print(prolongation(diff(y, x), inf, [y], [x]).expand())  # doctest: +NORMALIZE_WHITESPACE
    -Derivative(X(x, y(x)), x)*Derivative(y(x), x) - Derivative(X(x, y(x)), y(x))*Derivative(y(x),
    x)**2 + Derivative(Y(x, y(x)), x) + Derivative(Y(x, y(x)), y(x))*Derivative(y(x), x)

    Two independent variables (PDE case), eta^t for u(x, t):

    >>> t = Symbol('t')
    >>> u = Function('u')(x, t)
    >>> Xi = make_infinitesimal(x, x, t, u, name='X')
    >>> T = make_infinitesimal(t, x, t, u, name='T')
    >>> U = make_infinitesimal(u, x, t, u, name='U')
    >>> inf_pde = {x: Xi, t: T, u: U}
    >>> from delierium.helpers import ltf
    >>> r = prolongation(diff(u, t), inf_pde, [u], [x, t])
    >>> print(ltf(r.expand(), [U], [Xi, T], printer=False))
    -T_{t}*u_{t} - T_{u}*u_{t}**2 + U_{t} + U_{u}*u_{t} - X_{t}*u_{x} - X_{u}*u_{t}*u_{x}
    """
    infinitesimals = OrderedDict((k, finish_substitution(v)) for k, v in infinitesimals.items())
    dummies = OrderedDict()
    for combi in variable_combinations(indep, order(expr, dep, indep)[0]):
        funcs, etas = compute_level(combi, dep, indep, infinitesimals)
        infinitesimals[funcs[0]] = etas[0]
        suffix = "".join(str(v) for v in combi)
        dummies[funcs[0]] = Symbol(f"{dep[0].name}_{suffix}")
    for v in dep + indep:
        dummies[v] = Symbol(v.name)

    reverse_dummies = {v: k for k, v in dummies.items()}
    acc = sum(
        infinitesimals[_]
        * func_diff(expr.xreplace(dummies), _.xreplace(dummies)).xreplace(reverse_dummies)
        for _ in infinitesimals
    )
    return finish_substitution(acc)


def split_jet_coefficients(expr, dep) -> list[Expr]:
    """Split expr into determining equations: the coefficients of expr
    as a polynomial in the jet variables, i.e. in all derivatives of the
    dependent variables occurring in it. Denominators are cleared, zero
    and duplicate coefficients dropped.

    >>> x, t = Symbol('x'), Symbol('t')
    >>> y = Function('y')(x)
    >>> d1, d2 = Derivative(y, x), Derivative(y, x, 2)
    >>> split_jet_coefficients(2 * x * d1**2 * d2 + 3 * d1 + x * d1 + 5 * x**2 + d2**3 + 7, [y])
    [1, 2*x, x + 3, 5*x**2 + 7]

    Mixed jet variables of a PDE are split as well, and coefficients
    depending on u itself (not a jet variable) stay together:

    >>> u = Function('u')(x, t)
    >>> ux, ut = Derivative(u, x), Derivative(u, t)
    >>> split_jet_coefficients(u * ux * ut + x * ux * ut + ux**2 / u - x, [u])
    [1, -x, x + u(x, t)]

    Jet variables in a denominator (as after solving for the highest
    derivative) are cleared:

    >>> split_jet_coefficients(x * d2 - x / d1 + 1, [y])
    [1, -x, x]

    Exponentials of jet variables are split off as well: p**k * exp(m*a*p)
    are linearly independent functions of the jet variable p:

    >>> split_jet_coefficients(x * d1 * exp(y * d1) + x**2 * exp(2 * y * d1) + d1 - 1, [y])
    [-1, 1, x, x**2]
    """
    jet = {d: Dummy() for d in expr.atoms(Derivative) if d.expr in dep}
    expr = expr.xreplace(jet)
    to_symbol = {d: Symbol(d.name) for d in dep}
    expr = expr.xreplace(to_symbol).doit()
    # after solving for the highest derivative, jet variables may occur
    # in denominators; multiply by the jet-dependent part of the
    # denominator (it does not change where the expression vanishes)
    num, den = fraction(together(expr))
    other_den, _ = den.as_independent(*jet.values(), as_Add=False)
    expr = (num / other_den).expand()
    expr, exp_gens = _exp_generators(expr, list(jet.values()))
    coeffs = Poly(expr, *jet.values(), *exp_gens).coeffs() if jet else [expr]
    back = {v: k for k, v in to_symbol.items()}
    result = set()
    for c in coeffs:
        c = numer(cancel(c)).expand().xreplace(back)
        if c != 0:
            result.add(c)
    return sorted(result, key=default_sort_key)


def _exp_generators(expr, jet):
    """Replace the exponentials depending on the jet variables by powers of
    new generators, one per family exp(k*a), k a positive integer."""
    exps = sorted((e for e in expr.atoms(exp) if e.has(*jet)), key=default_sort_key)
    bases = []  # (exponent, generator)
    repl = {}
    for e in exps:
        for arg, gen in bases:
            ratio = cancel(e.args[0] / arg)
            if ratio.is_Rational:
                if not (ratio.is_Integer and ratio > 0):
                    raise NotImplementedError(f"{e} is exp({ratio}*({arg}))")
                repl[e] = gen**ratio
                break
        else:
            gen = Dummy()
            bases.append((e.args[0], gen))
            repl[e] = gen
    return expr.xreplace(repl), [gen for _, gen in bases]


def canonical_derivatives(expr, dep):
    """Bring the variables of every derivative of an infinitesimal into
    sympy's canonical order, so that e.g. X_{x y} and X_{y x} compare
    equal. Derivatives w.r.t. y(x) are not reordered by sympy itself.

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> X = Function('X')(x, y)
    >>> canonical_derivatives(Derivative(X, y, x) - Derivative(X, x, y), [y])
    0
    """
    to_symbol = {d: Symbol(d.name) for d in dep}
    back = {v: k for k, v in to_symbol.items()}
    return expr.xreplace(to_symbol).doit().expand().xreplace(back)


def convert_to_iterable(item):
    if not isinstance(item, Iterable):
        item = [item]
    return item


def create_infinitesimals(dep, indep, inf=None):
    """Build the dict of infinitesimal generator functions, one per
    dependent/independent variable, each depending on all of dep+indep.

    - inf=None: create a fresh infinitesimal for every variable, named by
      swapping the case of the variable's own name (x -> X, y -> Y, ...).
    - inf given: for each variable, a string value names a fresh
      infinitesimal to create; any other value (typically an already
      built Function expression) is used verbatim, unchanged.

    >>> x = Symbol('x')
    >>> y = Function('y')(x)

    Default naming:

    >>> create_infinitesimals(y, x)
    OrderedDict({y(x): Y(y(x), x), x: X(y(x), x)})

    Custom names:

    >>> create_infinitesimals(y, x, {x: 'A', y: 'B'})
    OrderedDict({x: A(y(x), x), y(x): B(y(x), x)})

    Passing already-built infinitesimals through unchanged:

    >>> X = make_infinitesimal(x, x, y, name='X')
    >>> create_infinitesimals(y, x, {x: X}) == OrderedDict({x: X})
    True
    """
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    infinitesimals = OrderedDict()
    if inf is None:
        for d in dep + indep:
            infinitesimals[d] = make_infinitesimal(d, *(dep + indep), name=d.name.swapcase())
    else:
        for v, i in inf.items():
            if isinstance(i, str):
                infinitesimals[v] = make_infinitesimal(v, *(dep + indep), name=i)
            else:
                infinitesimals[v] = i
    return infinitesimals


def compute_overdetermined_system_of_infinitesimals(
    eq: Expr, dep: Symbol | list[Symbol], indep: Symbol | list[Symbol], infinitesimals=None
):
    """
    infinitesimals : dict{Function/Symbol : new name}

    An ODE that is not linear in its highest derivative, y''**2 = y',
    with the symmetries d/dx, d/dy and x d/dx + 3 y d/dy:

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> for _ in janet_basis_from_ode(diff(y, x, 2)**2 - diff(y, x), y, x):
    ...     print(_)
    D(Y(y(x), x), (y(x), 2))
    D(X(y(x), x), x) + (-1/3) * D(Y(y(x), x), y(x))
    D(X(y(x), x), y(x))
    D(Y(y(x), x), x)
    """
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)

    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    _, highest_term = order(eq, dep, indep)
    highest_term = next(iter(highest_term))

    r = prolongation(eq, infinitesimals, dep, indep)
    h = Dummy()
    eq_h = numer(together(eq.xreplace({highest_term: h})))
    if Poly(eq_h, h).degree() == 1:
        sol = solve(eq, highest_term)[0]
        r = r.xreplace({highest_term: sol})
    else:
        # eq is not linear in its highest derivative: solving for it would
        # bring in roots of jet variables. pr X(eq) has to vanish on eq = 0,
        # i.e. (eq being irreducible) eq has to divide it as a polynomial in
        # the highest derivative, so its pseudo-remainder has to vanish
        r_h = numer(together(r.xreplace({highest_term: h})))
        r = prem(r_h, eq_h, h).xreplace({h: highest_term})
    return split_jet_coefficients(r, dep)


def overdetermined_system_ode(ode, dependent, independent, infinitesimals=None, *args, **kw):
    """
    >>> # Arrigo Example 2.20
    >>> from delierium.helpers import ltf
    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> ode = diff(y, x, 3) + y * diff(y, x, 2)
    >>> infinitesimals = OrderedDict(
    ...     {x: make_infinitesimal(x, x, y, name='X'), y: make_infinitesimal(y, x, y, name='Y')}
    ... )
    >>> inf = overdetermined_system_ode(ode, [y], [x], infinitesimals=infinitesimals)
    >>> inf = [str(ltf(_, [infinitesimals[y]], [infinitesimals[x]], printer=False)) for _ in inf]
    >>> for _ in sorted(inf):
    ...     print(_)
    -3*X_{xxy} - 2*X_{xy}*y + 3*Y_{xyy} + Y_{yy}*y
    -3*X_{xx} + X_{x}*y + Y + 3*Y_{xy}
    -3*X_{xyy} - X_{yy}*y + Y_{yyy}
    -3*X_{y}
    -6*X_{yy}
    -9*X_{xy} + X_{y}*y + 3*Y_{yy}
    -X_{xxx} - X_{xx}*y + 3*Y_{xxy} + 2*Y_{xy}*y
    -X_{yyy}
    Y_{xxx} + Y_{xx}*y
    """
    result = compute_overdetermined_system_of_infinitesimals(
        ode, dependent, independent, infinitesimals=infinitesimals
    )
    result = [finish_substitution(_) for _ in result]
    return result


def overdetermined_system_odes(
    eqs: list[Expr], dependent: Symbol, independent: Symbol, infinitesimals=None, *args, **kw
) -> list[Expr]:
    res = []
    for _ in eqs:
        osode = overdetermined_system_ode(_, dependent, independent, infinitesimals, *args, **kw)
        res.extend(osode)
    return res


def overdetermined_system_pde(pde, dependent, independent, infinitesimals=None, *args, **kw):
    """Determining equations for the Lie point symmetries of a scalar PDE
    (one dependent variable, any number of independent ones).

    >>> # Arrigo, heat equation, eq 3.34
    >>> from delierium.helpers import ltf
    >>> x, t = Symbol('x'), Symbol('t')
    >>> u = Function('u')(x, t)
    >>> infinitesimals = OrderedDict(
    ...     (v, make_infinitesimal(v, x, t, u, name=n)) for v, n in [(x, 'X'), (t, 'T'), (u, 'U')]
    ... )
    >>> pde = diff(u, t) - diff(u, x, 2)
    >>> inf = overdetermined_system_pde(pde, [u], [x, t], infinitesimals=infinitesimals)
    >>> inf = [
    ...     str(ltf(_, [infinitesimals[u]], [infinitesimals[x], infinitesimals[t]], printer=False))
    ...     for _ in inf
    ... ]
    >>> for _ in sorted(inf):
    ...     print(_)
    -2*U_{ux} - X_{t} + X_{xx}
    -T_{t} + T_{xx} + 2*X_{x}
    -U_{uu} + 2*X_{ux}
    2*T_{ux} + 2*X_{u}
    2*T_{u}
    2*T_{x}
    T_{uu}
    U_{t} - U_{xx}
    X_{uu}
    """
    if len(convert_to_iterable(dependent)) != 1:
        raise NotImplementedError("only one dependent variable is supported")
    result = compute_overdetermined_system_of_infinitesimals(
        pde, dependent, independent, infinitesimals=infinitesimals
    )
    return [finish_substitution(_) for _ in result]


def _linear_system_ode(ode, dependent, independent, infinitesimals=None):
    """The determining equations of an ODE as a linear system for Janet_Basis.

    Returns (system, dependents, independents, h_symbol): the dependent
    variable y(x) is replaced by the symbol H and all derivatives of y are
    set to zero, so the infinitesimals become functions of (H, x).
    """
    infinitesimals = create_infinitesimals([dependent], [independent], infinitesimals)
    overdetermined_system = overdetermined_system_ode(
        ode, [dependent], [independent], infinitesimals=infinitesimals
    )
    h_symbol = Symbol("H")
    inf = [infinitesimals[_] for _ in [dependent, independent]]

    r1 = [h_symbol, independent]
    # ToDo: 2 way:
    #    * either as Janet_Basis
    #    * or try to solve the undetermined system

    inf = [_.xreplace({dependent: h_symbol}) for _ in inf]
    r1 = [_.xreplace({dependent: h_symbol}) for _ in r1]
    intermediate_system = []
    for e in overdetermined_system:
        e = e.replace(dependent, h_symbol)
        mine = [_ for _ in e.atoms(Derivative) if _.args[0].func == dependent]

        max_deriv_order = max(len(_.operator().parameter_set()) for _ in mine) if mine else 0

        for j in range(1, max_deriv_order + 1):
            d = diff(dependent(independent), independent, j)
            e = e.subs({d: 0})
        intermediate_system.append(e)
    return intermediate_system, list(reversed(inf)), list(reversed(r1)), h_symbol


def janet_basis_from_ode(
    ode: Expr,
    dependent: Symbol,
    independent: Symbol,
    sort_order=Mgrevlex,
    infinitesimals=None,
    *args,
    **kw,
):
    system, inf, r1, h_symbol = _linear_system_ode(ode, dependent, independent, infinitesimals)
    janet = Janet_Basis(system, inf, r1, sort_order=sort_order)

    def back_substitute(e):
        return e.xreplace({h_symbol: dependent})

    res = []
    for lhdp in janet.S:
        p = []
        for term in lhdp.p:
            coeff = back_substitute(term.coeff)
            d = back_substitute(term.derivative)
            ctx = Context(
                dependent=[back_substitute(_) for _ in term.context.dependent],
                independent=[back_substitute(_) for _ in term.context.independent],
                weight=sort_order,
            )
            p.append(_Dterm(derivative=d, coeff=coeff, context=ctx))
        res.append(LHDP(e=0, context=ctx, dterms=p))
    res = Reorder(res, context=ctx)
    return res


def is_janet_basis_of_ode(
    B,
    ode,
    dependent,
    independent,
    sort_order=Mgrevlex,
    infinitesimals=None,
    dependent_order=None,
    independent_order=None,
):
    """Check whether B is the Janet basis of the determining equations of ode.

    B is written in the infinitesimals X(y, x), Y(y, x) of a plain symbol y
    named like the dependent variable, so that diff gives partial derivatives
    (with y(x) in place of y, diff(Y, x) would be the total derivative).
    LHDPs as returned by janet_basis_from_ode are accepted as well, see
    is_janet_basis_of.

    The ranking is given by sort_order and, highest first, by
    dependent_order (the infinitesimals, e.g. [Y, X]) and independent_order
    (e.g. [ys, x]); the default is the one of janet_basis_from_ode,
    [X, Y] and [x, y]. Infinitesimals may be given by name as well.

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> # Schwarz, Example 5.17
    >>> d1, d2 = diff(y, x), diff(y, x, 2)
    >>> ode = 8*x*d2*y**6 - 9*x**5*d1**4 - 16*x*d1**2*y**5 + 16*d1*y**6
    >>> ys = Symbol('y')
    >>> X, Y = Function("X")(ys, x), Function("Y")(ys, x)
    >>> B = [
    ...     diff(Y, ys, 2) - 2 * diff(Y, ys) / ys + 2 * Y / ys**2,
    ...     diff(X, x) - 3 * diff(Y, ys) / 2 - 2 * X / x + 3 * Y / ys,
    ...     diff(X, ys),
    ...     diff(Y, x),
    ... ]
    >>> is_janet_basis_of_ode(B, ode, y, x)
    True
    >>> is_janet_basis_of_ode(janet_basis_from_ode(ode, y, x), ode, y, x)
    True
    >>> is_janet_basis_of_ode(B[1:], ode, y, x)
    False

    With Y ranked above X and y above x, Y_y leads instead of X_x:

    >>> B2 = [
    ...     diff(X, x, 2) - 2 * diff(X, x) / x + 2 * X / x**2,
    ...     diff(Y, ys) - 2 * diff(X, x) / 3 + 4 * X / (3 * x) - 2 * Y / ys,
    ...     diff(X, ys),
    ...     diff(Y, x),
    ... ]
    >>> is_janet_basis_of_ode(B2, ode, y, x)
    False
    >>> is_janet_basis_of_ode(B2, ode, y, x, dependent_order=[Y, X], independent_order=[ys, x])
    True
    >>> is_janet_basis_of_ode(B2, ode, y, x, dependent_order=["Y", "X"], independent_order=[y, x])
    True
    """
    system, inf, r1, h_symbol = _linear_system_ode(ode, dependent, independent, infinitesimals)
    to_h = {dependent: h_symbol, Symbol(str(dependent.func)): h_symbol}
    B = [(b.expression() if isinstance(b, LHDP) else b).xreplace(to_h) for b in B]
    def dep_key(f):
        return f if isinstance(f, str) else f.func.__name__

    def ind_key(v):
        # y, y(x) and "y" all stand for the dependent variable, i.e. H
        return (Symbol(v) if isinstance(v, str) else v).xreplace(to_h)

    dep = _ranked(dependent_order, inf, dep_key)
    ind = _ranked(independent_order, r1, ind_key)
    return is_janet_basis_of(B, system, dep, ind, sort_order)


def _ranked(order, default, key):
    """default, rearranged like order; the entries are matched by key."""
    if order is None:
        return default
    by_key = {key(_): _ for _ in default}
    ranked = [by_key.get(key(_)) for _ in order]
    if None in ranked or len(set(ranked)) != len(default):
        raise ValueError(f"{list(order)} is not an ordering of {default}")
    return ranked


if __name__ == "__main__":
    import doctest

    doctest.testmod()
