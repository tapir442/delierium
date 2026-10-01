"""Infinitesimals.

Computes the overdetermined system of determining equations for the
infinitesimal generators of the Lie point symmetry group of an ODE/PDE,
via prolongation of the vector field and extraction of coefficients.
"""

from collections import OrderedDict
from collections.abc import Callable, Iterable, Mapping, Sequence
from functools import reduce
from itertools import combinations_with_replacement, permutations, product
from typing import Any, cast

from sympy import (  # noqa: F401
    Basic,
    Derivative,
    Dummy,
    Expr,
    Function,
    Integer,
    Poly,
    Pow,
    Rational,
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
    symbols,
    together,
)
from sympy.core.function import AppliedUndef
from sympy.polys.polyerrors import PolynomialError

from delierium.helpers import finish_substitution, func_diff, make_infinitesimal, profile_if_enabled
from delierium.janet_basis import (
    LHDP,
    JanetBasis,
    LHDPList,
    _Dterm,
    is_janet_basis_of,
    nonzero_factors,
    reorder,
)
from delierium.matrix_order import Context, Mgrevlex, WeightFunction

__all__ = [
    "create_infinitesimals",
    "is_janet_basis_of_ode",
    "is_janet_basis_of_odes",
    "janet_basis_from_ode",
    "janet_basis_from_odes",
    "overdetermined_system_ode",
    "overdetermined_system_odes",
    "overdetermined_system_pde",
    "prolongation",
]

init_printing()

# the infinitesimal of each variable: {x: X(x, y), y(x): Y(x, y), ...}
type Infinitesimals = dict[Basic, Expr]
# a variable or a sequence of them, see convert_to_iterable
type Variables = Basic | Iterable[Basic]
# infinitesimals to create, see create_infinitesimals
type InfinitesimalNames = Mapping[Basic, str | Expr] | None


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


def order(  # pylint: disable=unused-argument
    expr: Expr, dep: list[Function], indep: list[Symbol]
) -> tuple[int, set[Expr]]:
    """Highest derivative order of a dependent variable occurring in expr,
    and the set of derivatives attaining that order.

    `dep` and `indep` must already be lists (see convert_to_iterable).
    """
    max_order = 0
    max_deriv: set[Expr] = set()
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
def compute_level(
    deriv_vars_order: list[Any],
    dep: list[Expr],
    indep: list[Symbol],
    infinitesimals: Mapping[Basic, Expr],
) -> tuple[list[Expr], list[Expr]]:
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
    -X_x*y_x - X_y*y_x**2 + Y_x + Y_y*y_x

    Second prolongation eta^(xx), computed recursively from the first:

    >>> funcs, etas = compute_level([x, x], [y], [x], infinitesimals)
    >>> funcs
    [Derivative(y(x), (x, 2))]
    >>> eta = finish_substitution(etas[0]).expand()
    >>> print(ltf(eta, [Y], [X], printer=False))  # doctest: +NORMALIZE_WHITESPACE
    -2*X_x*y_xx - X_xx*y_x - 2*X_xy*y_x**2 - 3*X_y*y_x*y_xx - X_yy*y_x**3 + Y_xx + 2*Y_xy*y_x +
    Y_y*y_xx + Y_yy*y_x**2

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
    -T_t*u_t - T_u*u_t**2 + U_t + U_u*u_t - X_t*u_x - X_u*u_t*u_x
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
                # reduce() calls the lambda right away, while func is current
                lambda acc, var: acc - func_diff(func, var) * func_diff(infinitesimals[var], v),  # pylint: disable=cell-var-from-loop
                indep,
                func_diff(eta, v),
            ),
        )
        for func, eta in zip(funcs, etas, strict=True)
    ]
    funcs_next, etas_next = zip(*results, strict=True)
    return list(funcs_next), list(etas_next)


@profile_if_enabled
def prolongation(
    expr: Expr, infinitesimals: Mapping[Basic, Expr], dep: list[Expr], indep: list[Symbol]
) -> Expr:
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
    -T_t*u_t - T_u*u_t**2 + U_t + U_u*u_t - X_t*u_x - X_u*u_t*u_x
    """
    infinitesimals = OrderedDict((k, finish_substitution(v)) for k, v in infinitesimals.items())
    dummies: OrderedDict[Basic, Symbol] = OrderedDict()
    for combi in variable_combinations(indep, order(expr, dep, indep)[0]):
        funcs, etas = compute_level(combi, dep, indep, infinitesimals)
        suffix = "".join(str(v) for v in combi)
        for d, func, eta in zip(dep, funcs, etas, strict=True):
            infinitesimals[func] = eta
            dummies[func] = Symbol(f"{d.name}_{suffix}")
    for v in dep + indep:
        dummies[v] = Symbol(v.name)

    reverse_dummies = {v: k for k, v in dummies.items()}
    acc = sum(
        infinitesimals[_]
        * func_diff(expr.xreplace(dummies), _.xreplace(dummies)).xreplace(reverse_dummies)
        for _ in infinitesimals
    )
    return finish_substitution(acc)


def split_jet_coefficients(expr: Expr, dep: Sequence[Expr]) -> list[Expr]:
    """Split expr into determining equations: the coefficients of expr
    as a polynomial in the jet variables, i.e. in all derivatives of the
    dependent variables occurring in it. Denominators are cleared, zero
    and duplicate coefficients dropped.

    >>> x, t = Symbol('x'), Symbol('t')
    >>> y = Function('y')(x)
    >>> d1, d2 = Derivative(y, x), Derivative(y, x, 2)
    >>> split_jet_coefficients(2 * x * d1**2 * d2 + 3 * d1 + x * d1 + 5 * x**2 + d2**3 + 7, [y])
    [1, x, x + 3, 5*x**2 + 7]

    Mixed jet variables of a PDE are split as well, and coefficients
    depending on u itself (not a jet variable) stay together:

    >>> u = Function('u')(x, t)
    >>> ux, ut = Derivative(u, x), Derivative(u, t)
    >>> split_jet_coefficients(u * ux * ut + x * ux * ut + ux**2 / u - x, [u])
    [1, x, x + u(x, t)]

    Jet variables in a denominator (as after solving for the highest
    derivative) are cleared:

    >>> split_jet_coefficients(x * d2 - x / d1 + 1, [y])
    [1, x]

    Exponentials of jet variables are split off as well: p**k * exp(m*a*p)
    are linearly independent functions of the jet variable p:

    >>> split_jet_coefficients(x * d1 * exp(y * d1) + x**2 * exp(2 * y * d1) + d1 - 1, [y])
    [1, x, x**2]

    So are powers of jet variables with a symbolic exponent, the exponent
    being generic (Kamke 6.57, y'' = a (x y' - y)**r):

    >>> r = Symbol('r')
    >>> split_jet_coefficients(x * (x * d1 - y) ** r + (x * d1 - y) ** (r - 1) + d1, [y])
    [x, x**2, -x*y(x) + 1, y(x)]
    """
    jet = {d: Dummy() for d in expr.atoms(Derivative) if d.expr in dep}
    expr = expr.xreplace(jet)
    to_symbol = {d: Symbol(d.name) for d in dep}
    expr = expr.xreplace(to_symbol).doit(simplify=False)
    expr, pow_gens = _power_generators(expr, list(jet.values()))
    # after solving for the highest derivative, jet variables may occur
    # in denominators; multiply by the jet-dependent part of the
    # denominator (it does not change where the expression vanishes)
    num, den = fraction(together(expr))
    other_den, _ = den.as_independent(*jet.values(), *pow_gens, as_Add=False)
    expr = (num / other_den).expand()
    expr, exp_gens = _exp_generators(expr, list(jet.values()))
    coeffs = Poly(expr, *jet.values(), *pow_gens, *exp_gens).coeffs() if jet else [expr]
    back = {v: k for k, v in to_symbol.items()}
    result = set()
    for c in coeffs:
        c = numer(cancel(c)).expand().xreplace(back)
        if c != 0:
            if not c.is_Add:
                # a single term: its numeric factor does not matter, e.g.
                # -4*Derivative(Y, x) = 0 is Derivative(Y, x) = 0
                c = c.as_coeff_Mul()[1]
            result.add(c)
    return sorted(result, key=default_sort_key)


def _power_generators(expr: Expr, jet: Sequence[Basic]) -> tuple[Expr, list[Dummy]]:
    """Replace the powers b**e of jet-dependent b with a non-numeric
    exponent by new generators: b**(k*s + n) becomes G**k * b**n, one G per
    family (b, s), k a positive integer. For a generic exponent G is
    transcendental over the rational functions of the jet variables, so
    its powers split like independent variables."""
    pows = sorted(
        (p for p in expr.atoms(Pow) if p.base.has(*jet) and not p.exp.is_number),
        key=default_sort_key,
    )
    families: list = []  # (base, symbolic part of the exponent, generator)
    repl = {}
    for p in pows:
        n, s = p.exp.as_coeff_Add()
        for base, s0, gen in families:
            if base == p.base:
                k = cancel(s / s0)
                if k.is_Integer and k > 0:
                    repl[p] = gen**k * base**n
                    break
        else:
            gen = Dummy()
            families.append((p.base, s, gen))
            repl[p] = gen * p.base**n
    return expr.xreplace(repl), [gen for _, _, gen in families]


def _exp_generators(expr: Expr, jet: Sequence[Basic]) -> tuple[Expr, list[Dummy]]:
    """Replace the exponentials depending on the jet variables by powers of
    new generators, one per family exp(k*a), k a positive integer."""
    exps = sorted((e for e in expr.atoms(exp) if e.has(*jet)), key=default_sort_key)
    bases: list = []  # (exponent, generator)
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


def canonical_derivatives(expr: Expr, dep: Iterable[Expr]) -> Expr:
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
    return expr.xreplace(to_symbol).doit(simplify=False).expand().xreplace(back)


def _canonical_derivatives_of(expr: Expr, dep: Variables) -> Expr:
    """expr with the derivatives of the dependent variables in SymPy's
    canonical order of the variables. An unevaluated Derivative(u, x, t) is
    not the same as Derivative(u, t, x), the form diff gives and the
    prolongation uses; without this the mixed highest derivative of a PDE
    written that way would not be found (sine-Gordon u_xt = sin(u) gave
    infinitely many symmetries).

    Derivatives of expressions in the dependent variables, as in an equation
    in divergence form, are evaluated: (u**2 u_x)_x becomes
    2 u u_x**2 + u**2 u_xx.

    >>> from sympy import sin
    >>> x, t = Symbol('x'), Symbol('t')
    >>> u = Function('u')(x, t)
    >>> _canonical_derivatives_of(Derivative(u, x, t) - sin(u), [u])
    -sin(u(x, t)) + Derivative(u(x, t), t, x)
    >>> _canonical_derivatives_of(Derivative(u**2 * Derivative(u, x), x), [u])
    u(x, t)**2*Derivative(u(x, t), (x, 2)) + 2*u(x, t)*Derivative(u(x, t), x)**2
    """
    dep = convert_to_iterable(dep)
    derivatives = [d for d in expr.atoms(Derivative) if d.expr.has(*dep)]
    return expr.xreplace({d: d.doit(simplify=False) for d in derivatives})


def convert_to_iterable(item: Variables) -> list[Any]:
    """item as a list: a single variable becomes [item]."""
    return list(item) if isinstance(item, Iterable) else [item]


def create_infinitesimals(
    dep: Basic | Iterable[Basic], indep: Basic | Iterable[Basic], inf: InfinitesimalNames = None
) -> Infinitesimals:
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
    infinitesimals: Infinitesimals = OrderedDict()
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


def _leading_derivative(eq: Expr, candidates: set[Expr], dep: list[Function]) -> Expr:
    """The highest derivative to solve eq for, independent of the hash seed.

    Preferred is a derivative in which eq is linear with a coefficient free of
    the dependent variables and their derivatives (solving for it divides by
    no jet variable), then one in which eq is linear at all; ties are broken by
    the canonical order of SymPy expressions.

    >>> x, t, tau0, k0, n = symbols('x t tau0 k0 n')
    >>> u = Function('u')(x, t)
    >>> eq = tau0 * u.diff(t, 2) + u.diff(t) - k0 * u.diff(x) ** n * u.diff(x, 2)
    >>> _leading_derivative(eq, {u.diff(t, 2), u.diff(x, 2)}, [u])
    Derivative(u(x, t), (t, 2))
    """
    dep_names = {_.name for _ in dep}
    h = Dummy()

    def rank(d: Expr) -> int:
        try:
            p = Poly(numer(together(eq.xreplace({d: h}))), h)
        except PolynomialError:
            return 2
        if p.degree() != 1:
            return 2
        jet_free = not any(a.func.__name__ in dep_names for a in p.LC().atoms(AppliedUndef))
        return 0 if jet_free else 1

    return min(candidates, key=lambda d: (rank(d), default_sort_key(d)))


def compute_overdetermined_system_of_infinitesimals(
    eq: Expr,
    dep: Variables,
    indep: Variables,
    infinitesimals: InfinitesimalNames = None,
) -> list[Expr]:
    """
    infinitesimals : dict{Function/Symbol : new name}

    An ODE that is not linear in its highest derivative, y''**2 = y',
    with the symmetries d/dx, d/dy and x d/dx + 3 y d/dy:

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> for _ in janet_basis_from_ode(diff(y, x, 2) ** 2 - diff(y, x), y, x):
    ...     print(_)
    D(Y(y(x), x), (y(x), 2))
    D(X(y(x), x), x) + (-1/3) * D(Y(y(x), x), y(x))
    D(X(y(x), x), y(x))
    D(Y(y(x), x), x)
    """
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    eq = _canonical_derivatives_of(eq, dep)

    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    _, highest_terms = order(eq, dep, indep)
    highest_term = _leading_derivative(eq, highest_terms, dep)

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


def overdetermined_system_ode(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    ode: Expr,
    dependent: Variables,
    independent: Variables,
    infinitesimals: InfinitesimalNames = None,
    *args: object,
    **kw: object,
) -> list[Expr]:
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
    -3*X_xxy - 2*X_xy*y + 3*Y_xyy + Y_yy*y
    -3*X_xyy - X_yy*y + Y_yyy
    -9*X_xy + X_y*y + 3*Y_yy
    -X_xx*y - X_xxx + 3*Y_xxy + 2*Y_xy*y
    X_x*y - 3*X_xx + Y + 3*Y_xy
    X_y
    X_yy
    X_yyy
    Y_xx*y + Y_xxx
    """
    result = compute_overdetermined_system_of_infinitesimals(
        ode, dependent, independent, infinitesimals=infinitesimals
    )
    result = [finish_substitution(_) for _ in result]
    return result


def overdetermined_system_odes(  # pylint: disable=keyword-arg-before-vararg
    eqs: list[Expr],
    dependent: Variables,
    independent: Variables,
    infinitesimals: InfinitesimalNames = None,
    *args: Any,
    **kw: Any,
) -> list[Expr]:
    """Determining equations for the Lie point symmetries of a system of
    ODEs, one equation per dependent variable.

    Every equation is solved for its leading derivative; the prolongation
    of each equation is then taken on the solution manifold of the whole
    system, i.e. all leading derivatives and their derivatives are
    substituted before splitting on the remaining jet variables.

    >>> # Arrigo, Example 2.21
    >>> from delierium.helpers import ltf
    >>> t = Symbol('t')
    >>> x, y = Function('x')(t), Function('y')(t)
    >>> infinitesimals = OrderedDict(
    ...     (v, make_infinitesimal(v, t, x, y, name=n)) for v, n in [(t, 'T'), (x, 'X'), (y, 'Y')]
    ... )
    >>> odes = [diff(x, t) - 2 * x * y, diff(y, t) - x**2 - y**2]
    >>> inf = overdetermined_system_odes(odes, [x, y], [t], infinitesimals=infinitesimals)
    >>> for _ in inf:  # doctest: +NORMALIZE_WHITESPACE
    ...     print(
    ...         ltf(_, [infinitesimals[x], infinitesimals[y]], [infinitesimals[t]], printer=False)
    ...     )
    -2*T_t*x*y - 4*T_x*x**2*y**2 - 2*T_y*x**3*y - 2*T_y*x*y**3 - 2*X*y + X_t + 2*X_x*x*y +
    X_y*x**2 + X_y*y**2 - 2*Y*x
    -T_t*x**2 - T_t*y**2 - 2*T_x*x**3*y - 2*T_x*x*y**3 - T_y*x**4 - 2*T_y*x**2*y**2 - T_y*y**4 -
    2*X*x - 2*Y*y + Y_t + 2*Y_x*x*y + Y_y*x**2 + Y_y*y**2
    """
    eqs = [_canonical_derivatives_of(eq, dependent) for eq in eqs]
    dep = convert_to_iterable(dependent)
    indep = convert_to_iterable(independent)
    if len(eqs) == 1 and len(dep) == 1:
        return overdetermined_system_ode(eqs[0], dep, indep, infinitesimals, *args, **kw)
    if len(indep) != 1:
        raise NotImplementedError("systems of ODEs only, i.e. one independent variable")
    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    reduce_on_system = _ode_system_reduction(eqs, dep, indep[0])
    result: list[Expr] = []
    for eq in eqs:
        r = reduce_on_system(prolongation(eq, infinitesimals, dep, indep))
        for c in split_jet_coefficients(r, dep):
            c = finish_substitution(c)
            if not any((c - _).expand() == 0 for _ in result):
                result.append(c)
    return result


def _ode_system_reduction(
    eqs: Sequence[Expr], dep: list[Expr], t: Symbol
) -> Callable[[Expr], Expr]:
    """Solve a system of ODEs for one leading derivative per equation and
    return the function that replaces every leading derivative, and every
    derivative of it, by its value on the solutions of the system.
    """
    rhs = _solved_form(eqs, dep, t)

    def reducible(expr: Expr) -> list[Derivative]:
        return [
            d
            for d in expr.atoms(Derivative)
            if d.expr in rhs and d.derivative_count >= rhs[d.expr][0]
        ]

    _check_termination(rhs, reducible)

    def reduce_on_system(expr: Expr) -> Expr:
        while derivatives := reducible(expr):
            replacements = {}
            for d in derivatives:
                n, value = rhs[d.expr]
                replacements[d] = diff(value, t, d.derivative_count - n)
            expr = expr.xreplace(replacements)
        return expr

    return reduce_on_system


def _solved_form(
    eqs: Sequence[Expr], dep: list[Expr], t: Symbol
) -> dict[Expr, tuple[Integer, Expr]]:
    """{dependent variable: (order of its leader, value of its leader)}.

    The leading derivative of an equation is one of its highest
    derivatives; different equations need leaders of different dependent
    variables, and every equation has to be linear in its leader.
    """
    candidates = [sorted(order(eq, dep, [t])[1], key=default_sort_key) for eq in eqs]
    for leaders in product(*candidates):
        if len({_.expr for _ in leaders}) == len(leaders):
            break
    else:
        raise NotImplementedError("no distinct leading derivatives for the equations")
    rhs = {}
    for eq, leader in zip(eqs, leaders, strict=True):
        h = Dummy()
        if Poly(numer(together(eq.xreplace({leader: h}))), h).degree() != 1:
            raise NotImplementedError(f"{eq} is not linear in {leader}")
        rhs[leader.expr] = (leader.derivative_count, solve(eq, leader)[0])
    return rhs


def _check_termination(
    rhs: dict[Expr, tuple[Integer, Expr]], reducible: Callable[[Expr], list[Derivative]]
) -> None:
    """For the reduction to terminate, there has to be an orderly ranking
    (by order, then by the dependent variable) in which every reducible
    derivative on the right-hand side of an equation is lower than its
    leader: then every replacement brings in lower derivatives only, also
    after differentiation."""

    def is_orderly_ranking(variables: Sequence[Expr]) -> bool:
        rank = {f: i for i, f in enumerate(variables)}
        return all(
            (d.derivative_count, rank[d.expr]) < (n, rank[f])
            for f, (n, value) in rhs.items()
            for d in reducible(value)
        )

    if not any(is_orderly_ranking(_) for _ in permutations(rhs)):
        raise NotImplementedError("the reduction of the system by its equations may not terminate")


def overdetermined_system_pde(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    pde: Expr,
    dependent: Variables,
    independent: Variables,
    infinitesimals: InfinitesimalNames = None,
    *args: object,
    **kw: object,
) -> list[Expr]:
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
    -2*U_ux - X_t + X_xx
    -T_t + T_xx + 2*X_x
    -U_uu + 2*X_ux
    2*T_ux + 2*X_u
    T_u
    T_uu
    T_x
    U_t - U_xx
    X_uu
    """
    if len(convert_to_iterable(dependent)) != 1:
        raise NotImplementedError("only one dependent variable is supported")
    result = compute_overdetermined_system_of_infinitesimals(
        pde, dependent, independent, infinitesimals=infinitesimals
    )
    return [finish_substitution(_) for _ in result]


def _linear_system_ode(
    ode: Expr, dependent: Expr, independent: Symbol, infinitesimals: InfinitesimalNames = None
) -> tuple[list[Expr], list[Expr], list[Symbol], Symbol]:
    """The determining equations of an ODE as a linear system for JanetBasis.

    Returns (system, dependents, independents, h_symbol): the dependent
    variable y(x) is replaced by the symbol H, so the infinitesimals become
    functions of (H, x). (After splitting, the determining equations no
    longer contain derivatives of y.)
    """
    infinitesimals = create_infinitesimals([dependent], [independent], infinitesimals)
    overdetermined_system = overdetermined_system_ode(
        ode, [dependent], [independent], infinitesimals=infinitesimals
    )
    h_symbol = Symbol("H")
    inf = [infinitesimals[_] for _ in [dependent, independent]]

    r1 = [h_symbol, independent]
    inf = [_.xreplace({dependent: h_symbol}) for _ in inf]
    system = [e.replace(dependent, h_symbol) for e in overdetermined_system]
    return system, list(reversed(inf)), list(reversed(r1)), h_symbol


def janet_basis_from_ode(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    ode: Expr,
    dependent: Expr,
    independent: Symbol,
    sort_order: WeightFunction = Mgrevlex,
    infinitesimals: InfinitesimalNames = None,
    *args: object,
    **kw: object,
) -> LHDPList:
    system, inf, r1, h_symbol = _linear_system_ode(ode, dependent, independent, infinitesimals)
    janet = JanetBasis(system, inf, r1, sort_order=sort_order)
    return _back_substituted(janet, {h_symbol: dependent}, sort_order)


def _back_substituted(
    janet: JanetBasis, back: Mapping[Basic, Basic], sort_order: WeightFunction
) -> LHDPList:
    """The elements of a Janet basis as LHDPs, with the symbols standing for
    the dependent variables replaced back by them (back: symbol -> function)."""

    def back_substitute(e: Expr) -> Expr:
        return e.xreplace(back)

    res = []
    for lhdp in janet.S:
        p = []
        for term in lhdp.p:
            coeff = back_substitute(term.coeff.as_expr())
            d = back_substitute(term.derivative)
            ctx = Context(
                dependent=[back_substitute(_) for _ in term.context.dependent],
                independent=[back_substitute(_) for _ in term.context.independent],
                weight=sort_order,
            )
            p.append(_Dterm(derivative=d, coeff=coeff, context=ctx))
        res.append(LHDP(e=0, context=ctx, dterms=p))

    def assumptions() -> tuple[list[Expr], list[list[Expr]], list[Expr]]:
        return (
            nonzero_factors([back_substitute(f) for f in janet.assumed_nonzero()]),
            janet.parameter_conditions(),
            [back_substitute(f) for f in janet.singular_loci()],
        )

    return LHDPList(reorder(res, context=ctx), assumptions)


def _linear_system_odes(
    eqs: list[Expr],
    dependent: Variables,
    independent: Variables,
    infinitesimals: InfinitesimalNames = None,
) -> tuple[list[Expr], list[Expr], list[Basic], dict[Expr, Symbol]]:
    """The determining equations of a system of ODEs as a linear system for
    JanetBasis.

    Returns (system, infinitesimals, variables, to_symbol): every dependent
    variable x(t) is replaced by a symbol of the same name, so the
    infinitesimals become functions of (t, x, y, ...). Infinitesimals and
    variables are ordered as for a single ODE: the independent variable
    first.
    """
    dep = convert_to_iterable(dependent)
    indep = convert_to_iterable(independent)
    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    system = overdetermined_system_odes(eqs, dep, indep, infinitesimals=infinitesimals)
    to_symbol = {d: Symbol(d.func.__name__) for d in dep}
    inf = [infinitesimals[_].xreplace(to_symbol) for _ in indep + dep]
    variables = indep + [to_symbol[_] for _ in dep]
    return [e.xreplace(to_symbol) for e in system], inf, variables, to_symbol


def janet_basis_from_odes(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    eqs: list[Expr],
    dependent: Variables,
    independent: Variables,
    sort_order: WeightFunction = Mgrevlex,
    infinitesimals: InfinitesimalNames = None,
    *args: object,
    **kw: object,
) -> LHDPList:
    """Janet basis of the determining equations of a system of ODEs, see
    overdetermined_system_odes.

    Free particle in the plane, x'' = y'' = 0; its 15 point symmetries
    (sl(4)) are the solutions of these 18 equations:

    >>> t = Symbol('t')
    >>> x, y = Function('x')(t), Function('y')(t)
    >>> B = janet_basis_from_odes([diff(x, t, 2), diff(y, t, 2)], [x, y], [t])
    >>> len(B)
    18
    >>> for _ in B[:4]:
    ...     print(_)
    D(Y(x(t), y(t), t), t, (y(t), 2))
    D(Y(x(t), y(t), t), x(t), (y(t), 2))
    D(Y(x(t), y(t), t), (y(t), 3))
    D(T(x(t), y(t), t), (t, 2)) + (-2) * D(Y(x(t), y(t), t), t, y(t))
    """
    system, inf, variables, to_symbol = _linear_system_odes(
        eqs, dependent, independent, infinitesimals
    )
    janet = JanetBasis(system, inf, variables, sort_order=sort_order)
    return _back_substituted(janet, {v: k for k, v in to_symbol.items()}, sort_order)


def is_janet_basis_of_ode(
    B: Iterable[Expr | LHDP],
    ode: Expr,
    dependent: Expr,
    independent: Symbol,
    sort_order: WeightFunction = Mgrevlex,
    infinitesimals: InfinitesimalNames = None,
    dependent_order: Sequence[Expr | str] | None = None,
    independent_order: Sequence[Basic | str] | None = None,
) -> bool:
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
    >>> ode = 8 * x * d2 * y**6 - 9 * x**5 * d1**4 - 16 * x * d1**2 * y**5 + 16 * d1 * y**6
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

    def dep_key(f: Expr | str) -> str:
        return f if isinstance(f, str) else f.func.__name__

    def ind_key(v: Basic | str) -> Basic:
        # y, y(x) and "y" all stand for the dependent variable, i.e. H
        return (Symbol(v) if isinstance(v, str) else v).xreplace(to_h)

    dep = _ranked(dependent_order, inf, dep_key)
    ind = _ranked(independent_order, r1, ind_key)
    return is_janet_basis_of(B, system, dep, ind, sort_order)


def is_janet_basis_of_odes(
    B: Iterable[Expr | LHDP],
    eqs: list[Expr],
    dependent: Variables,
    independent: Variables,
    sort_order: WeightFunction = Mgrevlex,
    infinitesimals: InfinitesimalNames = None,
    dependent_order: Sequence[Expr | str] | None = None,
    independent_order: Sequence[Basic | str] | None = None,
) -> bool:
    """Check whether B is the Janet basis of the determining equations of
    the system of ODEs eqs, see janet_basis_from_odes.

    B is written in infinitesimals T, X, Y, ... of plain symbols named like
    the variables, e.g. T(t, x, y); the order of their arguments does not
    matter. LHDPs as returned by janet_basis_from_odes are accepted as well.

    The ranking is given by sort_order and, highest first, by
    dependent_order (the infinitesimals, e.g. [Y, X, T]) and
    independent_order (e.g. [y, x, t]); the default is the one of
    janet_basis_from_odes, [T, X, Y] and [t, x, y]. Infinitesimals may be
    given by name as well.

    Kepler problem in the plane, x'' = -x/r**3, y'' = -y/r**3; its three
    point symmetries are time translation, rotation and the scaling of
    Kepler's third law:

    >>> t = Symbol('t')
    >>> x, y = Function('x')(t), Function('y')(t)
    >>> r3 = (x**2 + y**2) ** Rational(3, 2)
    >>> odes = [diff(x, t, 2) + x / r3, diff(y, t, 2) + y / r3]
    >>> xs, ys = Symbol('x'), Symbol('y')
    >>> T, X, Y = [Function(_)(t, xs, ys) for _ in 'TXY']
    >>> r2 = xs**2 + ys**2
    >>> B = [
    ...     diff(T, t) - 3 * (xs * X + ys * Y) / (2 * r2),
    ...     diff(T, xs),
    ...     diff(T, ys),
    ...     diff(X, t),
    ...     diff(X, xs) - (xs * X + ys * Y) / r2,
    ...     diff(X, ys) - (ys * X - xs * Y) / r2,
    ...     diff(Y, t),
    ...     diff(Y, xs) + (ys * X - xs * Y) / r2,
    ...     diff(Y, ys) - (xs * X + ys * Y) / r2,
    ... ]
    >>> is_janet_basis_of_odes(B, odes, [x, y], [t])
    True
    >>> is_janet_basis_of_odes(B[1:], odes, [x, y], [t])
    False
    >>> is_janet_basis_of_odes(janet_basis_from_odes(odes, [x, y], [t]), odes, [x, y], [t])
    True
    """
    system, inf, variables, to_symbol = _linear_system_odes(
        eqs, dependent, independent, infinitesimals
    )
    ours = {(f.func.__name__, frozenset(f.args)): f for f in inf}

    def normalized(b: Expr | LHDP) -> Expr:
        b = (b.expression() if isinstance(b, LHDP) else b).xreplace(to_symbol)
        return b.xreplace(
            {
                f: ours[key]
                for f in b.atoms(AppliedUndef)
                if (key := (f.func.__name__, frozenset(f.args))) in ours
            }
        )

    def dep_key(f: Expr | str) -> str:
        return f if isinstance(f, str) else f.func.__name__

    def ind_key(v: Basic | str) -> Basic:
        # x, x(t) and "x" all stand for the symbol x
        return (Symbol(v) if isinstance(v, str) else v).xreplace(to_symbol)

    dep = _ranked(dependent_order, inf, dep_key)
    ind = _ranked(independent_order, variables, ind_key)
    return is_janet_basis_of([normalized(b) for b in B], system, dep, ind, sort_order)


def _ranked[T](
    ordering: Iterable[Any] | None, default: list[T], key: Callable[[Any], Any]
) -> list[T]:
    """default, rearranged like ordering; the entries are matched by key."""
    if ordering is None:
        return default
    by_key = {key(_): _ for _ in default}
    ranked = [by_key.get(key(_)) for _ in ordering]
    if None in ranked or len(set(ranked)) != len(default):
        raise ValueError(f"{list(ordering)} is not an ordering of {default}")
    return cast(list[T], ranked)


if __name__ == "__main__":
    import doctest

    doctest.testmod()
