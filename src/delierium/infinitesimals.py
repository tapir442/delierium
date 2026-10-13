"""Infinitesimals.

Computes the overdetermined system of determining equations for the
infinitesimal generators of the Lie point symmetry group of an ODE/PDE,
via prolongation of the vector field and extraction of coefficients.
"""

from collections import OrderedDict
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from functools import reduce
from itertools import combinations, combinations_with_replacement, permutations, product
from typing import Any, cast

from sympy import (  # noqa: F401
    QQ,
    Abs,
    Add,
    Basic,
    Derivative,
    Dummy,
    Equality,
    Expr,
    Float,
    Function,
    I,
    Integer,
    Lambda,
    LambertW,
    NumberSymbol,
    Poly,
    Pow,
    Rational,
    S,
    Subs,
    Symbol,
    cancel,
    default_sort_key,
    diff,
    exp,
    expand,
    expand_log,
    fraction,
    gcd,
    ilcm,
    init_printing,
    log,
    nsimplify,
    numer,
    powdenest,
    prem,
    sign,
    simplify,
    solve,
    symbols,
    sympify,
    together,
)
from sympy.core.function import AppliedUndef
from sympy.functions.elementary.hyperbolic import HyperbolicFunction
from sympy.functions.elementary.trigonometric import TrigonometricFunction
from sympy.polys.fields import sfield
from sympy.polys.polyerrors import CoercionFailed, PolynomialError
from sympy.polys.rings import PolyElement, sring
from sympy.polys.rings import ring as sring_ring

from delierium.helpers import (
    commensurable_families,
    finish_substitution,
    func_diff,
    make_infinitesimal,
    plain_symbol,
    profile_if_enabled,
)
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
    "VerificationResult",
    "create_infinitesimals",
    "determining_janet_basis",
    "is_janet_basis_of_ode",
    "is_janet_basis_of_odes",
    "janet_basis_from_ode",
    "janet_basis_from_odes",
    "overdetermined_system_ode",
    "overdetermined_system_odes",
    "overdetermined_system_pde",
    "prolongation",
    "verify_symmetries",
    "verify_symmetry",
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

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> order(y.diff(x, 3) + y.diff(x) ** 2, [y], [x])
    (3, {Derivative(y(x), (x, 3))})
    """
    max_order = 0
    max_deriv: set[Expr] = set()
    dep_names = [d.name for d in dep]
    for atom in expr.expand().atoms(Derivative):
        if atom.args[0].name in dep_names:
            atom_order = len(atom.variables)
            if max_order == atom_order:
                max_deriv |= {atom}
            elif max_order < atom_order:
                max_deriv = {atom}
                max_order = atom_order
    return (max_order, max_deriv)


@profile_if_enabled
def prolonged_infinitesimals(
    dep: list[Expr],
    indep: list[Symbol],
    infinitesimals: Mapping[Basic, Expr],
    max_order: int,
) -> OrderedDict[Basic, Expr]:
    """The infinitesimals of all derivatives of the dependent variables up
    to max_order, {Derivative(u, *J): phi_J}, in the order of
    variable_combinations.

    Computed in jet coordinates: x, u and the derivatives u_J are plain
    symbols, and with the characteristic Q = phi - sum_i xi^i u_i
    (Olver, Theorem 2.36)

        phi_J = D_J Q + sum_i xi^i u_{J,i},
        D_i F = dF/dx^i + sum_{u, J} u_{J,i} dF/du_J,

    D_J Q from D_{J-i} Q (each multi-index once). Then x, u, u_J are put
    back: u(x), Derivative(u(x), ...), Derivative(X(x, u(x)), u(x)).

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> X = make_infinitesimal(x, x, y, name='X')
    >>> Y = make_infinitesimal(y, x, y, name='Y')
    >>> from delierium.helpers import ltf
    >>> etas = prolonged_infinitesimals([y], [x], {x: X, y: Y}, 2)
    >>> list(etas)
    [Derivative(y(x), x), Derivative(y(x), (x, 2))]
    >>> print(ltf(etas[y.diff(x)].expand(), [Y], [X], printer=False))
    -X_x*y_x - X_y*y_x**2 + Y_x + Y_y*y_x
    >>> eta = etas[y.diff(x, 2)].expand()
    >>> print(ltf(eta, [Y], [X], printer=False))  # doctest: +NORMALIZE_WHITESPACE
    -2*X_x*y_xx - X_xx*y_x - 2*X_xy*y_x**2 - 3*X_y*y_x*y_xx - X_yy*y_x**3 + Y_xx + 2*Y_xy*y_x +
    Y_y*y_xx + Y_yy*y_x**2

    Two independent variables (PDE case): eta^t for u(x, t):

    >>> t = Symbol('t')
    >>> u = Function('u')(x, t)
    >>> Xi = make_infinitesimal(x, x, t, u, name='X')
    >>> T = make_infinitesimal(t, x, t, u, name='T')
    >>> U = make_infinitesimal(u, x, t, u, name='U')
    >>> etas = prolonged_infinitesimals([u], [x, t], {x: Xi, t: T, u: U}, 2)
    >>> list(etas)  # doctest: +NORMALIZE_WHITESPACE
    [Derivative(u(x, t), x), Derivative(u(x, t), t), Derivative(u(x, t), (x, 2)),
    Derivative(u(x, t), t, x), Derivative(u(x, t), (t, 2))]
    >>> print(ltf(etas[u.diff(t)].expand(), [U], [Xi, T], printer=False))
    -T_t*u_t - T_u*u_t**2 + U_t + U_u*u_t - X_t*u_x - X_u*u_t*u_x
    """
    space = _JetSpace(dep, indep)
    symbolic = space.symbolic([infinitesimals[v] for v in (*indep, *dep)])
    # polynomials in the jet coordinates (X(x, u) arbitrary): in a ring
    symbolic = space.in_ring(symbolic, max_order)
    etas = space.prolonged(symbolic, max_order)
    back = space.back()
    return OrderedDict(
        (
            dep[a].diff(*(indep[i] for i in multi)),
            _partials_in_argument_order(space.as_expr(eta).xreplace(back), dep),
        )
        for (a, multi), eta in etas.items()
    )


class _JetSpace:
    """Jet coordinates for prolonged_infinitesimals: x, u and the u_J are
    symbols, and so are the infinitesimals X(x, u) and their partial
    derivatives, X_K for the counts K by argument: SymPy differentiates
    functions and Derivatives much more slowly than symbols."""

    def __init__(self, dep: list[Expr], indep: list[Symbol]) -> None:
        """No jets yet but u for every dependent variable u(x).

        >>> x = Symbol('x')
        >>> space = _JetSpace([Function('y')(x)], [x])
        >>> list(space.base.values())
        [_y]
        """
        self.dep, self.indep = dep, indep
        self.base = {d: Dummy(d.func.__name__) for d in dep}
        self.jets: dict[tuple[int, tuple[int, ...]], Symbol] = {}
        # symbol -> (a, J)
        self.jet_of: dict[Basic, tuple[int, tuple[int, ...]]] = {
            self.base[d]: (a, ()) for a, d in enumerate(dep)
        }
        self.partials: dict[tuple[Basic, tuple[int, ...]], Symbol] = {}
        # symbol -> (X(x, u), K)
        self.partial_of: dict[Basic, tuple[Basic, tuple[int, ...]]] = {}
        # the polynomial ring of the jet coordinates (in_ring), its generators
        self.ring: Any = None
        self.gens: dict[Basic, Any] = {}
        self._total: dict[tuple[Basic, int], Any] = {}

    def jet(self, a: int, multi: tuple[int, ...]) -> Symbol:
        """The symbol for the derivative of the a-th dependent variable by
        the independent variables with the indices multi.

        >>> x, t = symbols('x t')
        >>> space = _JetSpace([Function('u')(x, t)], [x, t])
        >>> space.jet(0, (1, 0)), space.jet(0, (0, 1)) == space.jet(0, (1, 0))
        (_u_xt, True)
        """
        multi = tuple(sorted(multi))
        if not multi:
            symbol = self.base[self.dep[a]]
        else:
            if (a, multi) not in self.jets:
                name = f"{self.dep[a].func.__name__}_{''.join(str(self.indep[i]) for i in multi)}"
                self.jets[(a, multi)] = s = Dummy(name)
                self.jet_of[s] = (a, multi)
            symbol = self.jets[(a, multi)]
        return self.gens[symbol] if self.ring is not None else symbol

    def partial_symbol(self, f: Basic, counts: tuple[int, ...]) -> Symbol:
        """The symbol for the partial derivative of f with the counts by
        argument.

        >>> x = Symbol('x')
        >>> space = _JetSpace([Function('y')(x)], [x])
        >>> X = Function('X')(x, space.base[space.dep[0]])
        >>> space.partial_symbol(X, (1, 0))
        _X(1, 0)
        """
        if (f, counts) not in self.partials:
            self.partials[(f, counts)] = s = Dummy(f"{f.func.__name__}{counts}")
            self.partial_of[s] = (f, counts)
        return self.partials[(f, counts)]

    def symbolic(self, infinitesimals: list[Expr]) -> list[Expr]:
        """The infinitesimals with u for u(x) and with symbols for the
        functions of x and u (none if they hold derivatives already).

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> space = _JetSpace([y], [x])
        >>> space.symbolic([Function('X')(x, y), x * y])
        [_X(0, 0), _y*x]
        """
        plain = {d: self.base[d] for d in self.dep}
        result = [finish_substitution(e).xreplace(plain) for e in infinitesimals]
        if any(e.has(Derivative, Subs) for e in result):
            return result
        coordinates = {*self.indep, *self.base.values()}
        functions = {
            f
            for e in result
            for f in e.atoms(AppliedUndef)
            if f.args and set(f.args) <= coordinates and len(set(f.args)) == len(f.args)
        }
        as_symbols = {f: self.partial_symbol(f, (0,) * len(f.args)) for f in functions}
        return [e.xreplace(as_symbols) for e in result]

    def partial(self, F: Expr, c: Basic) -> Expr:
        """dF/dc for a coordinate c (x or u), also through the X_K.

        >>> x = Symbol('x')
        >>> space = _JetSpace([Function('y')(x)], [x])
        >>> (X,) = space.symbolic([Function('X')(x, Function('y')(x))])
        >>> space.partial(x * X, x)
        _X(0, 0) + _X(1, 0)*x
        """
        result = F.diff(c)
        for s in F.free_symbols & self.partial_of.keys():
            f, counts = self.partial_of[s]
            if c in f.args:
                k = f.args.index(c)
                higher = (*counts[:k], counts[k] + 1, *counts[k + 1 :])
                result += F.diff(s) * self.partial_symbol(f, higher)
        return result

    def total(self, F: Expr, i: int) -> Expr:
        """D_i F, F depending on x, u, finitely many u_J and X_K.

        >>> x = Symbol('x')
        >>> space = _JetSpace([Function('y')(x)], [x])
        >>> (X,) = space.symbolic([Function('X')(x, Function('y')(x))])
        >>> space.total(X, 0)
        _X(0, 1)*_y_x + _X(1, 0)
        """
        if self.ring is not None:
            return self._ring_total(F, i)
        result = self.partial(F, self.indep[i])
        free = F.free_symbols
        # u also where it is only an argument of an X_K
        hidden = {v for s in free & self.partial_of.keys() for v in self.partial_of[s][0].args}
        for s in (free | hidden) & self.jet_of.keys():
            a, multi = self.jet_of[s]
            derivative = F.diff(s) if multi else self.partial(F, s)
            result += self.jet(a, (*multi, i)) * derivative
        return result

    def prolonged(
        self, symbolic: list[Any], max_order: int
    ) -> dict[tuple[int, tuple[int, ...]], Any]:
        """{(a, J): phi_J} for the infinitesimals xi, phi of the
        coordinates (from symbolic or in_ring), J up to max_order in the
        order of variable_combinations, see prolonged_infinitesimals.

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> space = _JetSpace([y], [x])
        >>> list(space.prolonged(space.symbolic([Integer(1), Integer(0)]), 2).values())
        [0, 0]
        """
        n = len(self.indep)
        xi, phi = symbolic[:n], symbolic[n:]
        dq = {
            # started with the first term, not Integer(0): ring elements
            (a, ()): phi_a
            - sum((xi[i] * self.jet(a, (i,)) for i in range(1, n)), xi[0] * self.jet(a, (0,)))
            for a, phi_a in enumerate(phi)
        }
        result = {}
        for combi in variable_combinations(list(range(n)), max_order):
            multi = tuple(combi)
            for a in range(len(self.dep)):
                dq[(a, multi)] = self.total(dq[(a, multi[:-1])], multi[-1])
                result[(a, multi)] = dq[(a, multi)] + sum(
                    xi[i] * self.jet(a, (*multi, i)) for i in range(n)
                )
        return result

    def coordinates(self, e: Expr) -> Expr:
        """e with u for u(x) and the jet symbols for its derivatives.

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> _JetSpace([y], [x]).coordinates(x * y.diff(x, 2) + y)
        _y + _y_xx*x
        """
        index = {v: i for i, v in enumerate(self.indep)}
        jets: dict[Basic, Basic] = {}
        for d in e.atoms(Derivative):
            if d.expr in self.dep and all(v in index for v in d.variables):
                a = self.dep.index(d.expr)
                jets[d] = self.jet(a, tuple(index[v] for v in d.variables))
        return e.xreplace(jets).xreplace(self.base)

    def in_ring(self, infinitesimals: list[Expr], max_order: int) -> list[Any]:
        """The infinitesimals (from symbolic) as elements of the polynomial
        ring of the jet coordinates up to max_order + 1 and the X_K up to
        max_order, the other symbols (parameters) as constants; unchanged
        if they are no polynomials in them (concrete infinitesimals, 1/x).

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> space = _JetSpace([y], [x])
        >>> X, Y = space.in_ring(space.symbolic([Function('X')(x, y), y]), 1)
        >>> space.ring is not None, space.as_expr(Y)
        (True, _y)
        >>> space = _JetSpace([y], [x])
        >>> space.in_ring(space.symbolic([1 / x, y]), 1), space.ring
        ([1/x, _y], None)
        """
        n = len(self.indep)
        for a in range(len(self.dep)):
            for k in range(1, max_order + 2):
                for multi in combinations_with_replacement(range(n), k):
                    self.jet(a, multi)
        for f, _ in list(self.partials):
            for k in range(1, max_order + 1):
                for positions in combinations_with_replacement(range(len(f.args)), k):
                    self.partial_symbol(f, tuple(positions.count(p) for p in range(len(f.args))))
        coordinates = [*self.indep, *self.base.values(), *self.jets.values()]
        coordinates += self.partials.values()
        known = set(coordinates)
        # parameters and constants (pi)
        constants = {v for e in infinitesimals for v in e.free_symbols | e.atoms(NumberSymbol)}
        others = sorted(constants - known, key=str)
        gens = [*coordinates, *others]
        ring_, *elements = sring_ring(gens, QQ)
        try:
            result = [ring_.from_expr(e) for e in infinitesimals]
        except (ValueError, CoercionFailed):
            return infinitesimals
        self.ring = ring_
        self.gens = dict(zip(gens, elements, strict=True))
        return result

    def as_expr(self, e: Any) -> Expr:
        """e as a SymPy expression, also if it is a ring element.

        >>> x = Symbol('x')
        >>> space = _JetSpace([Function('y')(x)], [x])
        >>> (Y,) = space.in_ring([x**2], 1)
        >>> space.as_expr(Y), space.as_expr(x)
        (x**2, x)
        """
        return e.as_expr() if self.ring is not None and isinstance(e, PolyElement) else e

    def _total_of_generator(self, g: Basic, i: int) -> Any:
        """D_i of the generator g in the ring: 1 or 0 for the independent
        variables, u_{J,i} for u_J, X_{K+i} + sum_a X_{K+u_a} u_{a,i} for
        X_K, 0 for the parameters.

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> space = _JetSpace([y], [x])
        >>> (X,) = space.in_ring(space.symbolic([Function('X')(x, y)]), 1)
        >>> space.as_expr(space._total_of_generator(space.base[y], 0))
        _y_x
        """
        if (g, i) in self._total:
            return self._total[(g, i)]
        R = self.ring
        if g in self.jet_of:
            a, multi = self.jet_of[g]
            result = self.jet(a, (*multi, i))
        elif g in self.partial_of:
            f, counts = self.partial_of[g]
            result = R.zero
            for k, v in enumerate(f.args):
                higher = (*counts[:k], counts[k] + 1, *counts[k + 1 :])
                if v == self.indep[i]:
                    result += self.gens[self.partial_symbol(f, higher)]
                elif v in self.jet_of:
                    a, _ = self.jet_of[v]
                    result += self.gens[self.partial_symbol(f, higher)] * self.jet(a, (i,))
        else:
            result = R.one if g == self.indep[i] else R.zero
        self._total[(g, i)] = result
        return result

    def _ring_total(self, F: Any, i: int) -> Any:
        """D_i F for F in the ring: the sum of dF/dg * D_i g over its
        generators g.

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> space = _JetSpace([y], [x])
        >>> (X,) = space.in_ring(space.symbolic([x * Function('X')(x, y)]), 1)
        >>> space.as_expr(space._ring_total(X, 0))
        _X(0, 0) + _X(0, 1)*_y_x*x + _X(1, 0)*x
        """
        generators = list(self.gens)
        present = {k for monomial in F.itermonoms() for k, e in enumerate(monomial) if e}
        result = self.ring.zero
        for k in present:
            g = generators[k]
            derivative = self._total_of_generator(g, i)
            if derivative:
                result += F.diff(self.gens[g]) * derivative
        return result

    def back(self) -> dict[Basic, Basic]:
        """The symbols to put back: u(x), Derivative(u(x), ...), X(x, u(x))
        and its derivatives, these in the order of the arguments as in
        _partials_in_argument_order.

        >>> x = Symbol('x')
        >>> y = Function('y')(x)
        >>> space = _JetSpace([y], [x])
        >>> (X,) = space.symbolic([Function('X')(x, y)])
        >>> sorted(space.total(X, 0).xreplace(space.back()).args, key=str)
        [Derivative(X(x, y(x)), x), Derivative(X(x, y(x)), y(x))*Derivative(y(x), x)]
        """
        back: dict[Basic, Basic] = {self.base[d]: d for d in self.dep}
        for (a, multi), sym in self.jets.items():
            # diff() as in the rest of delierium: the canonical order u_tx
            back[sym] = self.dep[a].diff(*(self.indep[i] for i in multi))
        for (f, counts), sym in self.partials.items():
            g = f.xreplace(back)
            pairs = [(v.xreplace(back), k) for v, k in zip(f.args, counts, strict=True) if k]
            back[sym] = Derivative(g, *pairs) if pairs else g
        return back


def _partials_in_argument_order(e: Expr, dep: list[Expr]) -> Expr:
    """e with the mixed partials of the infinitesimals in the order of their
    arguments, X_yx for X(y, x): one form for one derivative. Those of the
    dependent variables stay in SymPy's canonical order, u_tx, as in the
    equation.

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> X = Function('X')(y, x)
    >>> _partials_in_argument_order(Derivative(X, x, y) + Derivative(y, x), [y]).args[1].variables
    (y(x), x)
    """

    def in_argument_order(d: Derivative) -> Derivative:
        args = list(d.expr.args)
        return Derivative(d.expr, *sorted(d.variable_count, key=lambda vc: args.index(vc[0])))

    return e.xreplace(
        {
            d: in_argument_order(d)
            for d in e.atoms(Derivative)
            if isinstance(d.expr, AppliedUndef)
            and d.expr not in dep
            and all(v in d.expr.args for v in d.variables)
        }
    )


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
    infinitesimals = OrderedDict(
        (k, finish_substitution(sympify(v))) for k, v in infinitesimals.items()
    )
    dummies: OrderedDict[Basic, Symbol] = OrderedDict()
    etas = prolonged_infinitesimals(dep, indep, infinitesimals, order(expr, dep, indep)[0])
    for func, eta in etas.items():
        infinitesimals[func] = eta
        suffix = "".join(str(v) for v in func.variables)
        dummies[func] = Symbol(f"{func.expr.func.__name__}_{suffix}")
    for v in dep + indep:
        dummies[v] = Symbol(v.name)

    reverse_dummies = {v: k for k, v in dummies.items()}
    acc = sum(
        infinitesimals[v]
        * func_diff(expr.xreplace(dummies), v.xreplace(dummies)).xreplace(reverse_dummies)
        for v in infinitesimals
    )
    return finish_substitution(acc)


def jet_power_conditions(expr: Expr, dep: Sequence[Expr]) -> list[list[Expr]]:
    """The conditions on the parameters under which two monomials of expr in
    the jet variables coincide: split_jet_coefficients takes them as
    different (a symbolic exponent is generic), so where they coincide there
    may be fewer determining equations and more symmetries (#16).

    Each condition is a list of expressions that vanish together: the
    differences of the exponents of two monomials, as long as none of them
    is a nonzero number (then the monomials never coincide).

    >>> from sympy import Function, symbols
    >>> x, p, q = symbols("x p q")
    >>> y = Function("y")(x)
    >>> u1, u2 = y.diff(x), y.diff(x, 2)
    >>> e = u1 ** (p - 1) * u2 + u1**2 * u2 + u1 ** (q + 1) * u2 + u1 ** (q + 1)
    >>> jet_power_conditions(e, [y])  # u1**(q + 1) alone differs by u2
    [[p - 3], [q - 1], [-p + q + 2]]
    """
    jet = {d: Dummy() for d in expr.atoms(Derivative) if d.expr in dep}
    if not jet:
        return []
    jets = list(jet.values())
    numerator = numer(together(expr.xreplace(jet))).expand()
    vectors = []
    for term in Add.make_args(numerator):
        powers = term.as_powers_dict()
        vector = tuple(powers.get(v, 0) for v in jets)
        if vector not in vectors:
            vectors.append(vector)
    conditions: list[list[Expr]] = []
    for v1, v2 in combinations(vectors, 2):
        differences = [numer(together(a - b)) for a, b in zip(v1, v2, strict=True)]
        if any(d.is_number and d != 0 for d in differences):
            continue
        condition = sorted(
            {-d if d.could_extract_minus_sign() else d for d in differences if d != 0},
            key=default_sort_key,
        )
        if condition and condition not in conditions:
            conditions.append(condition)
    return sorted(conditions, key=default_sort_key)


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
    # an equation with complex coefficients has complex symmetries: only the
    # I of trigonometric functions written as exponentials is split off
    complex_coefficients = expr.has(I)
    jet = {d: Dummy() for d in expr.atoms(Derivative) if d.expr in dep}
    expr = expr.xreplace(jet)
    to_symbol = {d: Symbol(d.name) for d in dep}
    expr = expr.xreplace(to_symbol).doit(simplify=False)
    jets = list(jet.values())
    # trigonometric and hyperbolic functions of jet variables as
    # exponentials, which _exp_generators splits (sin**2 + cos**2 = 1 would
    # be lost if sin and cos were independent generators)
    expr = expr.replace(
        lambda a: isinstance(a, (TrigonometricFunction, HyperbolicFunction)) and a.has(*jets),
        lambda a: a.rewrite(exp),
    )
    expr, pow_gens = _power_generators(expr, jets)
    expr, alg_gens, relations = _algebraic_generators(expr, jets)
    expr, fun_gens = _function_generators(expr, jets)
    gens = [*jets, *pow_gens, *alg_gens, *fun_gens]
    # after solving for the highest derivative, jet variables may occur
    # in denominators; multiply by the jet-dependent part of the
    # denominator (it does not change where the expression vanishes)
    num, den = fraction(together(expr))
    other_den, _ = den.as_independent(*gens, as_Add=False)
    coeffs: list[Expr] | None = None
    if other_den == 1 and not alg_gens and jet:
        # the usual case: the coefficients of the numerator directly, in
        # lowest terms as polynomials
        num, exp_gens = _exp_generators(num, gens)
        coeffs = _polynomial_coefficients(num, [*gens, *exp_gens])
    if coeffs is None:
        expr = (num / other_den).expand()
        for gen, relation in zip(alg_gens, relations, strict=True):
            # only the powers of G below its degree are linearly independent
            expr = prem(expr, relation, gen).expand()
        # exponentials of jet variables and of the new generators (exp(n atan(p)))
        expr, exp_gens = _exp_generators(expr, gens)
        coeffs = Poly(expr, *gens, *exp_gens).coeffs() if jet else [expr]
        lowest_terms = False
    else:
        lowest_terms = True
    back = {v: k for k, v in to_symbol.items()}
    result = set()
    for c in coeffs if complex_coefficients else _real_and_imaginary_parts(coeffs):
        c = (c if lowest_terms else _numerator(c)).xreplace(back)
        if c != 0:
            if not c.is_Add:
                # a single term: its numeric factor does not matter, e.g.
                # -4*Derivative(Y, x) = 0 is Derivative(Y, x) = 0
                c = c.as_coeff_Mul()[1]
            result.add(c)
    return sorted(result, key=default_sort_key)


def _polynomial_coefficients(e: Expr, gens: Sequence[Basic]) -> list[Expr] | None:
    """The coefficients of the polynomial e in gens, each with integer
    coefficients (as _numerator), from one sparse polynomial in all its
    symbols, functions and derivatives; None if e is no polynomial in
    them (1/x).

    >>> x, a, p = Symbol('x'), Symbol('a'), Symbol('p')
    >>> f = Function('f')(x)
    >>> sorted(_polynomial_coefficients(p**2 * x / 2 + p * (a * f.diff(x) + 1) - x, [p]), key=str)
    [-x, a*Derivative(f(x), x) + 1, x]
    >>> _polynomial_coefficients(p / x, [p]) is None
    True
    """
    atoms = {a: Dummy() for a in e.atoms(Derivative, AppliedUndef)}
    try:
        ring_, element = sring(e.xreplace(atoms), domain=QQ)
    except (PolynomialError, CoercionFailed, NotImplementedError, ValueError):
        return None
    if any(g.is_Pow and g.exp.is_negative for g in ring_.symbols):
        return None
    positions = [ring_.symbols.index(g) for g in gens if g in ring_.symbols]
    terms: dict[tuple[int, ...], dict[tuple[int, ...], Any]] = {}
    for monomial, coefficient in element.terms():
        key = tuple(monomial[k] for k in positions)
        rest = tuple(0 if k in positions else m for k, m in enumerate(monomial))
        terms.setdefault(key, {})[rest] = coefficient
    back = {d: a for a, d in atoms.items()}
    return [
        ring_.from_dict(part).clear_denoms()[1].as_expr().xreplace(back) for part in terms.values()
    ]


def _numerator(c: Expr) -> Expr:
    """The numerator of c in lowest terms, expanded: numer(cancel(c)).expand().

    Computed in SymPy's sparse field of rational functions, with derivatives
    and functions as symbols: cancel() took 15 s for a coefficient of 2000
    terms of the apoptosis model (ODEBench 53), the field 0.7 s.

    >>> x, a = Symbol('x'), Symbol('a')
    >>> f = Function('f')(x)
    >>> _numerator(x / (x + a) + a * f.diff(x) / x)
    a**2*Derivative(f(x), x) + a*x*Derivative(f(x), x) + x**2
    """
    atoms = {a: Dummy() for a in c.atoms(Derivative, AppliedUndef)}
    plain = c.xreplace(atoms)
    try:
        _, element = sfield(plain)
        result = element.numer.as_expr()
    except (PolynomialError, CoercionFailed, NotImplementedError):
        result = numer(cancel(plain)).expand()
    return result.xreplace({d: a for a, d in atoms.items()})


def _power_generators(expr: Expr, jet: Sequence[Basic]) -> tuple[Expr, list[Dummy]]:
    """Replace the powers b**e of jet-dependent b with a non-numeric
    exponent by new generators: b**(k*s + n) becomes G**k * b**n, one G per
    family (b, s), k an integer of either sign, n a number. For a generic
    exponent G = b**s is transcendental over the rational functions of the
    jet variables, so its powers split like independent variables.

    The powers of one base whose symbolic parts are rational multiples of
    each other form one family: b**n and b**(-n) after solving for a
    derivative are G and 1/G (#39), b**(n/2) and b**n are G and G**2.

    >>> p, n = Symbol('p'), Symbol('n')
    >>> e, (g,) = _power_generators(p**n * p + p ** (-n) + p ** (n / 2), [p])
    >>> e == g**2 * p + g**-2 + g
    True
    """
    parts = [
        (p, cancel(p.base), p.exp.expand().as_coeff_Add()[1])
        for p in expr.atoms(Pow)
        if p.base.has(*jet) and not p.exp.is_number
    ]
    repl = {}
    gens = []
    for base, unit, members in commensurable_families(parts):
        flip = -1 if unit.could_extract_minus_sign() else 1  # G = b**(n/2), not b**(-n/2)
        gen = Dummy()
        gens.append(gen)
        for p, k in members:
            repl[p] = gen ** (flip * k) * base ** p.exp.expand().as_coeff_Add()[0]
    return expr.xreplace(repl), gens


def _algebraic_generators(expr: Expr, jet: Sequence[Basic]) -> tuple[Expr, list[Dummy], list[Expr]]:
    """Replace the powers b**(m/n) of jet-dependent b with a non-integer
    rational exponent by powers of a new generator G = b**(1/q), q the lcm
    of the denominators of the exponents of b, and return the relations
    G**q - b = 0 (cleared of denominators). Modulo its relation,
    1, G, ..., G**(q - 1) are linearly independent over the rational
    functions of the jet variables (#5: w_tt = k w_xx**(-1/3), Kamke 7.13
    u'' u''' = a sqrt(1 + b**2 u''**2)).

    >>> p = Symbol('p')
    >>> e, (g,), (r,) = _algebraic_generators(p ** Rational(-1, 3) + p ** Rational(2, 3), [p])
    >>> e == g**-1 + g**2, r == g**3 - p
    (True, True)
    """
    pows = sorted(
        (
            p
            for p in expr.atoms(Pow)
            if p.base.has(*jet) and p.exp.is_Rational and not p.exp.is_Integer
        ),
        key=default_sort_key,
    )
    # one generator per base in lowest terms: solving for the highest
    # derivative brings the same base as one fraction, (u u2 - 2 u1**2)/u**6
    # beside u2/u**5 - 2 u1**2/u**6, and independent generators for both
    # would split the condition wrongly
    bases: dict[Expr, list[Expr]] = {}
    for p in pows:
        bases.setdefault(cancel(p.base), []).append(p)
    repl = {}
    gens, relations = [], []
    for base, members in bases.items():
        q = reduce(ilcm, (p.exp.q for p in members), 1)
        gen = Dummy()
        gens.append(gen)
        relations.append(numer(together(gen**q - base)))
        for p in members:
            repl[p] = gen ** (p.exp * q)
    return expr.xreplace(repl), gens, relations


def _function_generators(expr: Expr, jet: Sequence[Basic]) -> tuple[Expr, list[Dummy]]:
    """Replace the functions of jet variables (log, atan, ..., arbitrary
    functions F(p) and their derivatives, which are Subs) by new generators.
    A transcendental function of p is algebraically independent of p; an
    arbitrary F(p) and its derivatives are taken as independent, which is
    the generic case of a group classification (#5: CRC Vol. 1, 10.3
    v_t = k(v_x) v_xx). Exponentials are left to _exp_generators.

    >>> p = Symbol('p')
    >>> F = Function('F')
    >>> e, gens = _function_generators(p * log(p) + F(p) + 1, [p])
    >>> len(gens), e.has(log, F)
    (2, False)

    The derivative of F is a Derivative of an expression in p; F(p) inside
    it and on its own become two generators:

    >>> e, gens = _function_generators(F(p) + Derivative(F(p), p), [p])
    >>> len(gens), e.has(F)
    (2, False)
    """
    gens: list[Dummy] = []
    while True:
        candidates = [
            a
            for a in expr.atoms(Function, Subs, Derivative)
            if a.has(*jet) and not isinstance(a, exp)
        ]
        # the outermost first: log(F(p)) is one generator; an F(p) inside
        # F'(p) that also occurs on its own is replaced in the next round
        outer = [a for a in candidates if not any(a != b and b.has(a) for b in candidates)]
        if not outer:
            return expr, gens
        # one generator per function of arguments in lowest terms, as for
        # the bases in _algebraic_generators: log((u u2 - 2 u1**2)/u**6) is
        # log(u2/u**5 - 2 u1**2/u**6)
        by_key: dict[Expr, Dummy] = {}
        repl = {}
        for a in sorted(outer, key=default_sort_key):
            key = a.func(*map(cancel, a.args)) if isinstance(a, Function) else a
            repl[a] = by_key.setdefault(key, Dummy())
        gens.extend(by_key.values())
        expr = expr.xreplace(repl)


def _real_and_imaginary_parts(coeffs: Iterable[Expr]) -> list[Expr]:
    """Each coefficient with I (from trigonometric functions written as
    exponentials) split into its real and imaginary part: the infinitesimals
    and the parameters are real. Not for equations with complex
    coefficients (split_jet_coefficients).

    >>> from sympy import I, symbols
    >>> a, x = symbols("a x")
    >>> _real_and_imaginary_parts([3 + 2 * I * a, x])
    [3, 2*a, x]
    """
    result = []
    for c in coeffs:
        # expand only where needed: the coefficients can be large
        if c.has(I):
            c = expand(c)
            imaginary = c.coeff(I)
            result.extend([expand(c - I * imaginary), imaginary])
        else:
            result.append(c)
    return result


def _exp_generators(expr: Expr, jet: Sequence[Basic]) -> tuple[Expr, list[Dummy]]:
    """Replace the exponentials depending on the jet variables by powers of
    new generators, one per family exp(k*a), k a positive integer.

    >>> from sympy import Symbol, exp, symbols
    >>> a = symbols("a")
    >>> e, (g,) = _exp_generators(exp(a) + exp(2 * a), [a])
    >>> e.subs(g, Symbol("E"))
    E**2 + E
    """
    parts = [(e, S.One, e.args[0]) for e in expr.atoms(exp) if e.has(*jet)]
    gens = []
    repl = {}
    for _, unit, members in commensurable_families(parts):
        gen = Dummy()
        gens.append(gen)
        for e, k in members:
            if not k > 0:
                raise NotImplementedError(f"{e} is exp({k}*({unit}))")
            repl[e] = gen**k
    return expr.xreplace(repl), gens


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
    2 u u_x**2 + u**2 u_xx. So are derivatives of expressions without an
    unknown function, as Derivative(0, x) after a parameter is set to 0.

    >>> from sympy import sin
    >>> x, t = Symbol('x'), Symbol('t')
    >>> u = Function('u')(x, t)
    >>> _canonical_derivatives_of(Derivative(u, x, t) - sin(u), [u])
    -sin(u(x, t)) + Derivative(u(x, t), t, x)
    >>> _canonical_derivatives_of(Derivative(u**2 * Derivative(u, x), x), [u])
    u(x, t)**2*Derivative(u(x, t), (x, 2)) + 2*u(x, t)*Derivative(u(x, t), x)**2
    """
    dep = convert_to_iterable(dep)
    derivatives = [
        d for d in expr.atoms(Derivative) if d.expr.has(*dep) or not d.expr.atoms(AppliedUndef)
    ]
    return expr.xreplace({d: d.doit(simplify=False) for d in derivatives})


def _exact_numbers(expr: Expr) -> Expr:
    """expr with every float replaced by the simplest rational number within
    its precision (0.5 -> 1/2, 1.66666666666667 -> 5/3), as the coefficient
    field does (coefficients._prepare). With a float in the equation,
    solve() turns all its numbers into floats (4 -> 4.0), and the
    determining equations carried sqrt(4*x**2*y + 1) and
    sqrt(4.0*x**2*y + 1.0) as two different quantities (#37). Taking the
    full decimal instead gave exponents like 166666666666667/100000000000000
    (Kamke 1.624), on which GMP aborts.

    >>> x = Symbol('x')
    >>> _exact_numbers(0.5 * x + 1.25 + x**1.66666666666667)
    x**(5/3) + x/2 + 5/4
    """
    floats = expr.atoms(Float)
    return expr.xreplace({f: nsimplify(f, rational=True) for f in floats}) if floats else expr


def _local_signs(expr: Expr) -> Expr:
    """expr with every Abs(e) replaced by s*e and every sign(e) by s, s a new
    constant for the sign of e (one per e). Lie point symmetries are local:
    where e does not vanish its sign is constant. SymPy differentiates Abs of
    a complex symbol into re, im and sign, which the determining equations
    and the Janet basis cannot use.

    >>> t = Symbol('t')
    >>> v = Function('v')(t)
    >>> e = _local_signs(v.diff(t) + v * Abs(v))
    >>> sorted(e.free_symbols - {t}, key=str)
    [_sign]
    >>> e.subs(next(iter(e.free_symbols - {t})), 1)
    v(t)**2 + Derivative(v(t), t)
    """
    signs: dict[Expr, Dummy] = {}

    def sign_of(e: Expr) -> Dummy:
        return signs.setdefault(e, Dummy("sign"))

    expr = expr.replace(
        lambda a: isinstance(a, Abs) and not a.args[0].is_number,
        lambda a: sign_of(a.args[0]) * a.args[0],
    )
    return expr.replace(
        lambda a: isinstance(a, sign) and not a.args[0].is_number, lambda a: sign_of(a.args[0])
    )


def convert_to_iterable(item: Variables) -> list[Any]:
    """item as a list: a single variable becomes [item].

    >>> from sympy import symbols
    >>> x, t = symbols("x t")
    >>> convert_to_iterable(x), convert_to_iterable((x, t))
    ([x], [x, t])
    """
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


def _polynomial_in(eq: Expr, d: Basic) -> Poly | None:
    """The numerator of eq as a polynomial in d (a derivative), None if it
    is none.

    >>> from sympy import Function, sqrt, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> _polynomial_in(x * y.diff(x) ** 2 + y, y.diff(x)).all_coeffs()
    [x, 0, y(x)]
    >>> _polynomial_in(sqrt(y.diff(x)) + y, y.diff(x)) is None
    True
    """
    h = Dummy()
    try:
        return Poly(numer(together(eq.xreplace({d: h}))), h)
    except PolynomialError:
        return None


def _initial(eq: Expr, dep: list[Basic], indep: list[Basic]) -> Expr | None:
    """The initial of eq: the coefficient of its leading derivative (see
    _leading_derivative) in its numerator; None without a derivative or if
    eq is no polynomial in it.

    >>> from sympy import Function, symbols
    >>> x, a = symbols("x a")
    >>> y = Function("y")(x)
    >>> _initial(a * x * y.diff(x, 2) + y, [y], [x]), _initial(y, [y], [x])
    (a*x, None)
    """
    _, highest = order(eq, dep, indep)
    if not highest:
        return None
    p = _polynomial_in(eq, _leading_derivative(eq, highest, dep))
    return None if p is None else p.LC()


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
    dep_names = {d.name for d in dep}

    def rank(d: Expr) -> int:
        p = _polynomial_in(eq, d)
        if p is None or p.degree() != 1:
            return 2
        jet_free = not any(a.func.__name__ in dep_names for a in p.LC().atoms(AppliedUndef))
        return 0 if jet_free else 1

    return min(candidates, key=lambda d: (rank(d), default_sort_key(d)))


def _algebraic_in_highest_derivative(
    eq_h: Expr, r: Expr, highest_term: Expr, h: Dummy
) -> Expr | None:
    """The symmetry condition r (the prolonged equation) on eq = 0, for an
    equation with one square root S = sqrt(b) depending on its highest
    derivative h, e.g. Kamke 1.558, a x sqrt(y'**2 + 1) + x y' - y = 0 (#5).

    With eq = A + B*S and r = C + D*S modulo S**2 = b, eq = 0 gives
    S = -A/B, and C*B - D*A has to vanish where A**2 - B**2*b = 0, the
    equation with the root removed: its pseudo-remainder modulo that
    polynomial in h. As for equations polynomial in h (prem below), this is
    the condition for the whole equation, i.e. both signs of the root, not
    one branch. None if eq is not of this form.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> from sympy import Dummy, sqrt
    >>> a, h = symbols("a"), Dummy("h")
    >>> eq = a * x * sqrt(y.diff(x) ** 2 + 1) + x * y.diff(x) - y  # Kamke 1.558
    >>> r = prolongation(eq, create_infinitesimals([y], [x]), [y], [x])
    >>> condition = _algebraic_in_highest_derivative(eq.xreplace({y.diff(x): h}), r, y.diff(x), h)
    >>> condition.has(sqrt(y.diff(x) ** 2 + 1))
    False
    >>> _algebraic_in_highest_derivative(h**2 + 1, r, y.diff(x), h) is None
    True
    """
    roots = {
        p.base
        for p in eq_h.atoms(Pow)
        if p.base.has(h) and p.exp.is_Rational and not p.exp.is_Integer
    }
    if len(roots) != 1:
        return None
    (base,) = roots
    s = Dummy()

    def with_s(e: Expr) -> Expr | None:
        """e with the powers of sqrt(base) as powers of s, None for other roots."""
        pows = [
            p for p in e.atoms(Pow) if p.base == base and p.exp.is_Rational and not p.exp.is_Integer
        ]
        if any(p.exp.q != 2 for p in pows):
            return None
        return numer(together(e.xreplace({p: s ** (2 * p.exp) for p in pows})))

    eq_s = with_s(eq_h)
    r_s = with_s(r.xreplace({highest_term: h}))
    if eq_s is None or r_s is None or r_s.has(*(p for p in r_s.atoms(Pow) if p.base == base)):
        return None
    relation = numer(together(s**2 - base))
    try:
        eq_s = prem(eq_s, relation, s)
        r_s = prem(r_s, relation, s)
        A, B = (Poly(eq_s, s).coeff_monomial(s**k) for k in (0, 1))
        C, D = (Poly(r_s, s).coeff_monomial(s**k) for k in (0, 1))
        P = numer(together(A**2 - B**2 * base))
        return prem((C * B - D * A).expand(), P, h).xreplace({h: highest_term})
    except PolynomialError:
        return None


def _on_lower_derivative(eq: Expr, r: Expr, dep: list[Expr], highest_term: Expr) -> Expr | None:
    """r on eq = 0 when eq cannot be solved for its highest derivative but is
    linear in a lower one, e.g. u_t + F(u_xx) = 0 for u_t (#84): that
    derivative and its derivatives in r are replaced by the solution and its
    total derivatives. None if there is no such derivative.

    >>> from sympy import Function, symbols
    >>> x, t = symbols("x t")
    >>> u = Function("u")(x, t)
    >>> F = Function("F")
    >>> eq = u.diff(t) + F(u.diff(x, 2))  # u_t = -F(u_xx), #84
    >>> _on_lower_derivative(
    ...     eq, u.diff(t, x) + u.diff(t), [u], u.diff(x, 2)
    ... )  # doctest: +NORMALIZE_WHITESPACE
    -F(Derivative(u(x, t), (x, 2))) - Derivative(F(Derivative(u(x, t), (x, 2))),
    Derivative(u(x, t), (x, 2)))*Derivative(u(x, t), (x, 3))
    """
    candidates = sorted(
        (d for d in eq.atoms(Derivative) if d != highest_term and d.expr in dep),
        key=lambda d: (-len(d.variables), default_sort_key(d)),
    )
    for d in candidates:
        h = Dummy()
        eq_h = numer(together(eq.xreplace({d: h})))
        try:
            if Poly(eq_h, h).degree() != 1:
                continue
        except PolynomialError:
            continue
        sol = solve(eq_h, h)[0]
        if sol.has(d):
            continue
        result = r
        while derived := [e for e in result.atoms(Derivative) if _derivative_of(e, d)]:
            for e in derived:
                rest = list(e.variables)
                for v in d.variables:
                    rest.remove(v)
                result = result.xreplace({e: sol.diff(*rest) if rest else sol})
        return result
    return None


def _derivative_of(e: Derivative, d: Derivative) -> bool:
    """e is d or one of its derivatives.

    >>> from sympy import Function, symbols
    >>> x, t = symbols("x t")
    >>> u = Function("u")(x, t)
    >>> _derivative_of(u.diff(x, 2, t), u.diff(x)), _derivative_of(u.diff(t), u.diff(x))
    (True, False)
    """
    if e.expr != d.expr:
        return False
    rest = list(e.variables)
    for v in d.variables:
        if v not in rest:
            return False
        rest.remove(v)
    return True


def determining_condition(
    eq: Expr,
    dep: Variables,
    indep: Variables,
    infinitesimals: InfinitesimalNames = None,
) -> Expr:
    """The symmetry condition of eq (its prolongation on eq = 0) as an
    expression in the jet variables; split_jet_coefficients splits it into
    the determining equations (compute_overdetermined_system_of_infinitesimals).

    infinitesimals : dict{Function/Symbol : new name}

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> determining_condition(y.diff(x), y, x)  # y' = 0
    Derivative(Y(y(x), x), x)
    """
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    eq = _local_signs(_exact_numbers(_canonical_derivatives_of(eq, dep)))

    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    _, highest_terms = order(eq, dep, indep)
    highest_term = _leading_derivative(eq, highest_terms, dep)

    r = prolongation(eq, infinitesimals, dep, indep)
    h = Dummy()
    eq_h = numer(together(eq.xreplace({highest_term: h})))
    try:
        degree = Poly(eq_h, h).degree()
    except PolynomialError:
        algebraic = _algebraic_in_highest_derivative(eq_h, r, highest_term, h)
        if algebraic is not None:
            return algebraic
        # not polynomial in the highest derivative, e.g. u_t = atan(u_xx):
        # solve for it if the solution is unique (u_xx = tan(u_t)) (#5)
        try:
            sols: list[Expr] = list(solve(eq, highest_term))
        except NotImplementedError:
            sols = []
        if len(sols) == 1:
            return r.xreplace({highest_term: sols[0]})
        lower = _on_lower_derivative(eq, r, dep, highest_term)
        if lower is not None:
            return lower
        raise NotImplementedError(
            f"{eq} is not polynomial in its highest derivative {highest_term} "
            f"and cannot be solved uniquely for it (#5)"
        ) from None
    if degree == 1:
        sol = solve(eq, highest_term)[0]
        r = r.xreplace({highest_term: sol})
    else:
        # eq is not linear in its highest derivative: solving for it would
        # bring in roots of jet variables. pr X(eq) has to vanish on eq = 0,
        # i.e. (eq being irreducible) eq has to divide it as a polynomial in
        # the highest derivative, so its pseudo-remainder has to vanish
        r_h = numer(together(r.xreplace({highest_term: h})))
        r = prem(r_h, eq_h, h).xreplace({h: highest_term})
    return r


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
    in_ring = _ring_determining_equations(eq, dep, indep, infinitesimals)
    if in_ring is not None:
        return in_ring
    condition = determining_condition(eq, dep, indep, infinitesimals)
    return split_jet_coefficients(condition, convert_to_iterable(dep))


@profile_if_enabled
def _ring_determining_equations(
    eq: Expr,
    dep: Variables,
    indep: Variables,
    infinitesimals: InfinitesimalNames = None,
) -> list[Expr] | None:
    """The determining equations of eq as determining_condition and
    split_jet_coefficients give them, computed in one polynomial ring of
    the jet coordinates, the partial derivatives of the infinitesimals and
    the parameters: the numerator N of eq, pr X(N) reduced by N
    (pseudo-remainder in the highest derivative), its coefficients by the
    jet variables. None if eq or the infinitesimals are no polynomials in
    these (1/x, sin(y), arbitrary functions f(x)).

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> for e in _ring_determining_equations(y.diff(x, 2), y, x):
    ...     print(e)
    -Derivative(X(y(x), x), (x, 2)) + 2*Derivative(Y(y(x), x), x, y(x))
    Derivative(Y(y(x), x), (y(x), 2)) - 2*Derivative(X(y(x), x), x, y(x))
    Derivative(X(y(x), x), (y(x), 2))
    Derivative(Y(y(x), x), (x, 2))
    >>> _ring_determining_equations(y.diff(x, 2) + y.diff(x) / x, y, x) is not None
    True
    >>> _ring_determining_equations(y.diff(x, 2) - exp(y), y, x) is None
    True
    """
    dep = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    eq = _local_signs(_exact_numbers(_canonical_derivatives_of(eq, dep)))
    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    max_order, highest_terms = order(eq, dep, indep)
    highest_term = _leading_derivative(eq, highest_terms, dep)
    space = _JetSpace(dep, indep)
    symbolic = space.symbolic([infinitesimals[v] for v in (*indep, *dep)])
    h = space.coordinates(highest_term)
    # pr X(N/D) = pr X(N)/D where N = 0
    numerator = numer(together(space.coordinates(eq)))
    if any(e.has(Derivative, Subs, AppliedUndef) for e in (*symbolic, numerator)):
        return None
    *symbolic, N = space.in_ring([*symbolic, numerator], max_order)
    if space.ring is None:
        return None
    gens = space.gens
    coordinates = [gens[v] for v in (*indep, *space.base.values())]
    condition = space.ring.zero
    for c, eta in zip(coordinates, symbolic, strict=True):
        condition += eta * N.diff(c)
    for (a, multi), eta in space.prolonged(symbolic, max_order).items():
        condition += eta * N.diff(space.jet(a, multi))
    H = gens[h]
    lc = N.coeff_wrt(H, N.degree(H))
    if N.degree(H) == 1 and lc.is_ground:
        # N solved for the highest derivative
        condition = condition.compose(H, H - N.quo_ground(lc.LC))
    else:
        # on N = 0: N divides pr X(N) as a polynomial in the highest derivative
        condition = condition.prem(N, H)
    return _jet_coefficients(space, condition)


def _jet_coefficients(space: "_JetSpace", condition: Any) -> list[Expr]:
    """The coefficients of the ring element condition by the jet
    variables, each with coprime integer coefficients, as expressions in
    the functions and derivatives (_ring_determining_equations).

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> space = _JetSpace([y], [x])
    >>> (X,) = space.in_ring(space.symbolic([Function('X')(x, y)]), 1)
    >>> _jet_coefficients(space, space.total(X, 0) * 2 + 4 * X)
    [2*X(x, y(x)) + Derivative(X(x, y(x)), x), Derivative(X(x, y(x)), y(x))]
    """
    dep = space.dep
    generators = list(space.gens)
    jets = set(space.jets.values())
    positions = [k for k, g in enumerate(generators) if g in jets]
    parts: dict[tuple[int, ...], dict[tuple[int, ...], Any]] = {}
    for monomial, coefficient in condition.terms():
        key = tuple(monomial[k] for k in positions)
        rest = tuple(0 if k in positions else m for k, m in enumerate(monomial))
        parts.setdefault(key, {})[rest] = coefficient
    # the partials in SymPy's canonical order, as split_jet_coefficients
    plain = {d: Symbol(d.name) for d in dep}
    functions = {v: k for k, v in plain.items()}
    back = {
        s: v.xreplace(plain).doit(simplify=False).xreplace(functions)
        for s, v in space.back().items()
    }
    result = set()
    for part in parts.values():
        c = space.ring.from_dict(part).clear_denoms()[1].primitive()[1].as_expr().xreplace(back)
        if not c.is_Add:
            c = c.as_coeff_Mul()[1]
        result.add(c)
    return sorted(result, key=default_sort_key)


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
    return _determining_equations(ode, dependent, independent, infinitesimals)


def _determining_equations(
    eq: Expr, dependent: Variables, independent: Variables, infinitesimals: InfinitesimalNames
) -> list[Expr]:
    """The determining equations of the scalar equation eq, for
    overdetermined_system_ode and overdetermined_system_pde.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> len(_determining_equations(y.diff(x, 2), y, x, None))
    4
    """
    _checked_arguments(eq, dependent, independent)
    result = compute_overdetermined_system_of_infinitesimals(
        eq, dependent, independent, infinitesimals=infinitesimals
    )
    return [finish_substitution(e) for e in result]


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
    _checked_arguments(eqs, dependent, independent)
    eqs = [_local_signs(_exact_numbers(_canonical_derivatives_of(eq, dependent))) for eq in eqs]
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
            if not any((c - known).expand() == 0 for known in result):
                result.append(c)
    return result


def _ode_system_reduction(
    eqs: Sequence[Expr], dep: list[Expr], t: Symbol
) -> Callable[[Expr], Expr]:
    """Solve a system of ODEs for one leading derivative per equation and
    return the function that replaces every leading derivative, and every
    derivative of it, by its value on the solutions of the system.

    >>> from sympy import Function, symbols
    >>> t = symbols("t")
    >>> x1, x2 = Function("x1")(t), Function("x2")(t)
    >>> oscillator = [x1.diff(t) - x2, x2.diff(t) + x1]
    >>> reduce = _ode_system_reduction(oscillator, [x1, x2], t)
    >>> reduce(x1.diff(t, 2))
    -x1(t)
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

    >>> from sympy import Function, symbols
    >>> t = symbols("t")
    >>> x1, x2 = Function("x1")(t), Function("x2")(t)
    >>> oscillator = [x1.diff(t) - x2, x2.diff(t) + x1]
    >>> _solved_form(oscillator, [x1, x2], t)
    {x1(t): (1, x2(t)), x2(t): (1, -x1(t))}
    """
    candidates = [sorted(order(eq, dep, [t])[1], key=default_sort_key) for eq in eqs]
    for leaders in product(*candidates):
        if len({leader.expr for leader in leaders}) == len(leaders):
            break
    else:
        raise NotImplementedError("no distinct leading derivatives for the equations")
    rhs = {}
    for eq, leader in zip(eqs, leaders, strict=True):
        p = _polynomial_in(eq, leader)
        if p is None or p.degree() != 1:
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
    after differentiation.

    >>> from sympy import Function, symbols
    >>> t = symbols("t")
    >>> x1, x2 = Function("x1")(t), Function("x2")(t)
    >>> oscillator = [x1.diff(t) - x2, x2.diff(t) + x1]
    >>> from sympy import Derivative
    >>> def reducible(e):
    ...     return list(e.atoms(Derivative))
    >>> _check_termination({x1: (1, x2), x2: (1, -x1)}, reducible)
    >>> _check_termination({x1: (1, x2.diff(t)), x2: (1, x1.diff(t))}, reducible)
    Traceback (most recent call last):
    ...
    NotImplementedError: the reduction of the system by its equations may not terminate
    """

    def is_orderly_ranking(variables: Sequence[Expr]) -> bool:
        rank = {f: i for i, f in enumerate(variables)}
        return all(
            (d.derivative_count, rank[d.expr]) < (n, rank[f])
            for f, (n, value) in rhs.items()
            for d in reducible(value)
        )

    if not any(is_orderly_ranking(ranking) for ranking in permutations(rhs)):
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
    T_u
    T_uu
    T_ux + X_u
    T_x
    U_t - U_xx
    X_uu
    """
    if len(convert_to_iterable(dependent)) != 1:
        raise NotImplementedError("only one dependent variable is supported")
    return _determining_equations(pde, dependent, independent, infinitesimals)


def _linear_system_ode(
    ode: Expr, dependent: Expr, independent: Symbol, infinitesimals: InfinitesimalNames = None
) -> tuple[list[Expr], list[Expr], list[Symbol], Symbol]:
    """The determining equations of an ODE as a linear system for JanetBasis.

    Returns (system, dependents, independents, h_symbol): the dependent
    variable y(x) is replaced by the symbol H, so the infinitesimals become
    functions of (H, x). (After splitting, the determining equations no
    longer contain derivatives of y.)

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> system, functions, variables, H = _linear_system_ode(y.diff(x, 2), y, x)
    >>> functions, variables, H
    ([X(H, x), Y(H, x)], [x, H], H)
    """
    infinitesimals = create_infinitesimals([dependent], [independent], infinitesimals)
    overdetermined_system = overdetermined_system_ode(
        ode, [dependent], [independent], infinitesimals=infinitesimals
    )
    h_symbol = Symbol("H")
    inf = [infinitesimals[v] for v in [dependent, independent]]

    r1 = [h_symbol, independent]
    inf = [f.xreplace({dependent: h_symbol}) for f in inf]
    system = [e.replace(dependent, h_symbol) for e in overdetermined_system]
    return system, list(reversed(inf)), list(reversed(r1)), h_symbol


def determining_janet_basis(
    equations: Expr | Iterable[Expr],
    dependent: Variables,
    independent: Variables,
    sort_order: WeightFunction = Mgrevlex,
) -> JanetBasis:
    """The Janet basis of the determining equations of the Lie point
    symmetries of a scalar ODE, a system of ODEs or a scalar PDE. Its
    unknown functions are the infinitesimals in the order of the
    coordinates: the independent variables, then the dependent ones, written
    as plain symbols (y for y(x)). rank() is the dimension of the symmetry
    algebra (oo if infinite), LieAlgebra.from_janet_basis its structure.

    The Blasius equation has the translation d/dx and the scaling
    x d/dx - y d/dy; y' = y has infinitely many symmetries:

    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> blasius = 2 * diff(y, x, 3) + y * diff(y, x, 2)
    >>> determining_janet_basis(blasius, y, x).rank()
    2
    >>> determining_janet_basis(diff(y, x) - y, y, x).rank()
    oo
    """
    system, functions, variables = _determining_system(equations, dependent, independent)
    return JanetBasis(system, functions, variables, sort_order=sort_order)


def _checked_arguments(
    equations: Expr | Iterable[Expr], dependent: Variables, independent: Variables
) -> tuple[list[Expr], list[Expr], list[Basic]]:
    """equations, dependent and independent variables as lists, checked: the
    independent variables are distinct symbols, the dependent variables
    functions of them (y(x), not y), every equation (Eq(a, b) is a - b)
    contains a derivative of a dependent variable, only with respect to the
    independent ones. ValueError otherwise.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> from sympy import Eq
    >>> _checked_arguments(Eq(y.diff(x), y), y, x)
    ([-y(x) + Derivative(y(x), x)], [y(x)], [x])
    """
    eqs = [equations] if isinstance(equations, (Basic, int, float)) else list(equations)
    eqs = [e.lhs - e.rhs if isinstance(e, Equality) else sympify(e) for e in eqs]
    dep = convert_to_iterable(dependent)
    indep = convert_to_iterable(independent)
    _check_independent(indep)
    _check_dependent(dep, indep)
    for e in eqs:
        _check_equation(e, dep, indep)
    return eqs, dep, indep


def _check_independent(indep: list[Any]) -> None:
    """ValueError unless the independent variables are distinct symbols.

    >>> from sympy import symbols
    >>> x = symbols("x")
    >>> _check_independent([x, x])
    Traceback (most recent call last):
    ...
    ValueError: the independent variables [x, x] are not distinct
    """
    if not indep:
        raise ValueError("no independent variables")
    for v in indep:
        if not isinstance(v, Symbol):
            raise ValueError(f"the independent variable {v} is not a symbol")
    if len(set(indep)) != len(indep):
        raise ValueError(f"the independent variables {indep} are not distinct")


def _check_dependent(dep: list[Any], indep: list[Any]) -> None:
    """ValueError unless the dependent variables are functions of the
    independent ones.

    >>> from sympy import symbols
    >>> x, y = symbols("x y")
    >>> _check_dependent([y], [x])  # doctest: +ELLIPSIS
    Traceback (most recent call last):
    ...
    ValueError: the dependent variable y is not a function of ...: write y(x)
    """
    if not dep:
        raise ValueError("no dependent variables")
    for d in dep:
        if not isinstance(d, AppliedUndef):
            raise ValueError(
                f"the dependent variable {d} is not a function of the independent variables "
                f"{indep}: write {d}({', '.join(map(str, indep))})"
            )
        others = [a for a in d.args if a not in indep]
        if others:
            raise ValueError(
                f"the dependent variable {d} depends on {others}, which are not among the "
                f"independent variables {indep}"
            )


def _check_equation(e: Expr, dep: list[Any], indep: list[Any]) -> None:
    """ValueError unless e contains a derivative of a dependent variable by
    independent ones.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> _check_equation(y.diff(x), [y], [x])
    >>> _check_equation(y + 1, [y], [x])
    Traceback (most recent call last):
    ...
    ValueError: y(x) + 1 contains no derivative of the dependent variables [y(x)]
    """
    if e == 0:
        raise ValueError("an equation is 0")
    derivatives = [a for a in e.atoms(Derivative) if a.expr in dep]
    if not derivatives:
        raise ValueError(f"{e} contains no derivative of the dependent variables {dep}")
    for a in derivatives:
        others = sorted({v for v in a.variables if v not in indep}, key=str)
        if others:
            raise ValueError(
                f"{a}: derivative with respect to {others}, which are not among the "
                f"independent variables {indep}"
            )


def _determining_system(
    equations: Expr | Iterable[Expr], dependent: Variables, independent: Variables
) -> tuple[list[Expr], list[Expr], list[Basic]]:
    """(determining equations, infinitesimals, coordinates) of a scalar ODE,
    a system of ODEs or a scalar PDE, the dependent variables written as
    plain symbols, the infinitesimals in the order of the coordinates.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> system, functions, coordinates = _determining_system(y.diff(x, 2), y, x)
    >>> len(system), functions, coordinates
    (4, [X(y, x), Y(y, x)], [x, y])
    """
    eqs, dep, indep = _checked_arguments(equations, dependent, independent)
    if len(indep) == 1:
        system, functions, variables, _ = _linear_system_odes(eqs, dep, indep)
        return system, functions, variables
    if len(eqs) == 1 and len(dep) == 1:
        infinitesimals = create_infinitesimals(dep, indep)
        plain = {d: plain_symbol(d) for d in dep}
        pde = overdetermined_system_pde(eqs[0], dep, indep, infinitesimals=infinitesimals)
        functions = [infinitesimals[v].xreplace(plain) for v in indep + dep]
        return [e.xreplace(plain) for e in pde], functions, indep + [plain[d] for d in dep]
    raise NotImplementedError("determining equations of systems of PDEs (#21)")


@dataclass
class VerificationResult:
    """The determining equations with a generator substituted: residues
    (simplified, 0 also where they vanish for positive variables and
    parameters, i.e. locally; a residue that is not 0 may still vanish where
    simplification fails to show it), and the assumptions under which the
    determining equations hold: the initials of the equations (the
    coefficients of their highest derivatives) are nonzero. True if every
    residue is 0."""

    generator: tuple[Expr, ...]
    residues: list[Expr]
    assumptions: list[Expr] = field(default_factory=list)

    def __bool__(self) -> bool:
        """Whether every residue vanishes: the generator is a symmetry.

        >>> from sympy import Function, symbols
        >>> x = symbols("x")
        >>> y = Function("y")(x)
        >>> translation, other = verify_symmetries(y.diff(x, 2), y, x, [(1, 0), (0, x**2)])
        >>> bool(translation), bool(other)
        (True, False)
        """
        return all(r == 0 for r in self.residues)

    def nonzero_residues(self) -> list[Expr]:
        """The residues that do not vanish.

        >>> from sympy import Function, symbols
        >>> x = symbols("x")
        >>> y = Function("y")(x)
        >>> (result,) = verify_symmetries(y.diff(x, 2), y, x, [(0, x**2)])
        >>> result.nonzero_residues()
        [2]
        """
        return [r for r in self.residues if r != 0]


def verify_symmetry(
    equations: Expr | Iterable[Expr],
    dependent: Variables,
    independent: Variables,
    generator: Sequence[Any],
) -> VerificationResult:
    """Whether generator is a Lie point symmetry of a scalar ODE, a system
    of ODEs or a scalar PDE: its components (independent variables first,
    then the dependent ones as plain symbols, y for y(x)) substituted into
    the determining equations.

    The Blasius equation: x d/dx - y d/dy is a symmetry, x d/dx + y d/dy is
    not:

    >>> x, y_ = Symbol('x'), Symbol('y')
    >>> y = Function('y')(x)
    >>> blasius = diff(y, x, 3) + y * diff(y, x, 2)
    >>> bool(verify_symmetry(blasius, y, x, (x, -y_)))
    True
    >>> result = verify_symmetry(blasius, y, x, (x, y_))
    >>> bool(result), result.nonzero_residues()
    (False, [2*y])
    """
    return verify_symmetries(equations, dependent, independent, [generator])[0]


def verify_symmetries(
    equations: Expr | Iterable[Expr],
    dependent: Variables,
    independent: Variables,
    generators: Iterable[Sequence[Any]],
) -> list[VerificationResult]:
    """verify_symmetry for several generators, computing the determining
    equations once.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> [bool(r) for r in verify_symmetries(y.diff(x, 2), y, x, [(1, 0), (0, x**2)])]
    [True, False]
    """
    eqs = [equations] if isinstance(equations, Basic) else list(equations)
    dep = convert_to_iterable(dependent)
    indep = convert_to_iterable(independent)
    system, functions, variables = _determining_system(eqs, dep, indep)
    assumptions = _initials(eqs, dep, indep)
    results = []
    for generator in generators:
        components = tuple(_exact_numbers(sympify(c)) for c in generator)
        if len(components) != len(variables):
            raise ValueError(f"{generator}: one component per coordinate {variables}")
        values = dict(zip(variables, components, strict=True))
        solution = {
            f.func: Lambda(f.args, values[v]) for f, v in zip(functions, variables, strict=True)
        }
        residues = [_simplified_residue(e.subs(solution).doit()) for e in system]
        results.append(VerificationResult(components, residues, assumptions))
    return results


def _initials(eqs: list[Expr], dep: list[Basic], indep: list[Basic]) -> list[Expr]:
    """The coefficients of the highest derivatives of the equations that are
    not constants: the determining equations divide by them.

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> _initials([x * y.diff(x, 2) + y, y.diff(x) - 1], [y], [x])
    [x]
    """
    result = []
    for eq in eqs:
        eq = _exact_numbers(_canonical_derivatives_of(eq, dep))  # as determining_condition
        initial = _initial(eq, dep, indep)
        if initial is not None and not initial.is_number and initial not in result:
            result.append(initial)
    return result


def _simplified_residue(residue: Expr) -> Expr:
    """residue simplified, 0 if it vanishes: simplify(), or else with every
    power b**(s + n), s symbolic and n a number, written as G*b**n, G a new
    symbol for b**s. simplify misses (u + mu)**2*(u + mu)**(nu - 1) -
    (u + mu)**(nu + 1); an identity in the symbols G holds for their values
    too. Last, where the variables and parameters are positive (bases of
    powers taken positive): there the generator is a (local) symmetry.

    >>> from sympy import sqrt, symbols
    >>> x, u, mu, nu = symbols("x u mu nu")
    >>> _simplified_residue((u + mu) ** 2 * (u + mu) ** (nu - 1) - (u + mu) ** (nu + 1))
    0
    >>> _simplified_residue(sqrt(x**2) - x), _simplified_residue(x - 1)
    (0, x - 1)
    """
    residue = simplify(residue)
    if residue == 0:
        return residue
    generators: dict[tuple[Expr, Expr], Dummy] = {}
    powers = {}
    for p in residue.atoms(Pow):
        if not p.exp.is_number:
            n, s = p.exp.as_coeff_Add()
            powers[p] = generators.setdefault((p.base, s), Dummy()) * p.base**n
    if expand(numer(together(residue.xreplace(powers)))) == 0:
        return sympify(0)
    # symmetries are local: where the variables and parameters are positive,
    # Abs(y) = y and ((f*g)**(1/n))**n = f*g (Kamke 1.57, 1.552)
    positive = {z: Dummy(z.name, positive=True) for z in residue.free_symbols}
    local = powdenest(residue.xreplace(positive), force=True)
    if simplify(local) == 0 or simplify(_lambert_w_rewritten(local)) == 0:
        return sympify(0)
    return residue


def _lambert_w_rewritten(expr: Expr) -> Expr:
    """expr with the identities of W = LambertW(z), W exp(W) = z (principal
    branch, z > 0): log(W) = log(z) - W, exp(W) = z/W, logarithms of
    products expanded (positive arguments). Kamke 1.565 (#77).

    >>> from sympy import LambertW, exp, log, symbols
    >>> x = symbols("x")
    >>> (
    ...     _lambert_w_rewritten(log(LambertW(x)) + LambertW(x) - log(x)),
    ...     _lambert_w_rewritten(exp(LambertW(x))),
    ... )
    (0, x/LambertW(x))
    """
    if not expr.has(LambertW):
        return expr
    expr = expand_log(expr, force=True)
    expr = expr.replace(
        lambda e: isinstance(e, log) and isinstance(e.args[0], LambertW),
        lambda e: log(e.args[0].args[0]) - e.args[0],
    )
    expr = expr.replace(
        lambda e: isinstance(e, exp) and isinstance(e.args[0], LambertW),
        lambda e: e.args[0].args[0] / e.args[0],
    )
    return expand_log(expr, force=True)


def janet_basis_from_ode(  # pylint: disable=keyword-arg-before-vararg,unused-argument
    ode: Expr,
    dependent: Expr,
    independent: Symbol,
    sort_order: WeightFunction = Mgrevlex,
    infinitesimals: InfinitesimalNames = None,
    *args: object,
    **kw: object,
) -> LHDPList:
    """The Janet basis of the determining equations of the ODE, in y(x).

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> len(janet_basis_from_ode(y.diff(x, 2), y, x))
    6
    """
    system, inf, r1, h_symbol = _linear_system_ode(ode, dependent, independent, infinitesimals)
    janet = JanetBasis(system, inf, r1, sort_order=sort_order)
    return _back_substituted(janet, {h_symbol: dependent}, sort_order)


def _back_substituted(
    janet: JanetBasis, back: Mapping[Basic, Basic], sort_order: WeightFunction
) -> LHDPList:
    """The elements of a Janet basis as LHDPs, with the symbols standing for
    the dependent variables replaced back by them (back: symbol -> function).

    >>> from sympy import Function, symbols
    >>> x = symbols("x")
    >>> y = Function("y")(x)
    >>> system, functions, variables, H = _linear_system_ode(y.diff(x, 2), y, x)
    >>> basis = _back_substituted(JanetBasis(system, functions, variables), {H: y}, Mgrevlex)
    >>> basis[-1]
    D(Y(y(x), x), (x, 2))
    """

    def back_substitute(e: Expr) -> Expr:
        return e.xreplace(back)

    ctx = Context(
        dependent=[back_substitute(v) for v in janet.context.dependent],
        independent=[back_substitute(v) for v in janet.context.independent],
        weight=sort_order,
    )
    res = []
    for lhdp in janet.S:
        p = []
        for term in lhdp.terms:
            coeff = back_substitute(term.coeff.as_expr())
            d = back_substitute(term.derivative)
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

    >>> from sympy import Function, symbols
    >>> t = symbols("t")
    >>> x1, x2 = Function("x1")(t), Function("x2")(t)
    >>> oscillator = [x1.diff(t) - x2, x2.diff(t) + x1]
    >>> system, functions, variables, to_symbol = _linear_system_odes(oscillator, [x1, x2], t)
    >>> functions, variables
    ([T(x1, x2, t), X1(x1, x2, t), X2(x1, x2, t)], [t, x1, x2])
    """
    dep = convert_to_iterable(dependent)
    indep = convert_to_iterable(independent)
    infinitesimals = create_infinitesimals(dep, indep, infinitesimals)
    system = overdetermined_system_odes(eqs, dep, indep, infinitesimals=infinitesimals)
    to_symbol = {d: plain_symbol(d) for d in dep}
    inf = [infinitesimals[v].xreplace(to_symbol) for v in indep + dep]
    variables = indep + [to_symbol[d] for d in dep]
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
    """default, rearranged like ordering; the entries are matched by key.

    >>> _ranked(["b", "a"], [("a", 1), ("b", 2)], key=lambda z: z[0]), _ranked(None, [1], key=str)
    ([('b', 2), ('a', 1)], [1])
    """
    if ordering is None:
        return default
    by_key = {key(item): item for item in default}
    ranked = [by_key.get(key(item)) for item in ordering]
    if None in ranked or len(set(ranked)) != len(default):
        raise ValueError(f"{list(ordering)} is not an ordering of {default}")
    return cast(list[T], ranked)


if __name__ == "__main__":
    import doctest

    doctest.testmod()
