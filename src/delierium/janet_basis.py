"""
Janet Basis
"""

import functools
from collections import OrderedDict, namedtuple
from collections.abc import Iterable
from itertools import product
from operator import mul

from more_itertools import bucket, flatten
from sympy import Add, Mul, S, Symbol, default_sort_key, numer, oo, together
from sympy.core.function import AppliedUndef
from sympy.functions.elementary.exponential import ExpBase
from sympy.polys.polyerrors import CoercionFailed, PolynomialError
from sympy.polys.rings import sring

from delierium.coefficients import ONE, Coeff, primitive
from delierium.helpers import (
    Derivative,
    eq,
    is_derivative,
    is_function,
    ltf,
    pairs_exclude_diagonal,
    profile_if_enabled,
    show_output,
)
from delierium.matrix_order import Context, Mgrevlex, Mgrlex

__all__ = [
    "LHDP",
    "SCHWARZ_TYPES",
    "JanetBasis",
    "JanetType",
    "LHDPList",
    "autoreduce",
    "complete",
    "complete_system",
    "find_integrable_conditions",
    "integrability_conditions",
    "is_janet_basis_of",
    "janet_type",
    "nonzero_factors",
    "reduce_by_system",
    "split_assumptions",
    "vec_multipliers",
]

# Basic.free_symbols.cache_clear()


@profile_if_enabled
def compute_comparison_vector(dependent, func, ctxcheck):
    iv = [0] * len(dependent)
    if func in dependent:
        iv[dependent.index(func)] = 1
    return iv


@profile_if_enabled
def compute_order(derivative, independent, comp_order):
    """Computes the monomial tuple from the derivative part."""
    if is_derivative(derivative):
        return comp_order(derivative)
    # XXX: Check can that be within a system of linear PDEs ?
    return [0] * len(independent)


class _Dterm:
    __slots__ = ["coeff", "comparison_vector", "context", "derivative", "function", "order"]

    @profile_if_enabled
    def __init__(self, coeff, derivative, context):
        self.coeff = coeff if isinstance(coeff, Coeff) else Coeff(coeff)
        self.derivative = derivative
        self.context = context
        if is_derivative(self.derivative):
            self.function = self.derivative.args[0]
        else:
            self.function = self.derivative

        self.order = self._compute_order()
        self.comparison_vector = self._compute_comparison_vector()

    def copy(self):
        """Shallow copy; coefficients are changed in place elsewhere, so
        a _Dterm must not be shared between differential polynomials."""
        new = object.__new__(_Dterm)
        for slot in self.__slots__:
            setattr(new, slot, getattr(self, slot))
        return new

    @profile_if_enabled
    def expression(self):
        return self.coeff.as_expr() * self.derivative

    @profile_if_enabled
    def _compute_comparison_vector(self):
        """Concatenates order and comparison vector for input for ..."""
        iv = compute_comparison_vector(
            self.context.dependent, self.function, self.context.is_ctxfunc
        )
        return tuple(self.order + iv)

    def __str__(self):
        result = f"{self.derivative}" if self.coeff == 1 else f"({self.coeff}) * {self.derivative}"
        return result.replace("Derivative", "D")

    @profile_if_enabled
    def term(self):
        return self.expression()

    @profile_if_enabled
    def _compute_order(self):
        """computes the monomial tuple from the derivative part"""
        return compute_order(
            self.derivative, self.context.independent, self.context.order_of_derivative
        )

    @profile_if_enabled
    def __sub__(self, other):
        if self.comparison_vector != other.comparison_vector:
            raise ValueError
        return self.__class__(
            coeff=self.coeff - other.coeff, derivative=self.derivative, context=self.context
        )

    @profile_if_enabled
    def __add__(self, other):
        if self.comparison_vector != other.comparison_vector:
            raise ValueError
        return self.__class__(
            coeff=self.coeff + other.coeff, derivative=self.derivative, context=self.context
        )

    @profile_if_enabled
    def is_coefficient(self):
        # XXX nonsense
        return self.derivative == 1

    @profile_if_enabled
    def __lt__(self, other):
        """
        >>> from sympy import *
        >>> from delierium.matrix_order import Mlex
        >>> x, y, z = symbols("x, y, z")
        >>> g = Function("g")(x, y, z)
        >>> h = Function("h")(x, y, z)
        >>> f = Function("f")(x, y, z)
        >>> ctx = Context((f, g, h), (x, y, z), Mlex)
        >>> dterm1 = _Dterm(derivative=Derivative(f, x, y), coeff=x**2, context=ctx)
        >>> dterm2 = _Dterm(derivative=Derivative(f, x, y, z), coeff=1, context=ctx)
        >>> print(dterm1 < dterm2)
        True
        """
        # XXX context.gt still a bad place
        return not self == other and self.context.gt(
            other.comparison_vector, self.comparison_vector
        )

    @profile_if_enabled
    def __eq__(self, other) -> bool:
        return self is other or (
            self.comparison_vector == other.comparison_vector and self.coeff == other.coeff
        )

    def show(self, rich=True) -> None:
        if not rich:
            return str(self)
        return ltf(
            self.expression(), self.context.dependent, self.context.independent, printer=False
        )

    @profile_if_enabled
    def add_coefficient(self, c):
        return _Dterm(coeff=self.coeff + c, derivative=self.derivative, context=self.context)

    @profile_if_enabled
    def diff(self, *variables):
        if len(variables) > 1:
            # the product rule below holds for one variable only; for
            # several, differentiate one after the other (Leibniz rule)
            terms = [self]
            for v in variables:
                terms = [t for term in terms for t in term.diff(v)]
            return terms
        f = self.coeff
        g = self.derivative
        fprime = f.diff(*variables)
        result = []
        if fprime:
            result = [_Dterm(coeff=fprime, derivative=g, context=self.context)]
        gprime = g.diff(*variables)
        d2 = _Dterm(coeff=f, derivative=gprime, context=self.context)
        if d2:
            result.append(d2)
        return result

    @profile_if_enabled
    def __hash__(self):
        return hash(str(self.coeff) + str(self.derivative))

    _cache_key = __hash__


class LHDP:
    """Linear Homogenious Differential Polynomial."""

    @profile_if_enabled
    def __init__(self, e, context, dterms=()):
        self.context = context
        self.p = []
        self.multipliers = []
        self.nonmultipliers = []
        self.hash = 0
        if dterms:
            self.p = [_.copy() for _ in dterms]
        else:
            self._init(e.simplify().expand())
        # coefficients are in canonical form (coefficients.Coeff), so a
        # vanishing one is recognized
        self.p = [_ for _ in self.p if _.coeff.canonical()]

        self.p.sort(reverse=True)
        self.normalize()

    @profile_if_enabled
    def _init(self, e):
        if isinstance(e, (Symbol, Derivative, Mul, AppliedUndef)):
            operands = [e]
        elif isinstance(e, Symbol):
            raise ValueError(f"{e} is no term in a LHDP")
        else:
            assert isinstance(e, Add)
            operands = e.args
        r = [analyze_term(self.context, o) for o in operands]
        dterms = {}
        for _r in r:
            dterms.setdefault(_r[0], []).append((_r[1], _r[2]))
        self.p = []
        for v in dterms.values():
            # v is a list of tuples
            c = 0
            for tup in v:
                c += tup[1]
            self.p.append(_Dterm(derivative=v[0][0], coeff=c, context=self.context))

    def expression(self):
        return sum(_.expression() for _ in self.p)

    def _collect_terms(self, e):
        pass

    def atoms(self, e):
        # needed for ltf
        return self.expression().atoms(e)

    def show_derivatives(self):
        print(list(self.derivatives()))

    def leading_term(self):
        return self.p[0].term()

    def leading_derivative(self):
        return self.p[0].derivative

    def leading_function(self):
        return self.p[0].function

    def leading_coefficient(self):
        return self.p[0].coeff

    def terms(self):
        for p in self.p:
            yield p.term()

    def derivatives(self):
        for p in self.p:
            yield p.derivative

    def coefficients(self):
        for p in self.p:
            yield p.coeff

    def make_monic(self):
        """Divide by the leading coefficient."""
        coeff = self.p[0].coeff
        self.p[0].coeff = ONE
        if coeff != ONE:
            self.context.divisors.append(coeff)
            for _ in self.p[1:]:
                _.coeff = (_.coeff / coeff).canonical()

    @profile_if_enabled
    def normalize(self):
        if self.p:
            #            intermediate = [_Dterm(coeff=Rational(1, 1),
            #                                   derivative=self.p[0].derivative,
            #                                   context=self.p[0].context)
            #                           ]
            #            c = self.leading_coefficient()
            #            for _ in self.p[1:]:
            #                intermediate.append(_Dterm(coeff=_.coeff/c, # nsimplify done in LHDP
            #                                            derivative = _.derivative,
            #                                            context = _.context
            #                                           ))
            #            self.p = intermediate[:]
            scaled = primitive([_.coeff for _ in self.p]) if self.context.fraction_free else None
            if scaled is not None:
                # the equation is divided by what makes its coefficients
                # coprime; like the leading coefficient in make_monic, that
                # has to be nonzero
                coeff = self.p[0].coeff
                if coeff != ONE:
                    self.context.divisors.append(coeff)
                for term, coeff in zip(self.p, scaled, strict=True):
                    term.coeff = coeff
            else:
                self.make_monic()
        # XXX: wrong place?
        if self.p:
            self.order = self.p[0].order
            self.function = self.p[0].function
            self.comparison_vector = self.p[0].comparison_vector

    def __bool__(self):
        return len(self.p) > 0

    @profile_if_enabled
    #    @cache
    def __lt__(self, other):
        for _ in zip(self.p, other.p, strict=False):
            if eq(_[0], _[1]):
                continue
            return _[0] < _[1]
        return False

    @profile_if_enabled
    def __le__(self, other):
        return eq(self, other) or self < other

    @profile_if_enabled
    def __eq__(self, other):
        if other is None:
            return False
        if self is other:
            return True
        if len(self.p) != len(other.p):
            return False
        return all(_[0] == _[1] for _ in zip(self.p, other.p, strict=True))

    def show(self, rich=True, short=False):
        if not rich:
            return str(self)
        res = ""
        show_output([_.show() for _ in self.p])
        if self.multipliers or self.nonmultipliers:
            res += f"[{self.multipliers}], [{self.nonmultipliers}]"
        return res

    @profile_if_enabled
    def diff(self, *args):
        new_dterms = {}
        for dterm in self.p:
            _dterms = dterm.diff(*args)
            for new_dterm in _dterms:
                if new_dterm.comparison_vector in new_dterms:
                    new_dterms[new_dterm.comparison_vector].coeff += new_dterm.coeff
                else:
                    new_dterms[new_dterm.comparison_vector] = new_dterm
        return self.__class__(
            e=0, dterms=[_ for _ in new_dterms.values() if _.coeff], context=self.context
        )

    def __str__(self):
        m = [self.context.independent[_] for _ in self.multipliers]
        n = [self.context.independent[_] for _ in self.nonmultipliers]
        result = " + ".join([str(_) for _ in self.p])
        if m or n:
            result += f", {m}, {n}"
        return result

    def __repr__(self):
        return str(self)

    @profile_if_enabled
    def __hash__(self):
        if self.hash == 0:
            self.hash = hash("".join([str(hash(_)) for _ in self.p]))
        return self.hash

    @profile_if_enabled
    def xreplace(self, d):
        return self.__class__(self.expression().xreplace(d), self.context)

    _cache_key = __hash__


@profile_if_enabled
def analyze_term(context, term):
    operands = split_into_operands(term)
    coeffs = []
    d = []
    for operand in operands:
        if is_function(operand):
            if context.is_ctxfunc(operand):
                d.append(operand)
            else:
                coeffs.append(operand)
        elif is_derivative(operand):
            if context.is_ctxfunc(operand.args[0]):
                d.append(operand)
            else:
                coeffs.append(operand)
        else:
            coeffs.append(operand)
    coeffs = functools.reduce(mul, coeffs, S.One)
    if not d:
        return None
    return str(d[0]), d[0], coeffs


@profile_if_enabled
def split_into_operands(term):
    if is_derivative(term) or is_function(term):
        return [term]
    return term.as_ordered_factors()


@profile_if_enabled
def reorder(S, context, ascending=False):
    return sorted(S, reverse=not ascending)


@profile_if_enabled
def reduce_by_system(e: LHDP, S: list, context: Context) -> LHDP | None:
    reducing = True
    gen = S[:]
    while reducing:
        for dp in gen:
            enew = _reduce(e, dp, context)
            if enew is None:
                return None
            elif e == enew:
                reducing = False
            else:
                e = enew
                gen = [_ for _ in S if _]
                reducing = True
    return enew


@profile_if_enabled
def _reduce_inner(e1, e2, context):
    """One reduction step of e1 modulo e2 (Schwarz, Algorithm 2.4).

    Finds the first term of e1 that is a derivative ∂^dif of e2's leading
    derivative and eliminates it: lc * e1 - coeff * ∂^dif(e2), lc being
    e2's leading coefficient (1 unless the context is fraction free).

    Returns:
        * e1 itself (same object) if no term of e1 is reducible by e2,
        * None if the reduction yields zero,
        * the reduced LHDP otherwise.

    Schwarz, Example 2.33, p. 48
    >>> from sympy import Function, simplify
    >>> x = Symbol('x')
    >>> y = Symbol('y')
    >>> z = Function('z')(x, y)
    >>> ctx = Context([z], [x, y])
    >>> e1 = LHDP(Derivative(z, y) - ((x**2) / (y**2)) * Derivative(z, x) - z * (x - y) / y**2, ctx)
    >>> e2 = LHDP(Derivative(z, x) + z / x, ctx)
    >>> _reduce_inner(e1, e2, ctx).expression().simplify()
    Derivative(z(x, y), y) + z(x, y)/y
    >>> e1 = LHDP(Derivative(z, y) - ((x**2) / (y**2)) * Derivative(z, x) - z * (x - y) / y**2, ctx)
    >>> e2 = LHDP(Derivative(z, y) + z / y, ctx)
    >>> _reduce_inner(e1, e2, ctx).expression().simplify()
    Derivative(z(x, y), x) + z(x, y)/x
    """
    for term in e1.p:
        if term.function != e2.function:
            continue
        dif = [a - b for a, b in zip(term.order, e2.order, strict=True)]
        if any(d < 0 for d in dif):
            continue
        return _subtract_derivative(e1, e2, term.coeff, get_diff_vars(context, dif))
    return e1


@profile_if_enabled
def _subtract_derivative(e1, e2, factor, variables):
    """lc * e1 - factor * ∂^variables(e2), or None if that is zero; lc is
    e2's leading coefficient, 1 unless the context is fraction free.

    With no variables this is step S2 of Algorithm 2.4, e1 - factor * e2.

    Differentiating e2 w.r.t. H yields Y_H twice, from (-x/H) * Y_H and
    from (-x/H**2) * Y; the two contributions cancel (Schwarz, Example 5.16):

    >>> from sympy import Function, diff
    >>> x, H = Symbol('x'), Symbol('H')
    >>> X, Y = Function('X')(H, x), Function('Y')(H, x)
    >>> ctx = Context([X, Y], [x, H])
    >>> e1 = LHDP(diff(Y, H, x) + diff(Y, x) / H, ctx)
    >>> e2 = LHDP(diff(Y, x) - x * diff(Y, H) / H - X / (2 * H * x) - x * Y / H**2, ctx)
    >>> print(_reduce(e1, e2, ctx))
    D(Y(H, x), (H, 2)) + (1/(2*x**2)) * D(X(H, x), H) + (1/H) * D(Y(H, x), H) + (-1/H**2) * Y(H, x)
    """
    e2_terms = [dterm for p in e2.p for dterm in p.diff(*variables)] if variables else e2.p
    # copies of e1's terms: `hit.coeff -= product` below creates a new
    # coefficient (they are immutable) but rebinds it on the _Dterm, which
    # without the copy would be e1's own, changing e1 behind the caller's back.
    # Differentiating e2 may give several terms with the same derivative
    # (product rule), so they must be added up, not kept side by side
    remaining = OrderedDict((_.comparison_vector, _.copy()) for _ in e1.p)
    lc = e2.p[0].coeff
    if lc != ONE:
        # e1 is multiplied by lc: the result is equivalent where lc != 0
        e2.context.divisors.append(lc)
        for hit in remaining.values():
            hit.coeff *= lc
    for dterm in e2_terms:
        product = dterm.coeff * factor
        hit = remaining.get(dterm.comparison_vector)
        if hit is None:
            remaining[dterm.comparison_vector] = _Dterm(
                coeff=-product, derivative=dterm.derivative, context=dterm.context
            )
        elif hit.coeff == product:
            del remaining[dterm.comparison_vector]
        else:
            hit.coeff -= product
    dterms = [_ for _ in remaining.values() if _.coeff]
    if not dterms:
        return None
    return LHDP(e=0, context=e2.context, dterms=dterms)


@profile_if_enabled
def get_diff_vars(context, dif):
    variables = []
    for i in range(len(context.independent)):
        if dif[i] != 0:
            variables.extend([context.independent[i]] * abs(dif[i]))
    return variables


@profile_if_enabled
def _reduce(e1: LHDP, e2: LHDP, context: Context) -> LHDP | None:
    while True:
        new_e1 = _reduce_inner(e1, e2, context)
        if not new_e1:
            return None
        if e1 is new_e1:
            return e1
        e1 = new_e1


@profile_if_enabled
def autoreduce(S, context):
    dps = list(S)
    i = 0
    _p, r = dps[: i + 1], dps[i + 1 :]
    while r:
        newdps = []
        have_reduced = False
        for _r in r:
            rnew = reduce_by_system(_r, _p, context)
            have_reduced = have_reduced or _r != rnew
            if rnew:
                newdps.append(rnew)
        # print("NNNNNNNNNNNNNNNNNNNNNNNN")
        # for _ in newdps:
        #    print("===>", _)
        dps = reorder(_p + [_ for _ in newdps if _ not in _p], context, ascending=True)
        if not have_reduced:
            i += 1
        else:
            i = 0
        _p, r = dps[: i + 1], dps[i + 1 :]
    return dps


def vec_degree(v, m):
    return m[v]


@profile_if_enabled
def vec_multipliers(m, M, Vars):
    """multipliers and nonmultipliers for differential vectors aka tuples

    m   : a tuple representing a differential vector
    M   : the complete set of differential vectors
    Vars: a tuple representing the order of indizes in m
          Examples:
              (0,1,2) means first index in m represents the highest variable
              (2,1,0) means last index in m represents the highest variable

    Returns (multipliers, nonmultipliers), as lists of indices in m.

    Follows the Maple procedure Janet in Amir Hashemi's invbasis,
    https://amirhashemi.iut.ac.ir/sites/amirhashemi.iut.ac.ir/files//file_basepage/invbasis.txt

    ......................................................
    The doctest example is from Schwarz, Example C.1, p. 384
    This example is in on variables x1,x2,x3, with x3 the highest rated variable.
    So we have to specify (2,1,0) to represent this

    >>> M = [(2, 2, 3), (3, 0, 3), (3, 1, 1), (0, 1, 1)]
    >>> r = vec_multipliers(M[0], M, (2, 1, 0))
    >>> print(M[0], r[0], r[1])
    (2, 2, 3) [2, 1, 0] []
    >>> r = vec_multipliers(M[1], M, (2, 1, 0))
    >>> print(M[1], r[0], r[1])
    (3, 0, 3) [2, 0] [1]
    >>> r = vec_multipliers(M[2], M, (2, 1, 0))
    >>> print(M[2], r[0], r[1])
    (3, 1, 1) [1, 0] [2]
    >>> r = vec_multipliers(M[3], M, (2, 1, 0))
    >>> print(M[3], r[0], r[1])
    (0, 1, 1) [1] [0, 2]
    >>> N = [[0, 2], [2, 0], [1, 1]]
    >>> r = vec_multipliers(N[0], N, (0, 1))
    >>> print(r)
    ([1], [0])
    >>> r = vec_multipliers(N[1], N, (0, 1))
    >>> print(r)
    ([0, 1], [])
    >>> r = vec_multipliers(N[2], N, (0, 1))
    >>> print(r)
    ([1], [0])
    >>> r = vec_multipliers(N[0], N, (1, 0))
    >>> print(r)
    ([1, 0], [])
    >>> r = vec_multipliers(N[1], N, (1, 0))
    >>> print(r)
    ([0], [1])
    >>> r = vec_multipliers(N[2], N, (1, 0))
    >>> print(r)
    ([0], [1])
    >>> # next example form Gerdt/Blinkov: Janet-like monomial divisiom, Table1
    >>> # x1 -> Index 2
    >>> # x2 -> Index 1 (this is easy)
    >>> # x3 -> Index 0
    >>> U = [[0, 0, 5], [1, 2, 2], [2, 0, 2], [1, 4, 0], [2, 1, 0], [5, 0, 0]]
    >>> vec_multipliers(U[0], U, (2, 1, 0))
    ([2, 1, 0], [])
    >>> vec_multipliers(U[1], U, (2, 1, 0))
    ([1, 0], [2])
    >>> vec_multipliers(U[2], U, (2, 1, 0))
    ([0], [1, 2])
    >>> vec_multipliers(U[3], U, (2, 1, 0))
    ([1, 0], [2])
    >>> vec_multipliers(U[4], U, (2, 1, 0))
    ([0], [1, 2])
    >>> vec_multipliers(U[5], U, (2, 1, 0))
    ([0], [1, 2])
    >>> # the first variable is compared with its own maximal degree
    >>> V = [(0, 2), (1, 0)]
    >>> vec_multipliers(V[0], V, (0, 1))
    ([1], [0])
    >>> vec_multipliers(V[1], V, (0, 1))
    ([0, 1], [])
    >>> vec_multipliers(V[0], V[:1], (0, 1))
    ([0, 1], [])
    >>> # Iohara/Malbos, Example 3.2.6: five variables, the last index is the highest
    >>> W = [
    ...     (0, 0, 0, 1, 1),
    ...     (0, 0, 1, 0, 1),
    ...     (0, 1, 0, 0, 1),
    ...     (0, 0, 0, 2, 0),
    ...     (0, 0, 1, 1, 0),
    ...     (0, 0, 2, 0, 0),
    ... ]
    >>> for w in W:
    ...     print(w, *vec_multipliers(w, W, (4, 3, 2, 1, 0)))
    (0, 0, 0, 1, 1) [4, 3, 2, 1, 0] []
    (0, 0, 1, 0, 1) [4, 2, 1, 0] [3]
    (0, 1, 0, 0, 1) [4, 1, 0] [2, 3]
    (0, 0, 0, 2, 0) [3, 2, 1, 0] [4]
    (0, 0, 1, 1, 0) [2, 1, 0] [3, 4]
    (0, 0, 2, 0, 0) [2, 1, 0] [3, 4]
    """
    # Janet: the highest variable is a multiplier if m has the maximal degree in it
    d = max((vec_degree(Vars[0], u) for u in M), default=0)
    mult = []
    if vec_degree(Vars[0], m) == d:
        mult.append(Vars[0])
    for j in range(1, len(Vars)):
        v = Vars[j]
        dd = [vec_degree(x, m) for x in Vars[:j]]
        V = []
        for _u in M:
            if [vec_degree(_v, _u) for _v in Vars[:j]] == dd:
                V.append(_u)
        if vec_degree(v, m) == max((vec_degree(v, _u) for _u in V), default=0):
            mult.append(v)
    return mult, sorted(set(Vars) - set(mult))


coll = namedtuple('coll', ['monom', 'dp', 'multipliers', 'nonmultipliers'])


def _in_janet_class(monom, base, multipliers, nonmultipliers):
    """monom lies in the Janet class of base: it is base multiplied by
    multiplier variables only (Schwarz, p. 383)."""
    return all(monom[i] >= base[i] for i in multipliers) and all(
        monom[i] == base[i] for i in nonmultipliers
    )


@profile_if_enabled
def complete(S, context):
    """Janet-complete S, polynomials with the same leading function.

    Schwarz, Algorithm C1, p. 385: for every element and each of its
    nonmultipliers, the derivative by that variable is added unless its
    leading monomial already lies in the Janet class of some element.
    Repeat until nothing is missing. The result is not sorted.
    """
    result = set(S)
    variables = range(len(context.independent))
    while True:
        orders = [dp.order for dp in result]
        classes = [(dp, *vec_multipliers(dp.order, orders, variables)) for dp in result]
        missing = []
        for dp, _, nonmultipliers in classes:
            for n in nonmultipliers:
                raised = list(dp.order)
                raised[n] += 1
                if not any(
                    _in_janet_class(raised, other.order, mult, nonmult)
                    for other, mult, nonmult in classes
                ):
                    missing.append(dp.diff(context.independent[n]))
        if not missing:
            return list(result)
        result.update(missing)


@profile_if_enabled
def complete_system(S, context):
    """
    Algorithm C1, p. 385

    >>> from sympy import *
    >>> from delierium.matrix_order import Mgrlex, Mlex

    >>> x, y, z = symbols("x, y, z")
    >>> tvars = (x, y, z)
    >>> w = Function("w")(*tvars)
    >>> # these DPs are constructed from C1, pp 384
    >>> h1 = Derivative(w, x, x, x, y, y, z, z)
    >>> h2 = diff(w, x, x, x, z, z, z)
    >>> h3 = diff(w, x, y, z, z, z)
    >>> h4 = diff(w, x, y)
    >>> ctx = Context((w,), (x, y, z), Mgrlex)
    >>> dps = [LHDP(_, ctx) for _ in [h1, h2, h3, h4]]
    >>> cs = complete_system(dps, ctx)
    >>> # things are sorted up
    >>> for _ in cs:
    ...     print(_)
    D(w(x, y, z), x, y)
    D(w(x, y, z), x, y, z)
    D(w(x, y, z), (x, 2), y)
    D(w(x, y, z), x, y, (z, 2))
    D(w(x, y, z), (x, 2), y, z)
    D(w(x, y, z), (x, 3), y)
    D(w(x, y, z), x, y, (z, 3))
    D(w(x, y, z), (x, 2), y, (z, 2))
    D(w(x, y, z), (x, 3), y, z)
    D(w(x, y, z), (x, 3), (y, 2))
    D(w(x, y, z), (x, 2), y, (z, 3))
    D(w(x, y, z), (x, 3), (z, 3))
    D(w(x, y, z), (x, 3), y, (z, 2))
    D(w(x, y, z), (x, 3), (y, 2), z)
    D(w(x, y, z), (x, 3), y, (z, 3))
    D(w(x, y, z), (x, 3), (y, 2), (z, 2))
    >>> # example from Schwarz, pp 54
    >>> w = Function("w")(x, y)
    >>> z = Function("z")(x, y)
    >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
    >>> g5 = (
    ...     diff(z, x, x, x)
    ...     + diff(w, y, y) * 8 * y**2
    ...     + diff(w, x, x) / y
    ...     - diff(z, x, y) * 4 * y**2
    ...     - diff(z, x) * 32 * y
    ...     - 16 * w
    ... )
    >>> g6 = diff(z, x, x, y) - diff(z, y, y) * 4 * y**2 - diff(z, y) * 8 * y
    >>> ctx = Context((w, z), (x, y), Mgrlex)
    >>> dps = [LHDP(_, ctx) for _ in [g1, g5, g6]]
    >>> cs = complete_system(dps, ctx)
    >>> for _ in cs:  # doctest: +NORMALIZE_WHITESPACE
    ...     print(_)
    D(z(x, y), (y, 2)) + (1/(2*y)) * D(z(x, y), y)
    D(z(x, y), x, (y, 2)) + (1/(2*y)) * D(z(x, y), x, y)
    D(z(x, y), (x, 2), y) + (-4*y**2) * D(z(x, y), (y, 2)) + (-8*y) * D(z(x, y), y)
    D(z(x, y), (x, 3)) + (1/y) * D(w(x, y), (x, 2)) + (8*y**2) * D(w(x, y), (y, 2)) + (-4*y**2) *
    D(z(x, y), x, y) + (-32*y) * D(z(x, y), x) + (-16) * w(x, y)
    """
    s = bucket(S, key=lambda d: d.leading_function())
    res = flatten([complete(s[k], context) for k in s])
    return reorder(res, context, ascending=True)


@profile_if_enabled
def split_by_function(S, context):
    s = bucket(S, key=lambda d: d.leading_function())
    murksi = [find_integrable_conditions(s[k], context) for k in s]
    return flatten(murksi)


@profile_if_enabled
def _integrability_pairs(S, context):
    """(ei, n, ej, m): the derivative of ei by its nonmultiplier n and the
    derivative of ej by the variables m (ej's multipliers only) have the
    same leading derivative."""
    result = list(S)
    if len(result) == 1:
        return

    vars = list(range(len(context.independent)))

    # reverse order as in context the highest independent is first,
    # but for multiplier computation it is last
    monomials = [(_, list(_.order)) for _ in result]

    ms = tuple([_[1] for _ in monomials])

    def map_old_to_new(i):
        return context.independent[i]

    # multiplier-collection is our M
    multiplier_collection = []
    for dp, monom in monomials:
        # S1
        _multipliers, _nonmultipliers = vec_multipliers(monom, ms, vars)
        multiplier_collection.append(
            coll(
                monom,
                dp,
                [map_old_to_new(_) for _ in _multipliers],
                [map_old_to_new(_) for _ in _nonmultipliers],
            )
        )

    for ei, ej in pairs_exclude_diagonal(multiplier_collection):
        for n in ei.nonmultipliers:
            m = _multiplicative_derivative(ei, n, ej, context)
            if m is not None:
                yield ei.dp, n, ej.dp, m


@profile_if_enabled
def find_integrable_conditions(S, context):
    result = []
    for ei, n, ej, m in _integrability_pairs(S, context):
        condition = _difference(ei.diff(n), ej.diff(*m) if m else ej, context)
        if condition is not None:
            result.append(condition)
    return result


def _multiplicative_derivative(ei, n, ej, context):
    """The variables (with repetitions) by which ej's leading derivative has to
    be differentiated to become the derivative of ei's leading derivative by
    its nonmultiplier n, using only ej's multipliers, each of them any number
    of times; None if that is impossible."""
    raised = list(ei.monom)
    raised[context.independent.index(n)] += 1
    difference = [a - b for a, b in zip(raised, ej.monom, strict=True)]
    if any(d < 0 for d in difference) or any(
        d and v not in ej.multipliers for v, d in zip(context.independent, difference, strict=True)
    ):
        return None
    return [v for v, d in zip(context.independent, difference, strict=True) for _ in range(d)]


def _difference(d1, d2, context):
    """lc2 * d1 - lc1 * d2 as an LHDP, lc1 and lc2 their leading coefficients
    (1 unless the context is fraction free), so that the leading derivatives
    cancel; None if it vanishes. d1's terms are modified."""
    lc1, lc2 = d1.p[0].coeff, d2.p[0].coeff
    if lc1 != lc2:
        context.divisors.extend(_ for _ in (lc1, lc2) if _ != ONE)
        for t in d1.p:
            t.coeff *= lc2
    else:
        lc1 = ONE
    new_terms = []
    terms_from_first = {_.comparison_vector: _ for _ in d1.p}
    for s in d2.p:
        coeff = s.coeff if lc1 == ONE else s.coeff * lc1
        if s.comparison_vector in terms_from_first:
            terms_from_first[s.comparison_vector].coeff -= coeff
        else:
            new_terms.append(_Dterm(coeff=-coeff, derivative=s.derivative, context=context))
    dterms = [_ for _ in [*new_terms, *terms_from_first.values()] if _.coeff]
    return LHDP(e=0, context=context, dterms=dterms) if dterms else None


class JanetBasis:
    def __init__(self, S, dependent, independent, sort_order=Mgrevlex, fraction_free=True):
        """
        Parameters:
            * List of homogenous PDE's
            * List of dependent variables, i.e. the functions to searched for
            * List of variables
            * sort order, default is grevlex
            * fraction_free: during the completion, keep the coefficients of
              every equation coprime polynomials instead of dividing by the
              leading coefficient; this avoids the growth of the rational
              function coefficients. The basis is made monic at the end.

        >>> from sympy import *
        >>> from delierium.matrix_order import Mgrlex, Mlex
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> f1 = diff(w, y) + x * diff(z, y) / (2 * y * (x**2 + y)) - w / y
        >>> f2 = diff(z, x, y) + y * diff(w, y) / x + 2 * y * diff(z, x) / x
        >>> f3 = diff(w, x, y) - 2 * x * diff(z, x, 2) / y - x * diff(w, x) / y**2
        >>> f4 = (
        ...     diff(w, x, y)
        ...     + diff(z, x, y)
        ...     + diff(w, y) / (2 * y)
        ...     - diff(w, x) / y
        ...     + x * diff(z, y) / y
        ...     - w / (2 * y**2)
        ... )
        >>> f5 = diff(w, y, y) + diff(z, x, y) - diff(w, y) / y + w / (y**2)
        >>> system_2_24 = [f1, f2, f3, f4, f5]
        >>> checkS = JanetBasis(system_2_24, (w, z), (x, y))
        >>> for _ in checkS.S:
        ...     print(_)
        D(z(x, y), y)
        D(z(x, y), x) + (1/(2*y)) * w(x, y)
        D(w(x, y), y) + (-1/y) * w(x, y)
        D(w(x, y), x)
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
        >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
        >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
        >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
        >>> system_2_25 = [g2, g3, g4, g1]
        >>> checkS = JanetBasis(system_2_25, (w, z), (x, y))
        >>> for _ in checkS.S:
        ...     print(_)
        D(z(x, y), y)
        D(z(x, y), x) + (1/(2*y)) * w(x, y)
        D(w(x, y), y) + (-1/y) * w(x, y)
        D(w(x, y), x)
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> f1 = diff(w, y) + x * diff(z, y) / (2 * y * (x**2 + y)) - w / y
        >>> f2 = diff(z, x, y) + y * diff(w, y) / x + 2 * y * diff(z, x) / x
        >>> f3 = diff(w, x, y) - 2 * x * diff(z, x, 2) / y - x * diff(w, x) / y**2
        >>> f4 = (
        ...     diff(w, x, y)
        ...     + diff(z, x, y)
        ...     + diff(w, y) / (2 * y)
        ...     - diff(w, x) / y
        ...     + x * diff(z, y) / y
        ...     - w / (2 * y**2)
        ... )
        >>> f5 = diff(w, y, y) + diff(z, x, y) - diff(w, y) / y + w / (y**2)
        >>> system_2_24 = [f1, f2, f3, f4, f5]
        >>> checkS = JanetBasis(system_2_24, (w, z), (x, y), Mgrlex)
        >>> for _ in checkS.S:
        ...     print(_)
        D(z(x, y), y)
        D(z(x, y), x) + (1/(2*y)) * w(x, y)
        D(w(x, y), y) + (-1/y) * w(x, y)
        D(w(x, y), x)
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
        >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
        >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
        >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
        >>> system_2_25 = [g2, g3, g4, g1]
        >>> checkS = JanetBasis(system_2_25, (w, z), (x, y), Mgrlex)
        >>> for _ in checkS.S:
        ...     print(_)
        D(z(x, y), y)
        D(z(x, y), x) + (1/(2*y)) * w(x, y)
        D(w(x, y), y) + (-1/y) * w(x, y)
        D(w(x, y), x)
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
        >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
        >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
        >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
        >>> system_2_25 = [g2, g3, g4, g1]
        >>> checkS = JanetBasis(system_2_25, (w, z), (x, y), Mlex)
        >>> for _ in checkS.S:
        ...     print(_)
        D(z(x, y), y)
        D(z(x, y), x, y)
        D(z(x, y), (x, 2))
        w(x, y) + (2*y) * D(z(x, y), x)
        """
        self.context = context = Context(dependent, independent, sort_order)
        context.fraction_free = fraction_free
        if not isinstance(S, Iterable):
            # XXX bad criterion
            self.S = [S]
        else:
            self.S = S[:]
        self.S = reorder([LHDP(s, context, dterms=[]) for s in self.S], context, ascending=True)
        self._complete(context)
        if fraction_free:
            context.fraction_free = False
            for e in self.S:
                e.make_monic()
            self.S = reorder(self.S, context, ascending=True)

    def _complete(self, context):
        old = []
        while 1:
            if old == self.S:
                # no change since last run
                return
            old = self.S[:]
            #            self.show(rich=True, short=False, heading="This is where we start")
            #         import pdb; pdb.set_trace()
            self.S = autoreduce(self.S, context)
            #            self.show(rich=False, short=True, heading="after autoreduce")
            #            import pdb; pdb.set_trace()
            self.S = complete_system(self.S, context)
            #            self.show(rich=False, short=True, heading="after complete system")
            conditions = list(split_by_function(self.S, context))
            #            print("after conditions")
            #            for _ in conditions:
            #                print(_)
            reduced = [reduce_by_system(_m, self.S, context) for _m in conditions]
            #            print("after reduced")
            #            for _ in reduced:
            #                print(_)
            #            print(reduced)
            reduced = [_ for _ in reduced if _]
            #            print("after reduced")
            if not reduced:
                self.S = reorder(self.S, context, ascending=True)
                #                print("ÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖÖ")
                return
            self.S += [_ for _ in reduced if _ not in self.S]
            self.S = reorder(self.S, context, ascending=True)

    def representation(self, e):
        """e as a combination of the basis elements and their derivatives.

        Returns (terms, remainder): e = self.combination(terms) + remainder,
        each term (c, variables, j) standing for c times the j-th basis
        element differentiated by variables. The remainder
        is 0 if and only if e follows from the Janet basis, e.g. for every
        equation the basis was computed from. The representation is not
        unique; here the highest reducible term is eliminated first.

        >>> from sympy import *
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> # Schwarz, system (2.25)
        >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
        >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
        >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
        >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
        >>> janet = JanetBasis([g2, g3, g4, g1], (w, z), (x, y))
        >>> for _ in janet.S:
        ...     print(_)
        D(z(x, y), y)
        D(z(x, y), x) + (1/(2*y)) * w(x, y)
        D(w(x, y), y) + (-1/y) * w(x, y)
        D(w(x, y), x)
        >>> terms, remainder = janet.representation(g2)
        >>> for c, variables, j in terms:
        ...     print(c, variables, j)
        1 (x,) 3
        4*y**2 () 2
        -8*y**2 () 1
        >>> remainder
        0
        >>> simplify(janet.combination(terms) - g2)
        0

        Something that does not follow from the basis leaves a remainder:

        >>> janet.representation(diff(z, x, y) + z)[1]
        z(x, y)
        """
        terms, remaining = _reduce_with_cofactors(e, self.S, self.context)
        result = [(c.as_expr(), v, j) for (v, j), c in terms.items() if c]
        return result, sum((t.expression() for t in remaining.values()), S.Zero)

    def assumed_nonzero(self):
        """The factors assumed nonzero in computing the Janet basis.

        Whenever an equation is brought into normal form, it is divided by its
        leading coefficient (fraction free: by what makes its coefficients
        coprime polynomials, and a reduction multiplies it by the leading
        coefficient of the reducing equation). For values of parameters (or
        points) where one of these vanishes, the Janet basis may differ: the
        result is the generic case. Returns the irreducible nonconstant factors of the numerators of
        these coefficients, see nonzero_factors. Factors in the independent
        variables only mark singular points or lines; factors in parameters
        mark special cases that may have a different Janet basis.

        >>> from sympy import *
        >>> x, y, a = symbols("x y a")
        >>> z = Function("z")(x, y)
        >>> janet = JanetBasis([(a - 1) * diff(z, x) + z, x * diff(z, y) - z], [z], [y, x])
        >>> janet.assumed_nonzero()
        [x, a - 1, -a + x + 1]
        >>> for _ in janet.S:
        ...     print(_)
        z(x, y)

        For a = 1 the first equation is z = 0 itself, with the same result;
        for x = 0 the second one says z = 0. The factor x - a + 1 comes from
        an intermediate equation of the (fraction free) completion; it
        depends on x, so it excludes no special value of a.
        """
        divisors = self.context.divisors
        cached = getattr(self, "_assumed", None)
        if cached is None or cached[0] != len(divisors):
            factors = nonzero_factors(divisors)
            self._assumed = cached = (
                len(divisors),
                factors,
                split_assumptions(factors, self.context.independent),
            )
        return cached[1]

    def parameter_conditions(self):
        """The special cases of the parameters that the Janet basis excludes.

        Each entry is a list of expressions in the parameters (the symbols
        other than the independent variables) that vanish together exactly
        where one of the factors of assumed_nonzero vanishes identically in
        the independent variables. There the Janet basis may be different.

        >>> from sympy import *
        >>> x, y, a, b = symbols("x y a b")
        >>> z = Function("z")(x, y)
        >>> janet = JanetBasis(
        ...     [(a * x + b) * diff(z, x) + z, (a - 1) * diff(z, y) - x * z], [z], [y, x]
        ... )
        >>> janet.assumed_nonzero()
        [x, a - 1, a*x + b]
        >>> janet.parameter_conditions()
        [[a - 1], [a, b]]
        >>> janet.singular_loci()
        [x]
        """
        self.assumed_nonzero()
        return self._assumed[2][0]

    def singular_loci(self):
        """The factors of assumed_nonzero that vanish only on points, curves,
        ... of the independent variables, never identically: the Janet basis
        does not hold there, but everywhere else."""
        self.assumed_nonzero()
        return self._assumed[2][1]

    def type(self):
        """The type of the Janet basis: leading derivatives, parametric
        derivatives, dimension of the solution space and, where Schwarz
        tabulates it, his name of the type, see janet_type."""
        return janet_type(self.S, self.context)

    def combination(self, terms):
        """sum of c * (j-th basis element differentiated by variables) for
        the terms (c, variables, j) of representation."""
        result = S.Zero
        for c, variables, j in terms:
            b = self.S[j].expression()
            result += c * (b.diff(*variables) if variables else b)
        return result

    def show(self, rich=True, short=False, heading=""):
        """Print the Janet basis with leading derivative first."""
        if heading:
            print(heading)
        for _ in self.S:
            _.show()

    def rank(self):
        """The rank of the Janet basis: the dimension of the solution space
        of the system, i.e. the number of parametric derivatives (oo if
        there are infinitely many), type().dimension. For the determining
        equations of a differential equation it is the dimension of its Lie
        algebra of point symmetries.

        Schwarz, system (2.25): only w and z themselves are parametric.

        >>> from sympy import *
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
        >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
        >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
        >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
        >>> JanetBasis([g2, g3, g4, g1], (w, z), (x, y)).rank()
        2

        z_x = 0 leaves z an arbitrary function of y:

        >>> JanetBasis([diff(z, x)], [z], [x, y]).rank()
        oo
        """
        return self.type().dimension

    def order(self):
        """The order of the Janet basis, Schwarz's name for its rank."""
        return self.rank()

    def parametric_derivatives(self, max_order=None):
        """The parametric derivatives: those that are no derivative of a
        leading derivative, whose values at a point can be chosen freely;
        their number is the rank. None if there are infinitely many, unless
        max_order is given: then those of total order up to max_order.
        Highest ranked first.

        >>> from sympy import *
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> w = Function("w")(x, y)
        >>> # Schwarz, system (2.25)
        >>> g1 = diff(z, y, y) + diff(z, y) / (2 * y)
        >>> g2 = diff(w, x, x) + 4 * diff(w, y) * y**2 - 8 * (y**2) * diff(z, x) - 8 * w * y
        >>> g3 = diff(w, x, y) - diff(z, x, x) / 2 - diff(w, x) / (2 * y) - 6 * (y**2) * diff(z, y)
        >>> g4 = diff(w, y, y) - 2 * diff(z, x, y) - diff(w, y) / (2 * y) + w / (2 * y**2)
        >>> JanetBasis([g2, g3, g4, g1], (w, z), (x, y)).parametric_derivatives()
        [w(x, y), z(x, y)]
        >>> janet = JanetBasis([diff(z, x)], [z], [x, y])
        >>> janet.parametric_derivatives() is None
        True
        >>> janet.parametric_derivatives(2)
        [Derivative(z(x, y), (y, 2)), Derivative(z(x, y), y), z(x, y)]
        """
        if max_order is None:
            return self.type().parametric
        return [d for d, principal in self._classified_derivatives(max_order) if not principal]

    def principal_derivatives(self, max_order):
        """The principal derivatives of total order up to max_order: the
        derivatives of the leading derivatives, which the Janet basis
        determines from the parametric ones. There are always infinitely
        many, hence the bound. Highest ranked first.

        >>> from sympy import *
        >>> x, y = symbols("x y")
        >>> z = Function("z")(x, y)
        >>> JanetBasis([diff(z, x)], [z], [x, y]).principal_derivatives(2)
        [Derivative(z(x, y), (x, 2)), Derivative(z(x, y), x, y), Derivative(z(x, y), x)]
        """
        return [d for d, principal in self._classified_derivatives(max_order) if principal]

    def _classified_derivatives(self, max_order):
        """(derivative, is principal) for every derivative of every unknown
        function of total order up to max_order, highest ranked first."""
        context = self.context
        lead = [(b.function, tuple(b.order)) for b in self.S]
        terms = []
        for f in context.dependent:
            orders = [o for g, o in lead if g == f]
            for o in product(range(max_order + 1), repeat=len(context.independent)):
                if sum(o) <= max_order:
                    principal = any(
                        all(a >= b for a, b in zip(o, lo, strict=True)) for lo in orders
                    )
                    derivative = _derivative(f, o, context)
                    terms.append(
                        (_Dterm(coeff=1, derivative=derivative, context=context), principal)
                    )
        terms.sort(key=lambda t: t[0], reverse=True)
        return [(t.derivative, principal) for t, principal in terms]


def nonzero_factors(coefficients):
    """The irreducible nonconstant factors of the numerators of coefficients
    (Coeff or expressions), each once, up to sign, sorted."""
    result = set()
    for c in coefficients:
        if isinstance(c, Coeff) and c.is_field:
            num = c.f.numer.as_expr()
        else:
            num = numer(together(c.as_expr() if isinstance(c, Coeff) else c))
        if num.is_number:
            continue
        # factor in a polynomial ring of just the generators occurring in num
        # (y**n is a plain variable there, where factor_list fails): not in the
        # shared coefficient field, whose generators depend on everything
        # computed before (x may be stored as sqrt(x)**2)
        try:
            factors = [f.as_expr() for f, _ in sring(num)[1].factor_list()[1]]
        except (TypeError, PolynomialError, CoercionFailed):
            factors = [num]
        for f in factors:
            if not f.is_number:
                result.add(-f if f.could_extract_minus_sign() else f)
    return sorted(result, key=default_sort_key)


def split_assumptions(factors, variables):
    """Split factors assumed nonzero into parameter conditions and singular
    loci.

    A factor vanishes identically in the variables iff all its coefficients
    w.r.t. them (terms grouped by their part depending on the variables)
    vanish; these coefficients, depending only on the parameters, are one
    parameter condition. If one of them is a nonzero number, the factor never
    vanishes identically and is a singular locus.

    >>> from sympy import exp, symbols
    >>> x, y, a, n = symbols("x y a n")
    >>> split_assumptions([n - 1, x, 2 * a * y**2 - 1, a * x * y + n - 1], [x, y])
    ([[n - 1], [a, n - 1]], [x, 2*a*y**2 - 1])
    >>> split_assumptions([y**n, y, exp(x)], [x, y])
    ([], [y])
    """
    conditions, loci = [], []
    for f in factors:
        groups = {}
        for term in Add.make_args(f.expand()):
            independent, dependent = term.as_independent(*variables, as_Add=False)
            groups[dependent] = groups.get(dependent, S.Zero) + independent
        coefficients = [c for c in groups.values() if c != 0]
        if any(c.is_number for c in coefficients):
            # b**e vanishes where b does; exp(...) nowhere
            while f.is_Pow and not f.base.is_number:
                f = f.base
            if not isinstance(f, ExpBase) and f not in loci:
                loci.append(f)
        else:
            condition = sorted(
                {-c if c.could_extract_minus_sign() else c for c in coefficients},
                key=default_sort_key,
            )
            if condition not in conditions:
                conditions.append(condition)
    return conditions, loci


class LHDPList(list):
    """A list of LHDPs, e.g. a Janet basis, with the factors assumed nonzero
    in computing it (JanetBasis.assumed_nonzero), split into
    parameter_conditions and singular_loci. They are computed by assumptions,
    a function returning the three, when first used."""

    def __init__(self, items=(), assumptions=None):
        super().__init__(items)
        self._assumptions = assumptions

    @functools.cached_property
    def _computed(self):
        return self._assumptions() if self._assumptions else ([], [], [])

    @property
    def assumed_nonzero(self):
        return self._computed[0]

    @property
    def parameter_conditions(self):
        return self._computed[1]

    @property
    def singular_loci(self):
        return self._computed[2]


def _divisor(t, S):
    """Index of an element of S whose leading derivative t's derivative is a
    derivative of, or None."""
    for j, b in enumerate(S):
        if b.function == t.function and all(a >= c for a, c in zip(t.order, b.order, strict=True)):
            return j
    return None


def _reduce_with_cofactors(e, S, context):
    """Reduce e (an expression) modulo the normalized LHDPs S, eliminating
    the highest reducible term first. Returns (terms, remaining):
    terms[(variables, j)] is the coefficient (a Coeff) of S[j] differentiated
    by variables, remaining the irreducible terms by comparison vector, and
    e = sum of the terms + remaining. Nothing is normalized, so the
    coefficients are those of e itself."""
    e = e.simplify().expand()
    if e == 0:
        return OrderedDict(), {}
    lhdp = LHDP.__new__(LHDP)
    lhdp.context = context
    lhdp._init(e)
    remaining = {t.comparison_vector: t for t in lhdp.p if t.coeff}
    terms = OrderedDict()
    while True:
        for t in sorted(remaining.values(), reverse=True):
            j = _divisor(t, S)
            if j is not None:
                break
        else:
            return terms, remaining
        b = S[j]
        variables = tuple(
            get_diff_vars(context, [a - c for a, c in zip(t.order, b.order, strict=True)])
        )
        factor = t.coeff
        key = (variables, j)
        terms[key] = terms[key] + factor if key in terms else factor
        for dterm in (b.diff(*variables) if variables else b).p:
            hit = remaining.get(dterm.comparison_vector)
            product = dterm.coeff * factor
            if hit is None:
                remaining[dterm.comparison_vector] = _Dterm(
                    coeff=-product, derivative=dterm.derivative, context=context
                )
            else:
                hit = hit.copy()
                hit.coeff = hit.coeff - product
                if hit.coeff:
                    remaining[dterm.comparison_vector] = hit
                else:
                    del remaining[dterm.comparison_vector]


def _leader_set(*leaders):
    """{(function, (x-order, y-order))} from names like "2yy" (z2_yy) or "1"."""
    return frozenset((int(name[0]), (name.count("x"), name.count("y"))) for name in leaders)


# Schwarz, Algorithmic Lie Theory, Tables 2.1 (p. 57), 2.2 (p. 62), 2.3 (p. 63):
# the types of Janet bases with solution spaces of dimension <= 3, for one
# function z1 or two functions z1 < z2 of x < y, ranking grlex; a type is
# characterized by its leading derivatives
SCHWARZ_TYPES = {
    (1, 2): {
        _leader_set("1x", "1y"): "J^(1,2)_1",
        _leader_set("1y", "1xx"): "J^(1,2)_2,1",
        _leader_set("1x", "1yy"): "J^(1,2)_2,2",
        _leader_set("1y", "1xxx"): "J^(1,2)_3,1",
        _leader_set("1xx", "1xy", "1yy"): "J^(1,2)_3,2",
        _leader_set("1x", "1yyy"): "J^(1,2)_3,3",
    },
    (2, 2): {
        _leader_set("1", "2x", "2y"): "J^(2,2)_1,1",
        _leader_set("2", "1x", "1y"): "J^(2,2)_1,2",
        _leader_set("1", "2y", "2xx"): "J^(2,2)_2,1",
        _leader_set("1", "2x", "2yy"): "J^(2,2)_2,2",
        _leader_set("1x", "1y", "2x", "2y"): "J^(2,2)_2,3",
        _leader_set("2", "1y", "1xx"): "J^(2,2)_2,4",
        _leader_set("2", "1x", "1yy"): "J^(2,2)_2,5",
        _leader_set("1", "2y", "2xxx"): "J^(2,2)_3,1",
        _leader_set("1", "2xx", "2xy", "2yy"): "J^(2,2)_3,2",
        _leader_set("1", "2x", "2yyy"): "J^(2,2)_3,3",
        _leader_set("1x", "1y", "2y", "2xx"): "J^(2,2)_3,4",
        _leader_set("1x", "1y", "2x", "2yy"): "J^(2,2)_3,5",
        _leader_set("1y", "2x", "2y", "1xx"): "J^(2,2)_3,6",
        _leader_set("1x", "2x", "2y", "1yy"): "J^(2,2)_3,7",
        _leader_set("2", "1x", "1yyy"): "J^(2,2)_3,8",
        _leader_set("2", "1xx", "1xy", "1yy"): "J^(2,2)_3,9",
        _leader_set("2", "1y", "1xxx"): "J^(2,2)_3,10",
    },
}

JanetType = namedtuple("JanetType", ["leaders", "parametric", "dimension", "name"])


def janet_type(S, context):
    """The type of the Janet basis S (LHDPs in context).

    Returns a JanetType: the leading derivatives of S; the parametric
    derivatives, i.e. those that are no derivative of a leading derivative,
    whose initial values may be chosen freely (None if there are infinitely
    many); their number, the dimension of the solution space (oo if
    infinite); and Schwarz's name of the type if his Tables 2.1 - 2.3 cover
    it: one or two functions of two variables, grlex ranking, dimension up to
    3. The functions and variables in context are highest first, so they
    correspond to his (z2, z1) and (y, x).

    Schwarz, Example 2.40, p. 61:

    >>> from sympy import *
    >>> from delierium.matrix_order import Mgrlex
    >>> x, y = symbols("x y")
    >>> z = Function("z")(x, y)
    >>> S = [
    ...     diff(z, x, 2) - y / (x * (x + y)) * diff(z, y) + diff(z, x) / x,
    ...     diff(z, x, y) + diff(z, y) / (x + y),
    ...     diff(z, y, 2) + diff(z, y) / (x + y),
    ... ]
    >>> t = janet_type(JanetBasis(S, [z], [y, x], Mgrlex).S, Context([z], [y, x], Mgrlex))
    >>> t.leaders
    [Derivative(z(x, y), (y, 2)), Derivative(z(x, y), x, y), Derivative(z(x, y), (x, 2))]
    >>> t.parametric
    [Derivative(z(x, y), y), Derivative(z(x, y), x), z(x, y)]
    >>> t.dimension, t.name
    (3, 'J^(1,2)_3,2')

    Reversing the sign of the last term of the first equation gives a two
    dimensional solution space:

    >>> S[0] = diff(z, x, 2) - y / (x * (x + y)) * diff(z, y) - diff(z, x) / x
    >>> JanetBasis(S, [z], [y, x], Mgrlex).type().name
    'J^(1,2)_2,1'
    """
    leaders = sorted(S, reverse=True)
    lead = [(b.function, tuple(b.order)) for b in leaders]
    parametric = []
    for f in context.dependent:
        orders = [o for g, o in lead if g == f]
        # finitely many parametric derivatives iff there is a leader that is a
        # pure derivative by each variable (or f itself is a leader)
        bounds = []
        for i in range(len(context.independent)):
            pure = [o[i] for o in orders if all(k == 0 for j, k in enumerate(o) if j != i)]
            bounds.append(min(pure) if pure else None)
        if None in bounds:
            return JanetType([b.leading_derivative() for b in leaders], None, oo, None)
        for o in product(*(range(n) for n in bounds)):
            if not any(all(a >= b for a, b in zip(o, lo, strict=True)) for lo in orders):
                parametric.append((f, o))
    parametric_derivatives = [
        t.derivative
        for t in sorted(
            (
                _Dterm(coeff=1, derivative=_derivative(f, o, context), context=context)
                for f, o in parametric
            ),
            reverse=True,
        )
    ]
    name = None
    m, n = len(context.dependent), len(context.independent)
    if (m, n) in SCHWARZ_TYPES and context.sort_order in (Mgrlex, Mgrevlex):
        # grlex and grevlex coincide for two variables; the type is given by
        # the minimal leading derivatives (a Janet basis may contain
        # derivatives of them as well, depending on the Janet multipliers)
        minimal = [
            (f, o)
            for f, o in lead
            if not any(
                g == f and p != o and all(a >= b for a, b in zip(o, p, strict=True))
                for g, p in lead
            )
        ]
        schwarz = frozenset((m - context.dependent.index(f), (o[1], o[0])) for f, o in minimal)
        name = SCHWARZ_TYPES[(m, n)].get(schwarz)
    return JanetType(
        [b.leading_derivative() for b in leaders],
        parametric_derivatives,
        len(parametric_derivatives),
        name,
    )


def _derivative(f, orders, context):
    variables = [(v, k) for v, k in zip(context.independent, orders, strict=True) if k]
    return Derivative(f, *variables) if variables else f


@profile_if_enabled
def integrability_conditions(S, dependent, independent, sort_order=Mgrevlex):
    """The conditions on the coefficients of S for S to be a Janet basis.

    S is a system whose leading derivatives form a Janet basis type, with
    undetermined coefficients (e.g. functions a1(x, y), ...). As in step S5a
    of Schwarz's algorithm JanetBasis (p. 59), its integrability conditions
    are reduced but not added to the system: to keep the type, the
    coefficients of the parametric derivatives in them have to vanish.
    Returns these coefficients, each up to sign, sorted.

    Schwarz, Theorem 2.15, p. 59, type J^(1,2)_1:

    >>> from sympy import *
    >>> x, y = symbols("x y")
    >>> z = Function("z")(x, y)
    >>> a, b = Function("a")(x, y), Function("b")(x, y)
    >>> integrability_conditions([diff(z, x) + a * z, diff(z, y) + b * z], [z], [y, x])
    [Derivative(a(x, y), y) - Derivative(b(x, y), x)]
    """
    context = Context(dependent, independent, sort_order)
    system = reorder([LHDP(s, context) for s in S], context, ascending=True)
    # delierium's Janet multipliers may differ from Schwarz's (the variables
    # are taken in the other order), so the system may first have to be
    # completed by derivatives of its elements; this keeps the type
    system = reorder(complete_system(system, context), context, ascending=True)
    result = set()
    for ei, n, ej, m in _integrability_pairs(system, context):
        condition = ei.expression().diff(n) - (ej.expression().diff(*m) if m else ej.expression())
        _, remaining = _reduce_with_cofactors(condition, system, context)
        for t in remaining.values():
            c = t.coeff.as_expr().expand()
            if c != 0 and -c not in result:
                result.add(c)
    return sorted(result, key=default_sort_key)


@profile_if_enabled
def is_janet_basis_of(B, S, dependent, independent, sort_order=Mgrevlex):
    """Check whether B is the Janet basis of the linear system S.

    For a fixed ranking (sort order and order of the dependent and
    independent variables) the fully reduced Janet basis with leading
    coefficients 1 is unique, so B is compared with the Janet basis of S.
    B is normalized first; scaling its elements does not matter.

    Checking only that S reduces to zero modulo B is not enough: that
    shows that S follows from B, but not that B follows from S.

    >>> from sympy import *
    >>> x, y = symbols("x y")
    >>> z = Function("z")(x, y)
    >>> w = Function("w")(x, y)
    >>> # Schwarz, system (2.24)
    >>> S = [
    ...     diff(w, y) + x * diff(z, y) / (2 * y * (x**2 + y)) - w / y,
    ...     diff(z, x, y) + y * diff(w, y) / x + 2 * y * diff(z, x) / x,
    ...     diff(w, x, y) - 2 * x * diff(z, x, 2) / y - x * diff(w, x) / y**2,
    ...     diff(w, x, y)
    ...     + diff(z, x, y)
    ...     + diff(w, y) / (2 * y)
    ...     - diff(w, x) / y
    ...     + x * diff(z, y) / y
    ...     - w / (2 * y**2),
    ...     diff(w, y, y) + diff(z, x, y) - diff(w, y) / y + w / y**2,
    ... ]
    >>> B = [diff(z, y), diff(z, x) + w / (2 * y), diff(w, y) - w / y, diff(w, x)]
    >>> is_janet_basis_of(B, S, (w, z), (x, y))
    True
    >>> is_janet_basis_of([2 * b for b in B], S, (w, z), (x, y))
    True
    >>> is_janet_basis_of(B[:3], S, (w, z), (x, y))
    False
    >>> # wrong coefficient: w/y instead of w/(2*y)
    >>> is_janet_basis_of([B[0], diff(z, x) + w / y, B[2], B[3]], S, (w, z), (x, y))
    False
    >>> # too strong: S still follows from B, but B has fewer solutions
    >>> is_janet_basis_of([*B, z], S, (w, z), (x, y))
    False
    >>> # B may also be given as LHDPs, e.g. the result of JanetBasis
    >>> is_janet_basis_of(JanetBasis(S, (w, z), (x, y)).S, S, (w, z), (x, y))
    True
    """
    context = Context(dependent, independent, sort_order)
    expected = JanetBasis(S, dependent, independent, sort_order).S
    candidate = [LHDP(b.expression() if isinstance(b, LHDP) else b, context) for b in B]
    return sorted(map(str, expected)) == sorted(map(str, candidate))


if __name__ == "__main__":
    import doctest

    doctest.testmod()
# -

# https://amirhashemi.iut.ac.ir/sites/amirhashemi.iut.ac.ir/files//file_basepage/invbasis.txt#overlay-context=contents

########### Pommaret Division #############
# def LeftPommaret(u,U,Vars):
#    local N,Ind,i
#    N=NULL
#    Ind=indets(u):
#    for i from 1 to nops(Vars) while not (Vars[i] in Ind):
#        N = N,Vars[i]
#    N = N,Vars[i]
#    return N

# def RightPommaret(u,U,Vars):
#    local N,Ind,i
#    N:=NULL
#    Ind:=indets(u)
#    for i from  nops(Vars) by -1 to 1 while not (Vars[i] in Ind):
#        N:=N,Vars[i]
#    N:=N,Vars[i]
#    return N
