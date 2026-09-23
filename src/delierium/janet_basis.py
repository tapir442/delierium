"""
Janet Basis
"""

import functools
from collections import OrderedDict, namedtuple
from collections.abc import Iterable
from operator import mul

from more_itertools import bucket, flatten
from sympy import Add, Mul, Rational, S, Symbol, cancel
from sympy.core.backend import *
from sympy.core.function import AppliedUndef

from delierium.helpers import (
    Derivative,
    eq,
    expr_eq,
    expr_is_zero,
    is_derivative,
    is_function,
    is_numeric,
    ltf,
    pairs_exclude_diagonal,
    profile_if_enabled,
    show_output,
)
from delierium.matrix_order import Context, Mgrevlex

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
        self.coeff = coeff
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
        return self.coeff * self.derivative

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
    def is_zero(self):
        return expr_is_zero(self.coeff)

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
    def __bool__(self):
        # ToDo, lets think about that again, may be too slow
        return not self.is_zero()

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
            self.comparison_vector == other.comparison_vector and expr_eq(self.coeff, other.coeff)
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
    def _coeff_diff(self, coeff, *variables):
        return coeff.diff(*variables)

    def coeff_diff(self, coeff, *variables):
        # XXX parallelize. Theere is a small performance gain (1-2 %) without it, anyway
        return sum(self._coeff_diff(_, *variables) for _ in coeff.args)

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
        if isinstance(f, Add):
            fprime = self.coeff_diff(f, *variables)
        elif hasattr(f, "diff"):
            fprime = f.diff(*variables)
        else:
            fprime = 0
        result = []
        if not is_numeric(fprime) or (is_numeric(fprime) and fprime != 0):
            d1 = _Dterm(coeff=fprime, derivative=g, context=self.context)
            result = [d1]
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
        # coefficients are rational functions of the independent
        # variables; bring them into canonical form so that a vanishing
        # coefficient is recognized (e == 0 is only a structural test)
        for _ in self.p:
            _.coeff = cancel(_.coeff)
        self.p = [_ for _ in self.p if _.coeff != 0]

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
            coeff = self.p[0].coeff
            self.p[0].coeff = Rational(1, 1)
            for _ in self.p[1:]:
                _.coeff = cancel(_.coeff / coeff)
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
            e=0, dterms=[_ for _ in new_dterms.values() if _.coeff != 0], context=self.context
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
        operands = [term]
    else:
        try:
            operands = term.as_ordered_factors()
        except AttributeError:
            # symengine
            operands = term.args_as_sympy()
    return operands


# ToDo: JanetBasis as class as this object has properties like rank, order ...


@profile_if_enabled
def reorder(S, context, ascending=False):
    return sorted(S, reverse=not ascending)


@profile_if_enabled
def reduce_by_system(e: LHDP, S: list, context: Context) -> LHDP | None:
    reducing = True
    gen = S[:]
    while reducing:
        for dp in gen:
            enew = reduce(e, dp, context)
            if enew is None:
                return None
            elif e == enew:
                reducing = False
            else:
                e = enew
                gen = [_ for _ in S if _]
                reducing = True
    return enew


# @functools.cache
@profile_if_enabled
def _order(der, context):
    # pretty sure we don't need it
    if der != 1:
        return context.order_of_derivative(der)
    return [0] * len(context.independent)


@profile_if_enabled
def _reduce_inner(e1, e2, context):
    """One reduction step of e1 modulo e2 (Schwarz, Algorithm 2.4).

    Finds the first term of e1 that is a derivative ∂^dif of e2's leading
    derivative and eliminates it by subtracting coeff * ∂^dif(e2).
    e2 must be normalized (leading coefficient 1).

    Returns:
        * e1 itself (same object) if no term of e1 is reducible by e2,
        * None if the reduction yields zero,
        * the reduced LHDP otherwise.

    Schwarz, Example 2.33, p. 48
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
    """e1 - factor * ∂^variables(e2), or None if that is zero.

    With no variables this is step S2 of Algorithm 2.4, e1 - factor * e2.

    Differentiating e2 w.r.t. H yields Y_H twice, from (-x/H) * Y_H and
    from (-x/H**2) * Y; the two contributions cancel (Schwarz, Example 5.16):

    >>> x, H = Symbol('x'), Symbol('H')
    >>> X, Y = Function('X')(H, x), Function('Y')(H, x)
    >>> ctx = Context([X, Y], [x, H])
    >>> e1 = LHDP(diff(Y, H, x) + diff(Y, x) / H, ctx)
    >>> e2 = LHDP(diff(Y, x) - x * diff(Y, H) / H - X / (2 * H * x) - x * Y / H**2, ctx)
    >>> print(reduce(e1, e2, ctx))
    D(Y(H, x), (H, 2)) + (1/(2*x**2)) * D(X(H, x), H) + (1/H) * D(Y(H, x), H) + (-1/H**2) * Y(H, x)
    """
    e2_terms = [dterm for p in e2.p for dterm in p.diff(*variables)] if variables else e2.p
    # copies, because coefficients are updated in place below.
    # Differentiating e2 may give several terms with the same derivative
    # (product rule), so they must be added up, not kept side by side
    remaining = OrderedDict((_.comparison_vector, _.copy()) for _ in e1.p)
    for dterm in e2_terms:
        product = dterm.coeff * factor
        hit = remaining.get(dterm.comparison_vector)
        if hit is None:
            remaining[dterm.comparison_vector] = _Dterm(
                coeff=-product, derivative=dterm.derivative, context=dterm.context
            )
        elif expr_eq(hit.coeff, product):
            del remaining[dterm.comparison_vector]
        else:
            hit.coeff -= product
    dterms = [_ for _ in remaining.values() if _]
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
def reduce(e1: LHDP, e2: LHDP, context: Context) -> LHDP | None:
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
def find_integrable_conditions(S, context):
    result = list(S)
    if len(result) == 1:
        return []

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

    result = []
    for ei, ej in pairs_exclude_diagonal(multiplier_collection):
        for n in ei.nonmultipliers:
            m = _multiplicative_derivative(ei, n, ej, context)
            if m is None:
                continue
            # leading coefficients are 1, so the leading derivatives cancel
            condition = _difference(ei.dp.diff(n), ej.dp.diff(*m) if m else ej.dp, context)
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
    """d1 - d2 as an LHDP, None if it vanishes; d1's terms are modified."""
    new_terms = []
    terms_from_first = {_.comparison_vector: _ for _ in d1.p}
    for s in d2.p:
        if s.comparison_vector in terms_from_first:
            terms_from_first[s.comparison_vector].coeff -= s.coeff
        else:
            new_terms.append(_Dterm(coeff=-s.coeff, derivative=s.derivative, context=context))
    dterms = [_ for _ in [*new_terms, *terms_from_first.values()] if _]
    return LHDP(e=0, context=context, dterms=dterms) if dterms else None


class JanetBasis:
    def __init__(self, S, dependent, independent, sort_order=Mgrevlex):
        """
        Parameters:
            * List of homogenous PDE's
            * List of dependent variables, i.e. the functions to searched for
            * List of variables
            * sort order, default is grevlex

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
        from delierium.helpers import _free_symbols_cache

        _free_symbols_cache.clear()
        self.context = context = Context(dependent, independent, sort_order)
        if not isinstance(S, Iterable):
            # XXX bad criterion
            self.S = [S]
        else:
            self.S = S[:]
        old = []
        self.S = reorder([LHDP(s, context, dterms=[]) for s in self.S], context, ascending=True)
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

    def show(self, rich=True, short=False, heading=""):
        """Print the Janet basis with leading derivative first."""
        if heading:
            print(heading)
        for _ in self.S:
            _.show()

    def rank(self):
        """Return the rank of the computed Janet basis."""
        return 0

    def order(self):
        """Return the order of the computed Janet basis which is the same as
        the rank
        """
        return self.rank()

    def type(self):
        '''Computes the type of the Janet Basis, i.e. the leading derivatives'''
        self._type = [_.leading_derivative() for _ in self.S]


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
