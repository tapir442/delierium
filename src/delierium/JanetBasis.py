"""
Janet Basis
"""

import functools
from collections import namedtuple
from collections.abc import Iterable
from dataclasses import dataclass
from itertools import groupby, islice, zip_longest
from operator import mul

import sage.all
from IPython.core.debugger import set_trace
from IPython.display import Math
from more_itertools import bucket, flatten, powerset
from sage.calculus.functional import diff
from sage.calculus.var import function, var
from sage.misc.latex import latex
from sage.misc.reset import reset
from sage.modules.free_module_element import vector

from delierium.exception import DelieriumNotALinearPDE
from delierium.helpers import (adiff, eq, is_derivative, is_function, latexer,
                               pairs_exclude_diagonal)
from delierium.Involution import My_Multiplier
from delierium.MatrixOrder import Context, Mgrevlex, Mgrlex, higher, sorter
from delierium.typedefs import *

Sage_Expression = sage.symbolic.expression.Expression

from functools import cache
from time import time
start = time()
from line_profiler import profile

def compute_comparison_vector(dependent, function, ctxcheck):
    iv = [0] * len(dependent)
    if function in dependent:
        iv[dependent.index(function)] = 1
    elif ctxcheck(function):
        iv[dependent.index(function.operator())] = 1
    else:
        pass
    return iv

def compute_order(derivative, independent, comp_order):
    """computes the monomial tuple from the derivative part"""
    if is_derivative(derivative):
        return comp_order(derivative)
    # XXX: Check can that be within a system of linear PDEs ?
    return [0] * len(independent)


@dataclass
class _Dterm:
    coeff: int
    derivative: int
    context: Context

    @profile
    def __post_init__ (self):
        self.order = self._compute_order()
        if is_derivative(self.derivative):
            self.function = self.derivative.operator().function()
        else:
            self.function = self.derivative
        self.comparison_vector = self._compute_comparison_vector()
        self.expression = self.coeff * self.derivative

    @profile
    def _compute_comparison_vector(self):
        iv = [0] * len(self.context._dependent)
        if self.function in self.context._dependent:
            iv[self.context._dependent.index(self.function)] = 1
        elif self.context.is_ctxfunc(self.function):
            iv[self.context._dependent.index(self.function.operator())] = 1
        else:
            pass
        return vector(self.order + iv)

    def __str__(self):
        try:
            return f"({self.coeff.expression()}) * {self.derivative}"
        except AttributeError:
            if self.coeff == 1:
                return f"{self.derivative}"
            return f"({self.coeff}) * { self.derivative}"

    def term(self):
        return self.coeff * self.derivative

    @profile
    def _compute_order(self):
        """computes the monomial tuple from the derivative part"""
        if is_derivative(self.derivative):
            return self.context.order_of_derivative(self.derivative)
        # XXX: Check can that be within a system of linear PDEs ?
        return [0] * len(self.context._independent)


    def is_coefficient(self):
        # XXX nonsense
        return self.derivative == 1

    def __nonzero__(self):
        return self.derivative != 1

    def is_monic(self):
        return self.derivative != 1 and bool(self.coeff == 1)

    @profile
    def __lt__(self, other):
        """
        >>> x,y,z = var("x y z")
        >>> f     = function("f")(x,y,z)
        >>> g     = function("g")(x,y,z)
        >>> h     = function("h")(x,y,z)
        >>> ctx   = Context ((f,g,h),(x,y,z), Mlex)
        >>> d1    = (x**2) * diff(f, x, y)
        >>> d2    = diff(f, x, y, z)
        >>> dterm1 = _Dterm(d1,ctx)
        >>> dterm2 = _Dterm(d2,ctx)
        >>> print(bool(dterm1 < dterm2))
        True
        '''
        """
        # XXX context.gt still a bad place
        return not (self is other) and not self == other and \
            self.context.gt(other.comparison_vector, self.comparison_vector)

#    @functools.cache

    @profile
    def __eq__(self, other):
        return self.derivative == other.derivative  and self.coeff == other.coeff

    def show(self, rich=True):
        if not rich:
            return str(self)
        return self.latex()

    @profile
    def latex(self):
        def _latex_derivative(deriv):
            if is_derivative(deriv):
                func = deriv.function().operator().function()._latex_()
                ps = deriv.operator().parameter_set()
                variables = deriv.operands()
                sub = ",".join(map(lambda _: variables[_]._latex_(), ps))
                return "%s_{%s}" % (func, sub)
            elif hasattr(deriv, "function"):
                return deriv.function().operator()._latex_()
            else:
                return str(deriv)

        def _latex_coeff(coeff):
            if str(coeff) in ['1', '1.0']:
                return ""
            if str(coeff) in ['-1', '-1.0']:
                return "-"
            # need to be more fine granular
            if hasattr(coeff, "expand"):
                c = coeff.expand().simplify_full()._latex_()
            else:
                c = coeff
            if hasattr(coeff, "operator") and \
                coeff.operator() != None and \
                ((hasattr(coeff.operator(), "__name__") and coeff.operator().__name__ == "add_vararg") or is_function(coeff.operator())):
                return rf"({c})"
            return c

        d = _latex_derivative(self.derivative)
        c = _latex_coeff(self.coeff)
        return f"{c} {d}"

    def sorter(self, other):
        '''sorts two derivatives d1 and d2 using the weight matrix M
        according to the sort order given in the tuple of  dependent and
        independent variables

        >>> x, y, z = var("x y z")
        >>> u = function ("u")(x,y,z)
        >>> ctxMlex = Context((u,),(x,y,z), Mlex)
        >>> ctxMgrlex = Context((u,),(x,y,z), Mgrlex)
        >>> ctxMgrevlex = Context((u,),(x,y,z), Mgrevlex)
        >>> # this is the standard example stolen from wikipedia
        >>> u0 = diff(u,x,3)
        >>> u1 = diff(u,z,2)
        >>> u2 = diff(u,x,y,y,z)
        >>> u3 = diff(u, x,x,z,z)
        >>> l1 = [u0, u1,u2,u3]
        >>> shuffle(l1)
        >>> s = sorter(l1, key=cmp_to_key(lambda item1, item2: item1.sorter(item2)))
        >>> for _ in s: print(_)
        diff(u(x, y, z), z, z)
        diff(u(x, y, z), x, y, y, z)
        diff(u(x, y, z), x, x, z, z)
        diff(u(x, y, z), x, x, x)
        >>> s = sorted(l1, key=cmp_to_key(lambda item1, item2: item1.sorter(item2)))
        >>> for _ in s: print(_)
        diff(u(x, y, z), z, z)
        diff(u(x, y, z), x, x, x)
        diff(u(x, y, z), x, y, y, z)
        diff(u(x, y, z), x, x, z, z)
        >>> s = sorted(l1, key=cmp_to_key(lambda item1, item2: item1.sorter(item2)))
        >>> for _ in s: print(_)
        diff(u(x, y, z), z, z)
        diff(u(x, y, z), x, x, x)
        diff(u(x, y, z), x, x, z, z)
        diff(u(x, y, z), x, y, y, z)
        '''
        if self ==  other:
            return 1
        if self.context.gt(self.comparison_vector, other.comparison_vector):
            return 1
        return -1



class _Differential_Polynomial:

    def __init__(self, e, context):
        self.context = context
        self.p = []
        self.multipliers = []
        self.nonmultipliers = []

        if not 0 == e:
            self._init(e.expand())
#        print("after creation of DP")
#        for _ in self.p:
#            print(f"===> {str(_)=},  {_.comparison_vector}")

    @profile
    def _analyze(self, term):
        if hasattr(term.operator(), "__name__") and term.operator().__name__ == 'mul_vararg':
            operands = term.operands()
        else:
            operands = [term]
        coeffs = []
        d = []
        for operand in operands:
            if is_function(operand):
                if self.context.is_ctxfunc(operand):
                    d.append(operand)
                else:
                    coeffs.append(operand)
            elif is_derivative(operand):
                if self.context.is_ctxfunc(operand.operator().function()):
                    d.append(operand)
                else:
                    coeffs.append(operand)
            else:
                coeffs.append(operand)
        assert (len(d) == 1)
        coeffs = functools.reduce(mul, coeffs, 1)
        return str(d[0]), d[0], coeffs

    @profile
    def _init(self, e):
        print(f"_init: {time()-start}")
        operands = []
        o = e.operator()
        if hasattr(o, "__name__") and o.__name__ == 'add_vararg':
            operands = e.operands()
        else:
            operands = [e]
        print(f"befor groupby: {time()-start}")
        r = [self._analyze(o) for o in operands]
        dterms = {}
        for _r in r:
            dterms.setdefault(_r[0], []).append((_r[1], _r[2]))
        self.p = []
        for v in dterms.values():
            # v is a list of tuples
            c = 0
            for tup in v:
                c+=tup[1]
            self.p.append(_Dterm(derivative=v[0][0], coeff=c, context=self.context))
        self.p.sort(reverse=True)
        self.normalize()
        self.order = self.p[0].order
        self.function = self.p[0].function
        print(f"_init end: {time()-start}")

    def expression(self):
        return self._expression

    def _collect_terms(self, e):
        pass

    def show_derivatives(self):
        print(self.derivatives())

    def Lterm(self):
        return self.p[0].term()

    def Lder(self):
        return self.p[0].derivative

    def Lfunc(self):
        return self.p[0].function

    def Lcoeff(self):
        return self.p[0].coeff

    def terms(self):
        for p in self.p:
            yield p.term()

    def derivatives(self):
        for p in self.p:
            yield p.derivative

    def Ldervec(self):
        # implement asap
        pass

    def coefficients(self):
        for p in self.p:
            yield p.coeff

    def normalize(self):
        if self.p and self.p[0].coeff != 1:
            c = self.p[0].coeff
            self.p = [
                _Dterm((_.coeff / c), _.derivative, self.context)
                for _ in self.p if _.coeff
            ]
        self._expression = sum(_.expression for _ in self.p)
        self.comparison_vector =  self.p[0].comparison_vector

    def __nonzero__(self):
        return len(self.p) > 0
    @profile
    def __lt__(self, other):
        for _ in zip(self.p, other.p):
            if _[0] < _[1]:
                return True
            if _[0] == _[1]:
                continue
            return False
        return False
    @profile
    def __le__(self, other):
        return self == other or self < other
    @profile
    def __eq__(self, other):
        return all(_[0].expression == _[1].expression for _ in zip(self.p, other.p))

    def show(self, rich=True):
        if not rich:
            return str(self)
        res = ""
        for _ in self.p:
            s = _.show()
            if not res:
                res = s
                continue
            if s.startswith("-1 "):
                s = s.replace("-1 ", "-")
            if s.startswith("-"):
                res += s
            else:
                res += " + " + s
        res += f"{self.multipliers}, {self.nonmultipliers}"
        return res

    def latex(self):
        return "+".join(_.latex() for _ in self.p).replace("(-", "(").replace(
            "+-", "-")

    def diff(self, *args):
        return type(self)(diff(self.expression(), *args), self.context)

    def __str__(self):
        m = [self.context._independent[_] for _ in self.multipliers]
        n = [self.context._independent[_] for _ in self.nonmultipliers]
        return " + ".join([str(_) for _ in self.p]) +\
            f", {m}, {n}"


# ToDo: Janet_Basis as class as this object has properties like rank, order ...
@profile
def Reorder(S, context, ascending=False):
    s = list(
        sorted(S))
#               key=functools.cmp_to_key(
#                   lambda item1, item2: item1.p[0].sorter(item2.p[0])),
#               reverse=not ascending))
    #    from more_itertools import pairwise
    #    print(context._dependent, context._independent)
    #    for k in pairwise(s):
    #        print(k[0].Lder(), k[1].Lder())
    #    assert all(map(lambda a: a[0].Lder() <= a[1].Lder(), pairwise(s)))
    return s

@profile
def reduceS(e: _Differential_Polynomial, S: list,
            context: Context) -> _Differential_Polynomial:
    """
    Algorithm 2.5 from Schwarz, p.48
    >>> # Example 2.34, p.48
    >>> x, y = var("x y")
    >>> z = function("z")(x,y)
    >>> ctx = Context([z], [x,y])
    >>> e1 = _Differential_Polynomial(diff(z,y) - (x**2)*diff(z, x)/(y**2) - (x-y)*z/(y**2), ctx)
    >>> f1 = _Differential_Polynomial(diff(z,x) + z/x, ctx)
    >>> f2 = _Differential_Polynomial(diff(z,y) + z/y, ctx)
    >>> print(reduceS(e1, [f1, f2], ctx))
    <BLANKLINE>
    >>> from delierium.helpers import eq
    >>> # eq.cache_clear()
    >>> # Example 2.34, reversed order of f1,f2
    >>> x, y = var("x y")
    >>> z = function("z")(x,y)
    >>> ctx = Context([z], [x,y])
    >>> e1 = _Differential_Polynomial(diff(z,y) - (x**2)*diff(z, x)/(y**2) - (x-y)*z/(y**2), ctx)
    >>> f1 = _Differential_Polynomial(diff(z,x) + z/x, ctx)
    >>> f2 = _Differential_Polynomial(diff(z,y) + z/y, ctx)
    >>> print(reduceS(e1, [f2, f1], ctx))
    <BLANKLINE>
    >>> from delierium.helpers import eq
    >>> # eq.cache_clear()
    >>> # Example 2.35
    >>> x, y = var("x y")
    >>> z = function("z")(x,y)
    >>> w = function("w")(x,y)
    >>> ctx = Context([w, z], [x,y])
    >>> f4 = _Differential_Polynomial(\
      diff(w, x,  y) \
    + diff(z, x, y) \
    + diff(w, y)/(2*y) \
    - diff(w, x)/y \
    + x*diff(z, y)/y \
    - w/(2*y**2), ctx)
    >>> f1 = _Differential_Polynomial(diff(w,y) + x*diff(z,y)/(2*y*(x**2 +y)) - w/y, ctx)
    >>> f2 = _Differential_Polynomial(diff(z,x, y) + y*diff(w,y)/x + 2*y*diff(z, x)/x, ctx)
    >>> result = reduceS(f4, [f1, f2], ctx)
    >>> # f4d from p.49
    >>> denominator = (x*(y*4*x**5 + 8*(x**3)*(y**2) -x**3 + 2*(x*y)**2 + 2*y*x**2 + 4*x*y**3 -2*x*y+2*y**3-2*y**2))
    >>> ex = diff(z, y) \
    - diff(z, x)*4*(y*2*x**2 - x +2*y**2)*(x**2+y)*y**2/denominator \
    - w * (y*2*x**2 - x +2*y**2)*(x**2+y)*y/ denominator
    >>> #print(result.expression() - ex)
    >>> #print(f"{result.expression().expand()=}")
    >>> #print(f"{ex=}")
    >>> print(bool(result.expression() == ex))
    False
    """
    reducing = True
    gen = [_ for _ in S]
    while reducing:
        for dp in gen:
            enew = reduce(e, dp, context)
            # XXX check whether we can replace "==" by 'is'
            if enew == e:
                reducing = False
            else:
                e = enew
                gen = [_ for _ in S]
                reducing = True
    return enew


#@functools.cache
@profile
def _order(der, context):
    # pretty sure we don't need it
    if der != 1:
        return order_of_derivative(der, context, len(context._independent))
    return [0] * len(context._independent)

@profile
def _reduce_inner(e1, e2, context):
#    print("reduce_inner")
    set_trace()
    changed = False
    t = [_ for _ in e1.p if _.function == e2.function]
    if not t:
        return False
    t = t[0]
    # S1 from Algorithm 2.4
    c = t.coeff
    #        print(f"{str(t)=}")
    dif = [a - b for a, b in zip(t.order, e2.order)]
    #        print(f"   {str(e1)=}")
    #        print(f"   {str(e2)=}")
    if all(map(lambda h: h == 0, dif)):
        # S2 from Algorithm 2.4
        subs=[]
        print(f"   ===> subtract, *{c}")
        for p2 in e2.p:
            hits = [_ for _ in e1.p if _.comparison_vector == p2.comparison_vector]
            assert(len(hits) in [0,1])
            if hits:
                hits[0].coeff -= c * p2.coeff
                changed = True
            else:
                subs.append(_Dterm(coeff = -p2.coeff*c,
                                   derivative =p2.derivative,
                                   context = e1.context
                                   ))
                changed = True
    elif all(map(lambda h: h >= 0, dif)):
        # S2 from Algorithm 2.4
        # toDo: as diff also accepts zerozh derivatives we may
        # unfy these two branches
        variables_to_diff = []
        for i in range(len(context._independent)):
            if dif[i] != 0:
                variables_to_diff.extend([context._independent[i]] *
                                         abs(dif[i]))
        print(f"   ===> diff, *{c}, {variables_to_diff}")
        subs=[]
        for p2 in e2.p:
            f = p2.coeff
            gstrich = diff(p2.derivative, *variables_to_diff)
            fstrich = diff(p2.coeff, *variables_to_diff)
            g = p2.derivative
            order = compute_order(gstrich, e1.context._independent, e1.context.order_of_derivative)
            cmpvec = compute_comparison_vector(e1.context._dependent, p2.function, p2.context.is_ctxfunc)
            hits = [_ for _ in e1.p if _.comparison_vector == p2.comparison_vector]
            assert(len(hits) in [0,1])
            if hits:
                hits[0].coeff -= c * p2.coeff
                changed = True
            else:
                subs.append(_Dterm(coeff = -f*c,
                                   derivative = gstrich,
                                   context = p2.context
                                   ))
                changed = True
            order = compute_order(fstrich, e1.context._independent, e1.context.order_of_derivative)
            cmpvec = list(p2.comparison_vector)
            hits = [_ for _ in e1.p if _.comparison_vector == tuple(cmpvec)]
            assert(len(hits) in [0,1])
            if hits:
                hits[0].coeff -= c*fstrich
                changed = True
            else:
                subs.append(_Dterm(coeff = -c*fstrich,
                                   derivative = g,
                                   context = e1.context
                                   )
                            )
                changed = True


    if changed:
        e1.p.extend(subs)
        e1.p = [_ for _ in e1.p if _.coeff]
        e1.p.sort(reverse=True)
        e1.normalize()
        e1.show(rich=True)

    return changed


def reduce(e1: _Differential_Polynomial, e2: _Differential_Polynomial,
           context: Context) -> _Differential_Polynomial:
    """
    Algorithm 2.4 from Schwarz, p.48
    >>> # Example 2.33(f1), p.48
    >>> x, y = var("x y")
    >>> z = function("z")(x,y)
    >>> ctx = Context([z], [x,y])
    >>> e1 = _Differential_Polynomial(diff(z,y) - (x**2)*diff(z, x)/(y**2) - (x-y)*z/(y**2), ctx)
    >>> f1 = _Differential_Polynomial(diff(z,x) + z/x, ctx)
    >>> print(_reduce_inner(e1, f1, ctx))
    diff(z(x, y), y) + (1/y) * z(x, y), [], []
    >>> from delierium.helpers import eq
    >>> # eq.cache_clear()
    >>> # Example 2.33(f2), p.48
    >>> x, y = var("x y")
    >>> z = function("z")(x,y)
    >>> ctx = Context([z], [x,y])
    >>> e1 = _Differential_Polynomial(diff(z,y) - (x**2)*diff(z, x)/(y**2) - (x-y)*z/(y**2), ctx)
    >>> f2 = _Differential_Polynomial(diff(z,y) + z/y, ctx)
    >>> print(_reduce_inner(e1, f2, ctx))
    diff(z(x, y), x) + (1/x) * z(x, y), [], []
    """
    while _reduce_inner(e1, e2, context):
        pass
    return e1

@profile
def Autoreduce(S, context):
    """
    Algorithm 2.6, p.49
    >>> x,y = var("x y")
    >>> z = function("z")(x, y)
    >>> w = function("w")(x, y)
    >>> ctx = Context([w, z], [x,y])
    >>> f1 = _Differential_Polynomial(diff(w,y) + x*diff(z,y)/(2*y*(x**2 +y)) - w/y, ctx)
    >>> f2 = _Differential_Polynomial(diff(z,x, y) + y*diff(w,y)/x + 2*y*diff(z, x)/x, ctx)
    >>> f3 = _Differential_Polynomial(diff(w, x, y) - 2*x*diff(z,x,x)/y - x*diff(w,x)/(y**2), ctx)
    >>> f4 = _Differential_Polynomial(\
    diff(w, x,  y) \
    + diff(z, x, y) \
    + diff(w, y)/(2*y) \
    - diff(w, x)/y \
    + x*diff(z, y)/y \
    - w/(2*y**2), ctx)
    >>> f5 = _Differential_Polynomial(diff(w,y,y)+diff(z,x,y)-diff(w,y)/y+w/(y**2), ctx)
    >>> k = Autoreduce([f1,f2,f3,f4,f5], ctx)
    >>> # Attention! The text doesn't show the minus sign in the third equation
    >>> for _ in k: print(_)
    diff(z(x, y), y), [], []
    diff(z(x, y), x) + (1/2/y) * w(x, y), [], []
    diff(w(x, y), y) + (-1/y) * w(x, y), [], []
    diff(w(x, y), x), [], []
    """
    dps = list(S)
    i = 0
    _p, r = dps[:i + 1], dps[i + 1:]
    c = 0
    while r:
        newdps = []
        have_reduced = False
        for _r in r:
            rnew = reduceS(_r, _p, context)
            have_reduced = have_reduced or rnew != _r
            newdps.append(rnew)
        dps = Reorder(_p + [_ for _ in newdps if _ not in _p],
                      context,
                      ascending=True)
        print("A"*99, c)
#        for _ in dps:
#            display(Math(_.latex()))
        if not have_reduced:
            i += 1
        else:
            i = 0
            c += 1
        _p, r = dps[:i + 1], dps[i + 1:]
    return dps


def vec_degree(v, m):
    return m[v]


def vec_multipliers(m, M, Vars):
    """multipliers and nonmultipliers for differential vectors aka tuples

    m   : a tuple representing a differential vector
    M   : the complete set of differential vectors
    Vars: a tuple representing the order of indizes in m
          Examples:
              (0,1,2) means first index in m represents the highest variable
              (2,1,0) means last index in m represents the highest variable

    ......................................................
    The doctest example is from Schwarz, Example C.1, p. 384
    This example is in on variables x1,x2,x3, with x3 the highest rated variable.
    So we have to specify (2,1,0) to represent this

    >>> #M = [(2,2,3), (3,0,3), (3,1,1), (0,1,1)]
    >>> #r = vec_multipliers (M[0],M, (2,1,0))
    >>> #print (M[0], r[0], r[1])
    #(2, 2, 3) [2, 1, 0] []
    >>> #r = vec_multipliers (M[1],M, (2,1,0))
    >>> #print (M[1], r[0], r[1])
    #(3, 0, 3) [2, 0] [1]
    >>> #r = vec_multipliers (M[2],M, (2,1,0))
    >>> #print (M[2], r[0], r[1])
    #(3, 1, 1) [1, 0] [2]
    >>> #r = vec_multipliers (M[3],M, (2,1,0))
    >>> #print (M[3], r[0], r[1])
    #(0, 1, 1) [1] [0, 2]
    >>> #N=[[0,2], [2,0], [1,1]]
    >>> #r =vec_multipliers(N[0], N,  (0,1))
    >>> #print(r)
    #([1], [0])
    >>> #r =vec_multipliers(N[1], N,  (0,1))
    >>> #print(r)
    #([0, 1], [])
    >>> #r =vec_multipliers(N[2], N,  (0,1))
    >>> #print(r)
    #([1], [0])
    >>> #r =vec_multipliers(N[0], N,  (1,0))
    >>> #print(r)
    #([1, 0], [])
    >>> #r =vec_multipliers(N[1], N,  (1,0))
    >>> #print(r)
    #([0], [1])
    >>> #r =vec_multipliers(N[2], N,  (1,0))
    >>> #print(r)
    #([0], [1])
    >>> # next example form Gertd/Blinkov: Janet-like monomial divisiom, Table1
    >>> # x1 -> Index 2
    >>> # x2 -> Index 1 (this is easy)
    >>> # x3 -> Index 0
    >>> #U = [[0,0,5], [1,2,2],[2,0,2], [1,4,0],[2,1,0],[5,0,0]]
    >>> #vec_multipliers(U[0], U, (2,1,0))
    #([2, 1, 0], [])
    >>> #vec_multipliers(U[1], U, (2,1,0))
    #([1, 0], [2])
    >>> #vec_multipliers(U[2], U, (2,1,0))
    #([0], [1, 2])
    >>> #vec_multipliers(U[3], U, (2,1,0))
    #([1, 0], [2])
    >>> #vec_multipliers(U[4], U, (2,1,0))
    #([0], [1, 2])
    >>> #vec_multipliers(U[5], U, (2,1,0))
    #([0], [1, 2])
    >>> #dp1 = (0,0,0,1,1)
    >>> #dp2 = (0,0,1,0,1)
    >>> #dp3 = (0,1,0,0,1)
    >>> #dp4 = (0,0,0,2,0)
    >>> #dp5 = (0,0,1,1,0)
    >>> #dp6 = (0,0,2,0,0)
    >>> #l = [dp1, dp2, dp3, dp4, dp5, dp6]
    >>> #vec_multipliers(dp1, l, (4,3,2,1,0))
    #<BLANKLINE>
    """
    d = max((vec_degree(v, u) for u in M for v in Vars), default=0)
    mult = []
    if vec_degree(Vars[0], m) == d:
        mult.append(Vars[0])
    for j in range(1, len(Vars)):
        v = Vars[j]
        dd = list(map(lambda x: vec_degree(x, m), Vars[:j]))
        V = []
        for _u in M:
            if [vec_degree(_v, _u) for _v in Vars[:j]] == dd:
                V.append(_u)
        if vec_degree(v, m) == max((vec_degree(v, _u) for _u in V), default=0):
            mult.append(v)
    return mult, list(sorted(set(Vars) - set(mult)))


def map_old_to_new(v, context):
    return context._independent[len(context._independent) - v - 1]


def complete(S, context):
    """
    >>> # Example 3.2.6 from Iohara/Malbos, p.24
    >>> print("D"*200)
    >>> x1, x2, x3, x4, x5 = var("x1 x2 x3 x4 x5")
    >>> f = function("f")(x1, x2, x3, x4, x5)
    >>> ctx = Context([f], [x5,x4,x3,x2,x1])
    >>> dp1 = _Differential_Polynomial(diff(f, x5, x4), ctx)
    >>> dp2 = _Differential_Polynomial(diff(f, x5, x3), ctx)
    >>> dp3 = _Differential_Polynomial(diff(f, x5, x2), ctx)
    >>> dp4 = _Differential_Polynomial(diff(f, x4, x4), ctx)
    >>> dp5 = _Differential_Polynomial(diff(f, x3, x4), ctx)
    >>> dp6 = _Differential_Polynomial(diff(f, x3, x3), ctx)
    >>> complete([dp1, dp2,dp3,dp4,dp5,dp6], ctx)

    """

    result = list(S)
    vars = list(range(len(context._independent)))

    while 1:
        monomials = [(_, _.order) for _ in result]
        multiplier_collection = []
        new_multipliers = My_Multiplier(
            [tuple(reversed(_[1])) for _ in monomials]).mults
        for monom, dp in zip(monomials, result):
            # S1
            dp.multipliers = new_multipliers[tuple(reversed(monom[1]))]
            dp.nonmultipliers = list(set(vars) - set(dp.multipliers))
            multiplier_collection.append((tuple(reversed(monom[1])), dp))

        m0 = []
        for monom, dp in multiplier_collection:
            if not dp.nonmultipliers:
                m0.append((monom, None, dp))
            else:
                for n in dp.nonmultipliers:
                    _m0 = list(monom)
                    _m0[n] += 1
                    m0.append((_m0, n, dp))
        to_remove = []

        for _m0 in m0:
            # S3: check whether in class of any of the monomials
            for monomial, dp in multiplier_collection:
                if all(_m0[0][x] >= monomial[x] for x in dp.multipliers) and \
                   all(_m0[0][x] == monomial[x] for x in dp.nonmultipliers):
                    # this is in _m0's class
                    to_remove.append(_m0)
        for _to in to_remove:
            try:
                m0.remove(_to)
            except:
                pass
        if not m0:
            return result
        else:
            for _m0 in m0:
                dp = _Differential_Polynomial(
                    _m0[2].diff(map_old_to_new(_m0[1], context)).expression(),
                    context)
                if dp not in result:
                    result.append(dp)
        result = Reorder(result, context, ascending=False)


def CompleteSystem(S, context):
    """
    Algorithm C1, p. 385

    >>> tvars=var("x y z")
    >>> w = function("w")(*tvars)
    >>> # these DPs are constructed from C1, pp 384
    >>> h1=diff(w, x,x,x, y,y,z,z)
    >>> h2=diff(w, x,x,x,     z,z,z)
    >>> h3=diff(w, x,     y,  z,z,z)
    >>> h4=diff(w, x,     y)
    >>> ctx=Context((w,),(x,y,z), Mgrlex)
    >>> dps=[_Differential_Polynomial(_, ctx) for _ in [h1,h2,h3,h4]]
    >>> cs = CompleteSystem(dps, ctx)
    >>> # things are sorted up
    >>> for _ in cs: print(_)
    diff(w(x, y, z), x, y)
    diff(w(x, y, z), x, y, z)
    diff(w(x, y, z), x, x, y)
    diff(w(x, y, z), x, y, z, z)
    diff(w(x, y, z), x, x, y, z)
    diff(w(x, y, z), x, x, x, y)
    diff(w(x, y, z), x, y, z, z, z)
    diff(w(x, y, z), x, x, y, z, z)
    diff(w(x, y, z), x, x, x, y, z)
    diff(w(x, y, z), x, x, x, y, y)
    diff(w(x, y, z), x, x, y, z, z, z)
    diff(w(x, y, z), x, x, x, z, z, z)
    diff(w(x, y, z), x, x, x, y, z, z)
    diff(w(x, y, z), x, x, x, y, y, z)
    diff(w(x, y, z), x, x, x, y, z, z, z)
    diff(w(x, y, z), x, x, x, y, y, z, z)
    >>> # example from Schwarz, pp 54
    >>> w = function("w")(x,y)
    >>> z = function("z")(x,y)
    >>> g1 = diff(z,y,y) + diff(z, y)/(2*y)
    >>> g5 = diff(z,x,x,x) + diff(w,y,y)*8*y**2 + diff(w,x,x)/y - diff(z,x,y)*4*y**2 - diff(z,x)*32*y-16*w
    >>> g6 = diff(z,x,x,y) - diff(z,y,y)*4*y**2 - diff(z,y)*8*y
    >>> ctx = Context((w,z),(x,y), Mgrlex)
    >>> dps=[_Differential_Polynomial(_, ctx) for _ in [g1,g5,g6]]
    >>> cs = CompleteSystem(dps, ctx)
    >>> for _ in cs: print(_)
    diff(z(x, y), y, y) + (1/2/y) * diff(z(x, y), y)
    diff(z(x, y), x, y, y) + (1/2/y) * diff(z(x, y), x, y)
    diff(z(x, y), x, x, y) + (-4*y^2) * diff(z(x, y), y, y) + (-8*y) * diff(z(x, y), y)
    diff(z(x, y), x, x, x) + (1/y) * diff(w(x, y), x, x) + (8*y^2) * diff(w(x, y), y, y) + (-4*y^2) * diff(z(x, y), x, y) + (-32*y) * diff(z(x, y), x) + (-16) * w(x, y)
    """
    s = bucket(S, key=lambda d: d.Lfunc())
    res = flatten([complete(s[k], context) for k in s])
    return Reorder(res, context, ascending=True)


def split_by_function(S, context):
    s = bucket(S, key=lambda d: d.Lfunc())
    return flatten([FindIntegrableConditions(s[k], context) for k in s])


dp_with_mults = namedtuple("dp_with_mults", ["dp", "mult", "nonmult"])


def FindIntegrableConditions(S, context):
    """

    Example 2.37, p.54, part 1

    >>> x, y = var("x  y")
    >>> w = function("w")(x,y)
    >>> z = function("z")(x,y)
    >>> ctx = Context([w, z], [x,y])
    >>> dp = _Differential_Polynomial
    >>> g1 = dp(diff(z, y, y) + diff(z,y)/(2*y),ctx)
    >>> g2 = dp(diff(w, x, x) + 4*(y**2)*diff(w,y) - 8*(y**2)*diff(z, x) - 8*y*w, ctx)
    >>> g3 = dp(diff(w, x, y) - diff(z, x, x)/2 - diff(w,x) /(2*y) - 6*y**2 * diff(z, y), ctx)
    >>> g4 = dp(diff(w, y ,y) - 2* diff(z, x, y) - diff(w, y)/(2*y) + w / (2*y**2), ctx)
    >>> i1 = FindIntegrableConditions([g1], ctx)
    >>> print(i1)
    []
    >>> i2 = FindIntegrableConditions([g2, g3, g4], ctx)
    >>> print(i2)
    [-4*y^2*diff(w(x, y), y, y) + 2*y^2*diff(z(x, y), x, y) + 16*y*diff(z(x, y), x) - 1/2*diff(w(x, y), x, x)/y + 8*w(x, y) - 1/2*diff(z(x, y), x, x, x), 6*y^2*diff(z(x, y), y, y) + 12*y*diff(z(x, y), y) - 3/2*diff(z(x, y), x, x, y)]
    >>> from delierium.helpers import eq
    >>> # eq.cache_clear()

    Example 2.37, p.54, part 2

    >>> x, y = var("x  y")
    >>> w = function("w")(x,y)
    >>> z = function("z")(x,y)
    >>> ctx = Context([w, z], [x,y])
    >>> dp = _Differential_Polynomial
    >>> g1 = dp(diff(z, y, y) + diff(z,y)/(2*y),ctx)
    >>> g5 = dp(12*(y**2)*diff(z,x,y)-24*y*diff(z, x)- 12*w + diff(z, x, x, x), ctx)
    >>> g6 = dp(diff(z, x, x, y) - 6*y*diff(z,y), ctx)
    >>> g7 = dp(diff(z,x,y,y) + diff(z,x,y)/(2*y), ctx)
    >>> i2 = FindIntegrableConditions([g1, g5, g6, g7], ctx)
    >>> i2 = [_Differential_Polynomial(_, ctx) for _ in i2]
    >>> for _ in i2: print(_)
    diff(z(x, y), x, y, y) + (1/2/y) * diff(z(x, y), x, y) + (-1/y^2) * diff(w(x, y), y) + (-2/y^2) * diff(z(x, y), x)
    diff(z(x, y), x, x, y) + (12*y^2) * diff(z(x, y), y, y) + (12*y) * diff(z(x, y), y)
    """
    result = list(S)
    vars = list(range(len(context._independent)))
    monomials = [(_, _.order) for _ in result]

    # multiplier-collection is our M
    multiplier_collection = []
    new_multipliers = My_Multiplier([tuple(reversed(_[1])) for _ in monomials
                                    ]).mults
    for monom, dp in zip(monomials, result):
        # S1
        _multipliers = new_multipliers[tuple(reversed(monom[1]))]
        _nonmultipliers = list(set(vars) - set(_multipliers))
        multiplier_collection.append(
            dp_with_mults(
                dp, [map_old_to_new(_, context) for _ in _multipliers],
                [map_old_to_new(_, context) for _ in _nonmultipliers]))
    result = []
    for e1, e2 in pairs_exclude_diagonal(multiplier_collection):
        for n in e1.nonmult:
            for m in islice(powerset(e2.mult), 1, None):
                if eq(adiff(e1.dp.Lder(), context, n),
                      adiff(e2.dp.Lder(), context, *m)):
                    # integrability condition
                    # don't need leading coefficients because in DPs
                    # it is always 1
                    c = adiff(e1.dp.expression(), context, n) - \
                        adiff(e2.dp.expression(), context, *m)
                    if c != 0:
                        print(f"adding {c=} to result")
                        result.append(c)
    return result


class Janet_Basis:

    def __init__(self, S, dependent, independent, sort_order=Mgrevlex):
        """
        Parameters:
            * List of homogenous PDE's
            * List of dependent variables, i.e. the functions to searched for
            * List of variables
            * sort order, default is grevlex

        >>> vars = var ("x y")
        >>> z = function("z")(*vars)
        >>> w = function("w")(*vars)
        >>> f1 = diff(w, y) + x*diff(z,y)/(2*y*(x**2+y)) - w/y
        >>> f2 = diff(z,x,y) + y*diff(w,y)/x + 2*y*diff(z, x)/x
        >>> f3 = diff(w, x,y) - 2*x*diff(z, x,2)/y - x*diff(w,x)/y**2
        >>> f4 = diff(w, x,y) + diff(z, x,y) + diff(w, y)/(2*y) - diff(w,x)/y + x* diff(z, y)/y - w/(2*y**2)
        >>> f5 = diff(w,y,y) + diff(z,x,y) - diff(w, y)/y + w/(y**2)
        >>> system_2_24 = [f1,f2,f3,f4,f5]
        >>> checkS=Janet_Basis(system_2_24, (w,z), vars)
        >>> checkS.show()
        diff(z(x, y), y), [y, x], []
        diff(z(x, y), x) + (1/2/y) * w(x, y), [y, x], []
        diff(w(x, y), y) + (-1/y) * w(x, y), [x ,y], []
        diff(w(x, y), x), [x, y], []
        >>> vars = var ("x y")
        >>> z = function("z")(*vars)
        >>> w = function("w")(*vars)
        >>> g1 = diff(z, y,y) + diff(z,y)/(2*y)
        >>> g2 = diff(w,x,x) + 4*diff(w,y)*y**2 - 8*(y**2) * diff(z,x) - 8*w*y
        >>> g3 = diff(w,x,y) - diff(z,x,x)/2 - diff(w,x)/(2*y) - 6* (y**2) * diff(z,y)
        >>> g4 = diff(w,y,y) - 2*diff(z,x,y) - diff(w,y)/(2*y) + w/(2*y**2)
        >>> system_2_25 = [g2,g3,g4,g1]
        >>> checkS=Janet_Basis(system_2_25, (w,z), vars)
        >>> checkS.show()
        diff(z(x, y), y)
        diff(z(x, y), x) + (1/2/y) * w(x, y)
        diff(w(x, y), y) + (-1/y) * w(x, y)
        diff(w(x, y), x)
        >>> vars = var ("x y")
        >>> z = function("z")(*vars)
        >>> w = function("w")(*vars)
        >>> f1 = diff(w, y) + x*diff(z,y)/(2*y*(x**2+y)) - w/y
        >>> f2 = diff(z,x,y) + y*diff(w,y)/x + 2*y*diff(z, x)/x
        >>> f3 = diff(w, x,y) - 2*x*diff(z, x,2)/y - x*diff(w,x)/y**2
        >>> f4 = diff(w, x,y) + diff(z, x,y) + diff(w, y)/(2*y) - diff(w,x)/y + x* diff(z, y)/y - w/(2*y**2)
        >>> f5 = diff(w,y,y) + diff(z,x,y) - diff(w, y)/y + w/(y**2)
        >>> system_2_24 = [f1,f2,f3,f4,f5]
        >>> checkS=Janet_Basis(system_2_24, (w,z), vars, Mgrlex)
        >>> checkS.show()
        diff(z(x, y), y)
        diff(z(x, y), x) + (1/2/y) * w(x, y)
        diff(w(x, y), y) + (-1/y) * w(x, y)
        diff(w(x, y), x)
        >>> vars = var ("x y")
        >>> z = function("z")(*vars)
        >>> w = function("w")(*vars)
        >>> g1 = diff(z, y,y) + diff(z,y)/(2*y)
        >>> g2 = diff(w,x,x) + 4*diff(w,y)*y**2 - 8*(y**2) * diff(z,x) - 8*w*y
        >>> g3 = diff(w,x,y) - diff(z,x,x)/2 - diff(w,x)/(2*y) - 6* (y**2) * diff(z,y)
        >>> g4 = diff(w,y,y) - 2*diff(z,x,y) - diff(w,y)/(2*y) + w/(2*y**2)
        >>> system_2_25 = [g2,g3,g4,g1]
        >>> checkS=Janet_Basis(system_2_25, (w,z), vars, Mgrlex)
        >>> checkS.show()
        diff(w(x, y), x), [y, x], []
        diff(w(x, y), y) + (-1/y) * w(x, y), [x, y], []
        diff(z(x, y), x) + (1/2/y) * w(x, y), [y, x], []
        diff(z(x, y), y), [y, x], []
        """
        #        eq.cache_clear()
        context = Context(dependent, independent, sort_order)
        if not isinstance(S, Iterable):
            # bad criterion
            self.S = [S]
        else:
            self.S = S[:]
        old = []
        self.S = Reorder([_Differential_Polynomial(s, context) for s in self.S],
                         context,
                         ascending=True)
        loop = 0
        while 1:
            # XXX try 'is'instead of '=='
            if old == self.S:
                # no change since last run
                return
            old = self.S[:]
            loop += 1
            print("*"*88)
            print(f"This is where we start, {loop=}")
#            self.show(rich=True)
            self.S = Autoreduce(self.S, context)
            print("after autoreduce")
            self.show(rich=True)
            return
            self.S = CompleteSystem(self.S, context)
            print("after complete system")
#            self.show(rich=True)
            self.conditions = list(split_by_function(self.S, context))
            #            print("This are the conditions")
            #            print(f"{self.conditions}")
            if not self.conditions:
                self.S = Reorder(self.S, context, ascending=True)
                return

            reduced = [
                reduceS(_Differential_Polynomial(_m, context), self.S, context)
                for _m in self.conditions
            ]
            self.S += [
                _ for _ in reduced if not (_ in self.S or eq(_.expression(), 0))
            ]
            self.S = Reorder(self.S, context, ascending=True)
 #           self.show(rich=True)

    def show(self, rich=False):
        """Print the Janet basis with leading derivative first."""
        for _ in self.S:
            if rich:
                display(Math(_.latex()))
            else:
                print(_)

    def rank(self):
        """Return the rank of the computed Janet basis."""
        return 0

    def order(self):
        """Return the order of the computed Janet basis which is the same as
        the rank
        """
        return self.rank()

    def type(self):
        '''Computes the type of the Janet Basis, i.e. the leading derivatives
        '''
        self._type = [_.Lder() for _ in self.S]

if __name__ == "__main__":
    import doctest
    doctest.testmod()
# -

# https://amirhashemi.iut.ac.ir/sites/amirhashemi.iut.ac.ir/files//file_basepage/invbasis.txt#overlay-context=contents

########### Pommaret Division #############
#def LeftPommaret(u,U,Vars):
#    local N,Ind,i
#    N=NULL
#    Ind=indets(u):
#    for i from 1 to nops(Vars) while not (Vars[i] in Ind):
#        N = N,Vars[i]
#    N = N,Vars[i]
#    return N

#def RightPommaret(u,U,Vars):
#    local N,Ind,i
#    N:=NULL
#    Ind:=indets(u)
#    for i from  nops(Vars) by -1 to 1 while not (Vars[i] in Ind):
#        N:=N,Vars[i]
#    N:=N,Vars[i]
#    return N
