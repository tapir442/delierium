"""
Janet Basis
"""

import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.modules.free_module_element import vector
from sage.calculus.functional import diff
try :
    from delierium.helpers import (is_derivative, is_function, eq,
                                   order_of_derivative, adiff, latexer)
    from delierium.MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
    from delierium.Involution import My_Multiplier
except ModuleNotFoundError:
    from helpers import (is_derivative, is_function, eq,
                         order_of_derivative, adiff, latexer)
    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
    from Involution import My_Multiplier

import functools
from operator import mul
from collections.abc import Iterable
from more_itertools import powerset, bucket, flatten
from itertools import product, islice

from sage.misc.latex import latex
from sage.misc.html import html
import re
from sage.repl.rich_output.pretty_print import pretty_print

from IPython.core.debugger import set_trace
from IPython.display import Math

#@functools.cache
def func(e):
    try:
        return e.operator().function()
    except AttributeError:
        return e.operator()

class _Dterm:
    def __init__(self, e, context=None):
        r'''differential term

        >>> x,y,z = var("x y z")
        >>> f     = function("f")(x,y,z)
        >>> g     = function("g")(x,y,z)
        >>> h     = function("h")(x,y,z)
        >>> ctx   = Context ((f,g),(x,y,z))
        >>> d     = (x**2) * diff(f, x, y)
        >>> dterm = _Dterm(d,ctx)
        >>> print (dterm)
        (x^2) * diff(f(x, y, z), x, y)
        '''
        self._coeff, self._d = 1, 1
        self._context        = context
        self._has_minus      = False
        if is_derivative(e) or is_function(e):
            self._d     = e
        else:
            r = []
            for o in e.operands():
                if is_derivative(o) or is_function(o):
                    self._d = o
                else:
                    if o == -1:
                        self._has_minus = True
                    self._coeff *= o
                    r.append(o)
        self.order, self.function = self._compute_order()
        self.comparison_vector = self._compute_comparison_vector()
        self.expression = self._coeff * self._d

    def _compute_comparison_vector(self):
        iv = [0]*len(self._context._dependent)
        if self.function in self._context._dependent:
            iv[self._context._dependent.index(self.function)] += 1
        return vector(self.order + iv)


    def __str__(self):
        try:
            return f"({self._coeff.expression()}) * {self._d}"
        except AttributeError:
            if eq (self._coeff, 1):
                return f"{self._d}"
            return f"({self._coeff}) * { self._d}"

    def term(self):
        return self._coeff * self._d

    def _compute_order(self):
        """computes the monomial tuple from the derivative part"""
        if is_derivative(self._d):
            return order_of_derivative(self._d, len(self._context._independent))
        # XXX: Check can that be within a system of linead PDEs ?
        return [0] * len(self._context._independent), None

    def is_coefficient(self):
        # XXX nonsense
        return self._d == 1

    def __nonzero__(self):
        return self._d != 1

    def derivative(self):
        return self._d

    def is_monic(self):
        return self._d != 1 and bool(self._coeff == 1)

    def __lt__(self, other):
        """
        >>> x,y,z = var("x y z")
        >>> f     = function("f")(x,y,z)
        >>> g     = function("g")(x,y,z)
        >>> h     = function("h")(x,y,z)
        >>> ctx   = Context ((f,g,h),(x,y,z))
        >>> d1    = (x**2) * diff(f, x, y)
        >>> d2    = diff(f, x, y, z)
        >>> dterm1 = _Dterm(d1,ctx)
        >>> dterm2 = _Dterm(d2,ctx)
        >>> print(bool(dterm1 < dterm2))
        True
        '''
        """
        # XXX context.gt still a bad place
        return not eq(self, other) and \
            self._context.gt(self.comparison_vector, other.comparison_vector)

#    @functools.cache
    def __eq__(self, other):
        return eq(self._d, other._d) and eq(self._coeff, other._coeff)

    def show(self, rich=True):
        if not rich:
            return str(self)

        dlatex = latex(self._coeff)
        denominator_pattern = re.compile(r"(-)?\\frac\{.*}{(.* )?(?P<nomfunc>\w+)?\\left\((?P<vars>[\w ,]*)\\right\).*")
        while match := denominator_pattern.match(dlatex):
            to_replace = rf"{match.groupdict()['nomfunc']}\left({match.groupdict()['vars']}\right)"
            dlatex = dlatex.replace (to_replace, match.groupdict()['nomfunc'])
        if self._coeff != 1:
            return " ".join ((dlatex, latexer(self._d)))
        return latexer(self._d)

    def __hash__(self):
        return hash(self._expression)

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
        if eq(self, other):
            return 1
        if self._context.gt(self.comparison_vector, other.comparison_vector):
            return 1
        return -1


class _Differential_Polynomial:
    def __init__(self, e, context):
        self._context = context
        self._p = []
        self.multipliers    = []
        self.nonmultipliers = []

        if not eq(0, e):
            self._init(e.expand())
    def _init(self, e):
        if is_derivative(e) or is_function(e):
            self._p.append(_Dterm(e, self._context))
        elif e.operator().__name__ == 'mul_vararg':
            self._p.append(_Dterm(e, self._context))
        else:
            for s in e.operands():
                coeff, d = [], []
                if is_derivative(s) or is_function(s):
                    d.append(s)
                else:
                    for item in s.operands():
                        (d if (is_derivative(item) or self.ctxfunc(item)) else coeff).append(item)
                coeff = functools.reduce(mul, coeff, 1)
                found = False
                if d:
                    for _p in self._p:
                        if eq(_p._d, d[0]):
                            _p._coeff += coeff
                            found = True
                            break
                if not found:
                    if d:
                        self._p.append(_Dterm(coeff * d[0], self._context))
                    else:
                        self._p.append(_Dterm(coeff, self._context))

        self._p.sort(key=functools.cmp_to_key(
            lambda item1, item2: item1.sorter(item2)), reverse=True
        )
        self.normalize()
        self.order = self._p[0].order
        self.function =  self._p[0].function

    def expression(self):
        return self._expression

    def ctxfunc(self, e):
        return func(e) and func(e) in self._context._dependent

    def _collect_terms(self, e):
        pass

    def show_derivatives(self):
        print(self.derivatives())


    def Lterm(self):
        return self._p[0].term()

    def Lder(self):
        return self._p[0]._d

    def Lfunc(self):
        if is_function(self._p[0]._d):
            return self._p[0]._d.operator()
        return self._p[0]._d.operator().function()

    def Lcoeff(self):
        return self._p[0]._coeff

    def terms(self):
        for p in self._p:
            yield p.term()

    def derivatives(self):
        for p in self._p:
            yield p._d

    def Ldervec(self):
        # implement asap
        pass

    def coefficients(self):
        for p in self._p:
            yield p._coeff

    def normalize(self):
        if self._p and self._p[0]._coeff != 1:
            c = self._p[0]._coeff
            self._p = [_Dterm((_._coeff / c).simplify() * _._d, self._context)
                       for _ in self._p]
        self._expression = sum(_.expression() for _ in self._p)

    def __nonzero__(self):
        return len(self._p) > 0

    def __lt__(self, other):
        return self._p[0] < other._p[0]

    def __le__(self, other):
        return self == other or self < other

    def __eq__(self, other):
        if id(self) == id(other):
            return True
        return all(eq(_[0]._d, _[1]._d) for _ in zip(self._p, other._p))

    def show(self, rich=True):
        if not rich:
            return str(self)
        res = ""
        for _ in self._p:
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

    def diff(self, *args):
        return type(self)(diff(self.expression(), *args), self._context)

    def __str__(self):
        m = [self._context._independent[_] for _ in self.multipliers]
        n = [self._context._independent[_] for _ in self.nonmultipliers]
        return " + ".join([str(_) for _ in self._p]) +\
            f", {m}, {n}"

    def __hash__(self):
        return hash(self.expression())


# ToDo: Janet_Basis as class as this object has properties like rank, order ...
def Reorder(S, context, ascending=False):
    s = list(sorted(S, key=functools.cmp_to_key(
        lambda item1, item2:
            item1._p[0].sorter(item2._p[0])),
        reverse=not ascending))
#    from more_itertools import pairwise
#    print(context._dependent, context._independent)
#    for k in pairwise(s):
#        print(k[0].Lder(), k[1].Lder())
#    assert all(map(lambda a: a[0].Lder() <= a[1].Lder(), pairwise(s)))
    return s



def reduceS(e: _Differential_Polynomial,
            S: list, context: Context) -> _Differential_Polynomial:
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
def _order(der, context):
    # pretty sure we don't need it
    if der != 1:
        return order_of_derivative(der, len(context._independent))
    return [0]*len(context._independent)


def _reduce_inner(e1, e2, context):
    e2_order = e2.order
    lf = e2.function
    for t in (_ for _ in e1._p if eq(_.function, lf)):
        # S1 from Algorithm 2.4
        c = t._coeff
        e1_order = e1.order
        dif = [a-b for a, b in zip(e1_order, e2_order)]
        if all(map(lambda h: h == 0, dif)):
            # S2 from Algorithm 2.4
            return _Differential_Polynomial(
                e1.expression() - e2.expression() * c, context)
        if all(map(lambda h: h >= 0, dif)):
            # S2 from Algorithm 2.4
            # toDo: as diff also accepts zerozh derivatives we may
            # unfy these two branches
            variables_to_diff = []
            for i in range(len(context._independent)):
                if dif[i] != 0:
                    variables_to_diff.extend([context._independent[i]]*abs(dif[i]))
            return _Differential_Polynomial(
                e1.expression() - c*diff(e2.expression(), *variables_to_diff),
                context)
    return e1


def reduce(e1: _Differential_Polynomial,
           e2: _Differential_Polynomial,
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
    while not bool((_e1 := _reduce_inner(e1, e2, context)) == e1):
        e1 = _e1
    return _e1

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
    _p, r = dps[:i+1], dps[i+1:]
    while r:
        newdps = []
        have_reduced = False
        for _r in r:
            rnew = reduceS(_r, _p, context)
            have_reduced = have_reduced or rnew != _r
            newdps.append(rnew)
        dps = Reorder(_p + [_ for _ in newdps if _ not in _p], context, ascending=True)
        if not have_reduced:
            i += 1
        else:
            i = 0
        _p, r = dps[:i+1], dps[i+1:]
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


#@functools.cache
def derivative_to_vec(d, context):
    # pretty sure that we don't need it
    return order_of_derivative(d, len(context._independent))

def find_multipliers_and_nonmultipliers(S, context):
    pass


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
    if len(result) == 1:
        return result
    vars = list(range(len(context._independent)))

    def map_old_to_new(v):
        return context._independent[vars.index(v)]

    while 1:
        monomials = [(_, _.order) for _ in result]
        ms        = tuple([_[1] for _ in monomials])
        m0 = []

        multiplier_collection = []
        new_multipliers = My_Multiplier([tuple(_[1]) for _ in monomials]).mults
        for monom, dp in zip(monomials, result):
            # S1
            _nonmultipliers = list(set(vars) - set())
            dp.multipliers = new_multipliers[tuple(monom[1])]
            dp.nonmultipliers = list(set(vars) - set(dp.multipliers))
            multiplier_collection.append((monom[1], dp))

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
                dp = _Differential_Polynomial(_m0[2].diff(map_old_to_new(_m0[1])).expression(), context)
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
    if len(result) == 1:
        return []
    vars = list(range(len(context._independent)))
    monomials = [(_, _.order) for _ in result]

    ms = tuple([_[1] for _ in monomials])

    def map_old_to_new(i):
        return context._independent[vars.index(i)]

    # multiplier-collection is our M
    multiplier_collection = []
    monomial_tuples = [tuple(_[1]) for _ in monomials]
    new_multipliers = My_Multiplier(monomial_tuples).mults
    for mon, dp in zip (monomial_tuples, result):
        # S1
        # damned! Variables are messed up!
        _multipliers = new_multipliers[mon]
        _nonmultipliers = list(set(vars) - set(_multipliers))
        multiplier_collection.append(
            (dp,
             [map_old_to_new(_) for _ in _multipliers],
             [map_old_to_new(_) for _ in _nonmultipliers]
             ))
    result = []
    for e1, e2 in product(multiplier_collection, repeat=2):
        if e1 is e2: continue
        for n in e1[2]:
            for m in islice(powerset(e2[1]), 1, None):
                if eq(adiff(e1[0].Lder(), context, n), adiff(e2[0].Lder(), context, *m)):
                    # integrability condition
                    # don't need leading coefficients because in DPs
                    # it is always 1
                    c = adiff(e1[0].expression(), context, n) - \
                        adiff(e2[0].expression(), context, *m)
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
        diff(w(x, y), y) + (-1/y) * w(x, y), [x ,y], []
        diff(z(x, y), x) + (1/2/y) * w(x, y), [y, x], []
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
        self.S = Reorder([_Differential_Polynomial(s, context) for s in self.S], context, ascending = True)
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
#            set_trace()
            for _ in self.S:
                print(_)
            self.S = Autoreduce(self.S, context)
            print("after autoreduce")
            for _ in self.S:
                print(_)
            self.S = CompleteSystem(self.S, context)
            print("after complete system")
            for _ in self.S:
                print(_)
            self.conditions = list(split_by_function(self.S, context))

            print("This are the conditions")
            print(f"{self.conditions}")
            if not self.conditions:
                self.S = Reorder(self.S, context, ascending=True)
                return

            reduced = [reduceS(_Differential_Polynomial(_m, context), self.S, context)
                       for _m in self.conditions
                       ]
            self.S += [_ for _ in reduced if
                       not (_ in self.S or eq(_.expression(), 0))]
            self.S = Reorder(self.S, context, ascending=True)
            for _ in self.S:
                print(_.Lder())

    def show(self, rich=False):
        """Print the Janet basis with leading derivative first."""
        for _ in self.S:
            if rich:
                display(Math(_.show()))
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
