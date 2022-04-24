# +
# #!/usr/bin/env python
# coding: utf-8
# -

import sage.all
from sage.calculus.var import var, function
from sage.misc.reset import reset
from sage.calculus.functional import diff
try :
    from delierium.helpers import (is_derivative, is_function, eq,
                                   order_of_derivative, adiff, latexer)
    from delierium.MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
except ModuleNotFoundError:
    from helpers import (is_derivative, is_function, eq,
                         order_of_derivative, adiff, latexer)
    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex

import functools
from operator import mul
from IPython.core.debugger import set_trace
from collections.abc import Iterable
from more_itertools import powerset, bucket, flatten
from itertools import product, islice

from sage.misc.latex import latex
from sage.misc.html import html
import re


@functools.cache
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
        self._order      = self._compute_order()
        self._expression = self._coeff * self._d

    def __str__(self):
        try:
            return f"({self._coeff.expression()}) * {self._d}"
        except AttributeError:
            if eq (self._coeff, 1):
                return f"{self._d}"
            else:
                return f"({self._coeff}) * { self._d}"
    def term(self):
        return self._coeff * self._d
    def expression(self): 
        return self._expression
    def _compute_order(self):
        """computes the monomial tuple from the derivative part"""
        if is_derivative(self._d):
            return order_of_derivative(self._d, len(self._context._independent))
        else:
            return [0] * len(self._context._independent)
    def order(self):
        return self._order
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
        return not eq(self, other) and higher(self, other, self._context)

    @functools.cache
    def __eq__(self, other):
        return eq(self._d, other._d) and eq(self._coeff, other._coeff)

    def show(self, rich=True):
        if not rich:
            return str(self)
#        dlatex = latex(self._d)
#        pattern = re.compile(r"\\frac\{\\partial.*\}\{(?P<denominator>.+)\}(?P<funcname>.+)\\left\((?P<vars>.+)\\right\)")#
#        matcher = pattern.match(dlatex)
#        res     = []
#        funcname= ""
#        if matcher:
#            vars = matcher.groupdict()["vars"]
#            funcname = matcher.groupdict()["funcname"]
#            denominator   = matcher.groupdict()["denominator"]
 #           denom_matcher = re.compile(r"((\()?\\partial (?P<varname>\w+)(\)?)((\^\{(?P<exponent>\d+)\})?))")
 #           while denominator:
 #               den = denom_matcher.match(denominator)
  #              exp = den.groupdict()["exponent"]
   #             exp = int(exp) if exp else 1
    #            res.append((den.groupdict()["varname"], exp))
     #           denominator = denominator.replace(den.groups()[0], "")
#        else:
#            funcname = str(self._d.function().operator())
#        vstring = "".join((_[0]*_[1] for _ in res))
#        if self._coeff != 1:
#            h = "<p>$%s %s_{%s}$</p>" % (self._coeff, funcname, vstring)
 #       else:
  #          h = "<p>$%s_{%s}$</p>" % (funcname, vstring)
        return latexer(self._d)
    def __hash__(self):
        return hash(self._expression)


class _Differential_Polynomial:
    def __init__(self, e, context):
        self._context = context
        self._p = []
        if not eq(0, e):
            self._init(e.expand())
    def _init(self, e):
   #     def is_a_real_derivative(op):
   #         # XXX make this part of context ?
   #         return (is_derivative(op) and op.operator().function() in self._context._dependent) or \
   #             is_function(o)
   #     operands = e.operands()
   #     operator = e.operator()
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
            lambda item1, item2: sorter(item1._d, item2._d, self._context)
            ), reverse=True
        )
        self.normalize()

    def expression(self):
        return self._expression        
        
    def ctxfunc(self, e):
        return func(e) and func(e) in self._context._dependent

    def _collect_terms(self, e):
        pass

    def show_derivatives(self):
        print([x for x in self.derivatives()])

    def Lterm(self):
        return self._p[0].term()

    def Lder(self):
        return self._p[0]._d

    def Lfunc(self):
        if is_function(self._p[0]._d):
            return self._p[0]._d.operator()
        else:
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

    def __eq__(self, other):
        return all(eq(_[0]._d, _[1]._d) for _ in zip(self._p, other._p))

    def show(self, rich=True):
        breakpoint()
        if not rich:
            return str(self)
        r = ""
        for _ in self._p:
            k = _.show()
            if not _._has_minus:
                if r:
                    r += html("<p>+</p>") + k
                else:
                    r += k
            else:
                r += k
        return html(r.replace("</p><p>", "").replace("*", ""))

    def diff(self, *args):
        return type(self)(diff(self.expression(), *args), self._context)

    def __str__(self):
        return " + ".join([str(_) for _ in self._p])

    def __hash__(self):
        return hash(self.expression())


# ToDo: Janet_Basis as class as this object has properties like rank, order ...
def Reorder(S, context, ascending=False):
    return sorted(S, key=functools.cmp_to_key(
        lambda item1, item2:
            sorter(item1.Lder(), item2.Lder(), context)),
        reverse=not ascending)


def reduceS(e: _Differential_Polynomial,
            S: list, context: Context) -> _Differential_Polynomial:
    reducing = True
    gen = (_ for _ in S)
    while reducing:
        for dp in gen:
            enew = reduce(e, dp, context)
            # XXX check wheter we can repalce "==" by 'is'
            if enew == e:
                reducing = False
            else:
                e = enew
                gen = (_ for _ in S)
                reducing = True
    return enew
def reduce(e1: _Differential_Polynomial,e2: _Differential_Polynomial, context:Context)->_Differential_Polynomial:
    def _order(der):
        if der != 1:
            return order_of_derivative(der, len(context._independent))
        else:
            return [0]*len(context._independent)

    def _reduce_inner(e, ld):
        e2_order = _order(ld)
#        ldf      = func(ld)
#        # instead of looping over terms we just look for reduction with *equal *
#        # derivatives/functions, just for two hopes: no need to diff and faster
#        # elimination of terms
#        potential_funcs  = [(_order(t._d), t._coeff) for t in e._p if eq(ldf, func(t._d))
#               and all(map(lambda h: h == 0, [a-b for a, b in zip(_order(t._d), e2_order)]))]
#        if potential_funcs:
#            return _Differential_Polynomial(e1.expression() - e2.expression() * potential_funcs[0][1], context)
#
#        potential_funcs  = [(_order(t._d), t._coeff) for t in e._p if eq(ldf, func(t._d))#
#               and all(map(lambda h: h >= 0, [a-b for a, b in zip(_order(t._d), e2_order)]))]
#
#
#        if potential_funcs:
#            dif = [a-b for a,b in zip(potential_funcs[0][0], e2_order)]
#            variables_to_diff = []
#            for i in range(len(context._independent)):
#                if dif[i] != 0:
#                    variables_to_diff.extend([context._independent[i]]*abs(dif[i]))
#            return _Differential_Polynomial(e1.expression() - diff(e2.expression(), *variables_to_diff) * potential_funcs[0][1]
#                                           , context)
#        return e
        for t in e._p:
            d = t._d
            if func(ld) != func(d):
                continue
            c = t._coeff
            e1_order = _order(d)
            dif = [a-b for a, b in zip(e1_order, e2_order)]
            if all(map(lambda h: h == 0, dif)):
                return _Differential_Polynomial(
                    e1.expression() - e2.expression() * c, context)
            if all(map(lambda h: h >= 0, dif)):
                variables_to_diff = []
                for i in range(len(context._independent)):
                    if dif[i] != 0:
                        variables_to_diff.extend([context._independent[i]]*abs(dif[i]))
                return _Differential_Polynomial(e1.expression()-c*diff(e2.expression(), *variables_to_diff), context)
        return e

    _e1 = None
    while not bool((_e1 := _reduce_inner(e1, e2.Lder())) == e1):
        e1 = _e1
    return _e1

def Autoreduce(S, context):
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

    >>> M = [(2,2,3), (3,0,3), (3,1,1), (0,1,1)]
    >>> r = vec_multipliers (M[0],M, (2,1,0))
    >>> print (M[0], r[0], r[1])
    (2, 2, 3) [2, 1, 0] []
    >>> r = vec_multipliers (M[1],M, (2,1,0))
    >>> print (M[1], r[0], r[1])
    (3, 0, 3) [2, 0] [1]
    >>> r = vec_multipliers (M[2],M, (2,1,0))
    >>> print (M[2], r[0], r[1])
    (3, 1, 1) [1, 0] [2]
    >>> r = vec_multipliers (M[3],M, (2,1,0))
    >>> print (M[3], r[0], r[1])
    (0, 1, 1) [1] [0, 2]
    >>> N=[[0,2], [2,0], [1,1]]
    >>> r =vec_multipliers(N[0], N,  (0,1))
    >>> print(r)
    ([1], [0])
    >>> r =vec_multipliers(N[1], N,  (0,1))
    >>> print(r)
    ([0, 1], [])
    >>> r =vec_multipliers(N[2], N,  (0,1))
    >>> print(r)
    ([1], [0])
    >>> r =vec_multipliers(N[0], N,  (1,0))
    >>> print(r)
    ([1, 0], [])
    >>> r =vec_multipliers(N[1], N,  (1,0))
    >>> print(r)
    ([0], [1])
    >>> r =vec_multipliers(N[2], N,  (1,0))
    >>> print(r)
    ([0], [1])
    >>> # next example form Gertd/Blinkov: Janet-like monomial divisiom, Table1
    >>> # x1 -> Index 2
    >>> # x2 -> Index 1 (this is easy)
    >>> # x3 -> Index 0
    >>> U = [[0,0,5], [1,2,2],[2,0,2], [1,4,0],[2,1,0],[5,0,0]]
    >>> vec_multipliers(U[0], U, (2,1,0))
    ([2, 1, 0], [])
    >>> vec_multipliers(U[1], U, (2,1,0))
    ([1, 0], [2])
    >>> vec_multipliers(U[2], U, (2,1,0))
    ([0], [1, 2])
    >>> vec_multipliers(U[3], U, (2,1,0))
    ([1, 0], [2])
    >>> vec_multipliers(U[4], U, (2,1,0))
    ([0], [1, 2])
    >>> vec_multipliers(U[5], U, (2,1,0))
    ([0], [1, 2])
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


@functools.cache
def derivative_to_vec(d, context):
    return order_of_derivative(d, len(context._independent))


def complete(S, context):
    result = list(S)
    if len(result) == 1:
        return result
    vars = list(range(len(context._independent)))

    def map_old_to_new(v):
        return context._independent[vars.index(v)]
    while 1:
        monomials = [(_, derivative_to_vec(_.Lder(), context)) for _ in result]
        ms        = tuple([_[1] for _ in monomials])
        m0 = []

        # multiplier-collection is our M
        multiplier_collection = []
        for dp, monom in monomials:
            # S1
            _multipliers, _nonmultipliers = vec_multipliers(monom, ms, vars)
            multiplier_collection.append((monom, dp, _multipliers, _nonmultipliers))
        for monom, dp, _multipliers, _nonmultipliers in multiplier_collection:
            if not _nonmultipliers:
                m0.append((monom, None, dp))
            else:
                # todo: do we need subsets or is a multiplication by only one
                # nonmultiplier one after the other enough ?
                for n in _nonmultipliers:
                    _m0 = list(monom)
                    _m0[n] += 1
                    m0.append((_m0, n, dp))
        to_remove = []
        for _m0 in m0:
            # S3: check whether in class of any of the monomials
            for monomial, _, _multipliers, _nonmultipliers in multiplier_collection:
                if all(_m0[0][x] >= monomial[x] for x in _multipliers) and \
                   all(_m0[0][x] == monomial[x] for x in _nonmultipliers):
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
    result = list(S)
    if len(result) == 1:
        return []
    vars = list(range(len(context._independent)))
    monomials = [(_, derivative_to_vec(_.Lder(), context)) for _ in result]

    ms = tuple([_[1] for _ in monomials])

    def map_old_to_new(i):
        return context._independent[vars.index(i)]

    # multiplier-collection is our M
    multiplier_collection = []
    for dp, monom in monomials:
        # S1
        # damned! Variables are messed up!
        _multipliers, _nonmultipliers = vec_multipliers(monom, ms, vars)
        multiplier_collection.append(
            (dp,
             [map_old_to_new(_) for _ in _multipliers],
             [map_old_to_new(_) for _ in _nonmultipliers]
             ))
    result = []
    for e1, e2 in product(multiplier_collection, repeat=2):
        if e1 == e2: continue
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
        diff(z(x, y), y)
        diff(z(x, y), x) + (1/2/y) * w(x, y)
        diff(w(x, y), y) + (-1/y) * w(x, y)
        diff(w(x, y), x)
        """
        eq.cache_clear()
        context = Context(dependent, independent, sort_order)
        if not isinstance(S, Iterable):
            # bad criterion
            self.S = [S]
        else:
            self.S = S[:]
        old = []
        self.S = Reorder([_Differential_Polynomial(s, context) for s in self.S], context, ascending = True)
        while 1:
            if old == self.S:
                # no change since last run
                return
            old = self.S[:]
            #print("This is where we start")
            #self.show()
            #for _ in self.S:
            #    _.Lder().show()            
            # set_trace()
            self.S = Autoreduce(self.S, context)
            #print("after autoreduce")
            #self.show()
            #for _ in self.S:
            #    _.Lder().show()
            
            self.S = CompleteSystem(self.S, context)
            #print("after complete system")
            #self.show()
            
            self.conditions = split_by_function(self.S, context)
            reduced = [reduceS(_Differential_Polynomial(_m, context), self.S, context)
                       for _m in self.conditions
                       ]
            if not reduced:
                self.S = Reorder(self.S, context)
                return
            self.S += [_ for _ in reduced if
                       not (_ in self.S or eq(_.expression(), 0))]
            self.S = Reorder(self.S, context, ascending=True)

    def show(self, rich=False):
        """Print the Janet basis with leading derivative first."""
        if rich:
            return html("".join((_.show() for _ in self.S)))
        else:
            for _ in self.S:
                print(_)
        other_re = r"(?P<prefix>.+)?(?P<deriveoperator>D\[.*\]\(\w+\)\(.+\))"

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
