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
    from delierium.Involution import Multipliers
except ModuleNotFoundError:
    from helpers import (is_derivative, is_function, eq,
                         order_of_derivative, adiff, latexer)
    from MatrixOrder import higher, sorter, Context, Mgrlex, Mgrevlex
    from Involution import Multipliers

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
        if is_derivative(e) or is_function(e):
            self._d     = e
        else:
            r = []
            for o in e.operands():
                #print (f"{e=}, {o=}")
                if is_derivative(o) or is_function(o):
                    self._d = o
                else:
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

        dlatex = latex(self._coeff)
        denominator_pattern = re.compile(r"(-)?\\frac\{.*}{(.* )?(?P<nomfunc>\w+)?\\left\((?P<vars>[\w ,]*)\\right\).*")
        res     = []
        funcname= ""
        while match := denominator_pattern.match(dlatex):
            to_replace = r"%s\left(%s\right)" % (match.groupdict()['nomfunc'], match.groupdict()['vars'])
            dlatex = dlatex.replace (to_replace, match.groupdict()['nomfunc'])
        if self._coeff != 1:
            return " ".join ((dlatex, latexer(self._d)))
        else:
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
        return res

    def diff(self, *args):
        return type(self)(diff(self.expression(), *args), self._context)

    def __str__(self):
        return " + ".join([str(_) for _ in self._p])

    def __hash__(self):
        return hash(self.expression())

    def order(self):
        return self._p[0]._order

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


def reduce(e1: _Differential_Polynomial,
           e2: _Differential_Polynomial,
           context: Context) -> _Differential_Polynomial:
    """Reduce e1 wrt e2 according to Schwarz, S1
    """
    @functools.cache
    def _order(der):
        if der != 1:
            return order_of_derivative(der, len(context._independent))
        else:
            return [0]*len(context._independent)

    def _reduce_inner(e1, e2):
        e2_order = _order(e2.Lder())
        lf = func(e2.Lder())
        for t in (_ for _ in e1._p if eq(func(_._d), lf)):
            c = t._coeff
            e1_order = _order(t._d)
            dif = [a-b for a, b in zip(e1_order, e2_order)]
            if all(map(lambda h: h == 0, dif)):
                return _Differential_Polynomial(
                    e1.expression() - e2.expression() * c, context)
            if all(map(lambda h: h >= 0, dif)):
                variables_to_diff = []
                for i in range(len(context._independent)):
                    if dif[i] != 0:
                        variables_to_diff.extend([context._independent[i]]*abs(dif[i]))
                return _Differential_Polynomial(
                    e1.expression() - c*diff(e2.expression(), *variables_to_diff),
                    context)
        return e1
    while not bool((_e1 := _reduce_inner(e1, e2)) == e1):
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
        i = 0 if have_reduced else i + 1
        _p, r = dps[:i+1], dps[i+1:]
    return dps


@functools.cache
def derivative_to_vec(d, context):
    return order_of_derivative(d, len(context._independent))

from delierium.Involution import complete as invcomplete
from pprint import pprint

def complete(S, context):
    # XXX rework without Differential polynomial. just with leading monomials
    # XXX create differential polynomials when returning the result
    # XXX put 'complete' into Involution, easier to test, and much faster
    result = list(S)
    if len(result) == 1:
        return result
    vars = list(range(len(context._independent)))    
    def map_old_to_new(v):
        return context._independent[vars.index(v)]
    for _ in result:
        _.show()
        
    monomials = [tuple(_._p[0]._order) for _ in result]
    print("monomials")
    for m in monomials:
        print(m)
    m0 = invcomplete(monomials)
    h = []
    def create(poly):
        result=[]
        found = True
        anchor = poly[2]
        p      = poly
        while found:
            for m in m0:
                if anchor == m[2]:
                    dp = _Differential_Polynomial(p.diff(map_old_to_new(m[1])).expression(), context)
                    result.append(dp)
                    anchor = dp._p[0]._order
                    p      = dp
                else:
                    found = False
        return result
    for r in m0:
        new_dpolynomials = create(r)
        result.extend(new_dpolynomials)
    return result


def CompleteSystem(S, context):
    """
    Algorithm C1, Schwarz p. 385

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
        division = Multipliers(monom, ms, vars)
        _multipliers, _nonmultipliers = division.multipliers, division.nonmultipliers
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
            print("*"*99)
            print("This is where we start")
            self.show(rich=True)
            for _ in self.S:
                _.Lder().show()
            #set_trace()
            self.S = Autoreduce(self.S, context)
            print("after autoreduce")
            self.show(rich=True)
            for _ in self.S:
                _.Lder().show()

            #set_trace()
            self.S = CompleteSystem(self.S, context)
            print("after complete system")
            self.show(rich=True)

            self.conditions = list(split_by_function(self.S, context))
            print("Conditions")
            for _ in self.conditions:
                _.show()
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

