# +
# #!/usr/bin/env python
# coding: utf-8
# -

from sage.all import *
from delierium import *
from pprint import pprint
import functools
from operator import mul
from IPython.core.debugger import set_trace


@functools.cache
def eq(d1, d2):
    return bool (d1==d2)

@functools.total_ordering
class DTerm:
    def __init__ (self, e, context = None):
        r'''differential term

        >>> from delierium.JanetBasis import DTerm
        >>> from delierium.MatrixOrder import Context
        >>> x,y,z = sage.all.var("x y z")
        >>> f     = sage.all.function("f")(x,y,z)
        >>> g     = sage.all.function("g")(x,y,z)
        >>> h     = sage.all.function("h")(x,y,z)
        >>> ctx   = Context ((f,g),(x,y,z))
        >>> d     = (x**2) * sage.all.diff(f, x, y)
        >>> dterm = DTerm(d,ctx)
        >>> print (dterm)
        x^2 * diff(f(x, y, z), x, y)
        '''
        self._coeff       = Rational(1)
        self._d           = Rational(1)
        self._context     = context
        if is_derivative(e) or is_function(e):
            # XXX put into _d only if in in context
            self._d = e
        else:
            r = []
            for o in e.operands ():
                if is_derivative (o):
                    self._d = o
                else:
                    if is_function(o) and o in context._dependent:
                        self._d = o  # zeroth derivative
                    else:
                        r.append (o)
            # XXX how to get rid of simpify_full? It's eating up all the cpu
            self._coeff = functools.reduce (mul, r, 1)
            if bool(self._coeff == Integer(1)):
                self._coeff = 1
            if bool(self._coeff == Integer(0)):
                self._coeff = 0
            if not r:
                raise ValueError("invalid expression '{}' for DTerm".format(e))
    def __str__ (self):
        return "{} * {}".format (self._coeff, self._d)
    def term(self):
        return self._coeff * self._d
    def order (self):
        if is_derivative(self._d):
            return order_of_derivative (self._d)
        else:
            return [0] * len (context._independent)
    def is_coefficient(self):
        # XXX nonsense
        return self._d == 1

    def derivative (self):
        return self._d

    def is_monic(self):
        return self._d != 1 and bool(self._coeff == 1)
    def __lt__ (self, other):
        return higher (self, other,self._context) and not self == other
    def __eq__ (self, other):
        return eq(self._d, other._d) and bool(self._coeff == other._coeff)
    def show(self):
        self.term().show()
    def expression (self):
        return self.term().expression()
    def __hash__ (self):
        return hash(self.__str__())

@functools.total_ordering
class Differential_Polynomial:
    def __init__ (self, e, context):
        self._context = context
        self._init(e.expand())

    def _init(self, e):
        self._p = []
        res     = []
        if is_derivative(e) or is_function(e):
            self._p.append(DTerm(e, self._context))
        else:
            for s in e.operands ():
                coeff = []
                d     = []
                if is_derivative (s):
                    d.append(s)
                else:
                    for item in s.operands():
                        (d if (is_derivative(item) or self.ctxfunc (item)) else coeff).append(item)
                coeff = functools.reduce (mul, coeff, 1)
                if bool (coeff == 0):
                    continue
                found = False
                for _p in self._p:
                    if not d:
                        continue
                    if d and _p._d == d[0]:
                        _p._coeff += coeff
                        found = True
                        break
                if not found:
                    if d:
                        self._p.append (DTerm(coeff * d[0], self._context))
                    else:
                        self._p.append (DTerm(coeff, self._context))
        self._p = [_ for _ in reversed(
                    sorted(
                        self._p,
                        key=functools.cmp_to_key(lambda item1, item2:
                                             sorter (item1.derivative(), item2.derivative(), self._context)))
                )]
        self.normalize()

    def ctxfunc(self, e):
        def func(e):
            try:
                return e.operator().function()
            except AttributeError:
                return e.operator()
        return func(e) and func(e) in self._context._dependent

    def _collect_terms (self, e):
        pass

    def show_derivatives(self):
        print ([x for x in self.derivatives()])

    def Lterm (self):
        return self._p[0].term()

    def Lder (self):
        return self._p[0]._d

    def Lcoeff(self):
        return self._p[0]

    def terms (self):
        for p in self._p:
            yield p.term()

    def derivatives (self):
        for p in self._p:
            yield p._d

    def Ldervec (self):
        # implement asap
        pass

    def coefficients (self):
        for p in self._p:
            yield p._coeff
    def is_monic (self):
        if self._p:
            return self._p[0].is_monic()
        return True
    def normalize (self):
        if self._p:
            if bool (self._p[0]._coeff == Integer (1)):
                self._p[0]._coeff = 1
            else:
                c = self._p[0]._coeff
                self._p = [DTerm((_._coeff / c).simplify() * _._d, self._context) for _ in self._p]
    def __nonzero__ (self):
        return self._p
    def expression (self):
        return sum(_._coeff * _._d for _ in self._p)
    @functools.cache
    def __lt__ (self, other):
        return self._p[0] < other._p[0]
    @functools.cache
    def __eq__ (self, other):
        return all(bool(_[0]._d == _[1]._d) for _ in zip (self._p, other._p))
    def show(self):
        self.expression().show()
    def __sub__ (self, other):
        return Differential_Polynomial(self.expression() - other.expression(), self._context)
    def __add__ (self, other):
        return Differential_Polynomial(self.expression() + other.expression(), self._context)
    def __mul__ (self, other):
        return Differential_Polynomial(self.expression() * other , self._context)
    def __copy__(self):
        newone = type(self)(self.expression(), self._context)
        return newone
    def __hash__ (self):
        return hash(repr(self))

# ToDo: Janet_Basis as class as this object has properties like rank, order ....
def Reorder (S, context, ascending = False):
    return sorted(S, key=functools.cmp_to_key(lambda item1, item2:
                        sorter (item1.Lder(), item2.Lder(), context)),
                            reverse = not ascending
                        )

def reduceS (e:Differential_Polynomial, S:list, context)->Differential_Polynomial:
    S= Reorder (S, context, ascending = True)
    reducing = True
    gen = (_ for _ in S)
    while reducing:
        for p in gen:
            enew = reduce (e, p, context)
            if enew == e:
                reducing = False
            else:
                e = enew
                gen = (_ for _ in S)
                reducing = True
    return enew
def reduce(e1: Differential_Polynomial,e2: Differential_Polynomial, context:Context)->Differential_Polynomial:
    def _order (der):
        if der != 1:
            ## XXX: user pylie namespace
            return order_of_derivative(der)
        else :
            return [0]*len(context._independent)
    def func(e):
        try:
            return e.operator().function()
        except AttributeError:
            return e.operator()

    def _reduce (e, ld):
        e2_order = _order (ld)
        for t in e._p:
            d = t._d
            c = t._coeff
            if func(ld) != func(d):
                continue
            e1_order = _order (d)
            dif = [a-b for a, b in zip (e1_order, e2_order)]
            if all (map (lambda h: h == 0, dif)) :
                return Differential_Polynomial (e1.expression() - e2.expression() * c, context)
            if all (map (lambda h: h >= 0, dif)):
                variables_to_diff = []
                for i in range (len(context._independent)):
                    if dif [i] != 0:
                        variables_to_diff.extend ([context._independent[i]]*abs(dif[i]))
                return Differential_Polynomial (e1.expression()-c*diff(e2.expression(), *variables_to_diff), context)
        return e

    _e1 = None
    while True:
        _e1 = _reduce (e1, e2.Lder())
        if bool(_e1 == e1):
            return _e1
        e1 = _e1

def Autoreduce(S, context):
    dps = list(S)
    i = 0
    while True:
        p = dps[:i+1]
        r = dps[i+1:]
        if not r:
            return dps
        newdps = []
        have_reduced = False
        for _r in r:
            rnew = reduceS(_r, p, context)
            have_reduced = have_reduced or rnew != _r
            newdps.append(rnew)
        dps = Reorder(p + [_ for _  in newdps if _ not in p], context, ascending = True)
        if not have_reduced:
            # no reduction done
            i += 1
        else:
            # start from scratch
            i = 0

def degree(v, m)->Integer:
    # returnd degree of variable 'v' in monomial 'm'
    for operand in m.operands():
        if bool(v == operand):
            return 1
        e = operand.operands()
        if e and bool (e[0] == v):
            return e[1]
    return 0

def multipliers(m, M, Vars):
    """Multipliers for Monomials"""
    assert (m in M)
    # ToDo: convert to differential vectors and use vec_multipliers!
    d = max((degree (v, u) for u in M for v in Vars), default=0)
    mult = []
    if degree (Vars[0], m) == d:
        mult.append (Vars[0])
    for j in range (1, len (Vars)):
        v = Vars[j]
        dd = list (map (lambda x: degree (x,m), Vars[:j]))
        V = []
        for _u in M:
            if [degree (_v, _u) for _v in Vars[:j]]==dd:
                V.append (_u)
        if degree (v, m) == max((degree (v, _u) for _u in V), default = 0):
            mult.append (v)
    # XXX return nonmultipliers, too
    return mult

def vec_degree(v, m)->Integer:
    return m[v]

def vec_multipliers(m, M, Vars):
    """multipliers and nonmultipliers for differential vectors
    """
    d = max((vec_degree (v, u) for u in M for v in Vars), default=0)
    mult = []
    if vec_degree (Vars[0], m) == d:
        mult.append (Vars[0])
    for j in range (1, len (Vars)):
        v = Vars[j]
        dd = list (map (lambda x: vec_degree (x,m), Vars[:j]))
        V = []
        for _u in M:
            if [vec_degree (_v, _u) for _v in Vars[:j]]==dd:
                V.append (_u)
        if vec_degree (v, m) == max((vec_degree (v, _u) for _u in V), default = 0):
            mult.append (v)
    return mult, set(Vars) - set(mult)


# +
@functools.total_ordering
class Differential_Vector:
    """Differential Vector:
       maps a partial derivative to a tuple representing this derivative
    """
    def __init__ (self,e, ctx):
        """
            e   : expression for the derivative
            ctx : context object representing the order of variables
        """
        self._e = self.obj = e
        # is this the right place to do ?
        if ctx._weight == Mlex:
            M = matrix.identity(len(self._e))
        elif ctx._weight == Mgrlex:
            M = matrix (len(self._e))
            for i in range(len(self._e)):
                M [0, i] = 1
            for i in range (len(self._e) - 1):
                M [i+1, i] = 1
        elif ctx._weight == Mgrevlex:
            M = matrix (len(self._e))
            for i in range(len(self._e)):
                M [0, i] = 1
            for i in range (1,len(self._e)):
                M [len(self._e)-i, i] = -1
        self.M = M

    #XXX use functools.cmp_to_key ?
    def mycmp (self, a, b):
        a = self.M*vector(a)
        b = self.M*vector(b)
        v = [_a - _b for _a,_b in zip (a, b)]
        # XXX check order
        for _ in v:
            if _ < 0:
                return 1
            if _ > 0:
                return -1
        return 0
    def __lt__(self, other):
        return self.mycmp(self.obj, other.obj) < 0
    def __eq__(self, other):
        return self.mycmp(self.obj, other.obj) == 0


def in_class (r, mclass, M, vars):
    '''checks whether "r" is in the same class like "mclass"'''
    mult, nonmult = vec_multipliers (mclass, M , vars)
    return all (vec_degree (x, r) >= vec_degree (x, mclass) for x in mult)  and \
        all (vec_degree(x, r) == vec_degree (x, mclass) for x in nonmult)

def derivative_to_vec (d, context):
    return order_of_derivative (d)


def complete (l,ctx):
    ld         = [derivative_to_vec(_.Lder(), ctx) for _ in l]
    sort_order = tuple(reversed([i for i in range(len(ctx._independent))]))
    m0         = []
    for m, monomial in zip (ld, l):
        _, nonmult = vec_multipliers (m , ld , sort_order)
        for nm in nonmult:
            _m = list(m)
            _m [nm] += 1
            # XXX Fixme
            if not any (in_class (tuple(_m), v, l, sort_order) for v in l):
                m0.append (diff (monomial, ctx._independent[nm]))

        if set(m0) == set():
            return l
        l.extend (m0)
        l = reversed(sorted(map (lambda _ : Differential_Vector(_, ctx), list(set(l)))))
        l = [_._e for _ in l]

def CompleteSystem(S, context):
    #return S
    s = {}
    for _ in S:
        _fun = _.Lder().operator().function()
        s.setdefault (_fun, []).append (_)
    res = []
    for k in s:
        _ = complete (s[k], context)
        res.extend (_)
    return Reorder(res, context, ascending = True)
# -
