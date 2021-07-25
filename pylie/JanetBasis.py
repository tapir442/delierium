#!/usr/bin/env python
# coding: utf-8

from sage.all import *
from pylie import *
from pprint import pprint
import functools
from operator import mul
from IPython.core.debugger import set_trace




class DTerm:
    '''differential term'''
    def __init__ (self, e, context = None):
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
            self._coeff = functools.reduce (mul, r, 1).expand().simplify_full()
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
    def is_monic(self):
        return self._d != 1 and bool(self._coeff == 1)
    def __lt__ (self, other):
        return higher (self, other,self._context) and not self == other
    def __le__ (self, other):
        return higher (self, other,self._context)
    def __ge__ (self, other):
        return higher (self, other,self._context) 
    def __gt__ (self, other):
        return higher (self, other,self._context) and not self == other
    def __eq__ (self, other):
        return self._d == other._d and bool(self._coeff == other._coeff)
    def __neq__ (self, other):
        return self._d != other._d
    def show(self):
        self.term().show()
    def expression (self):
        return self.term().expression()
        
    
class Differential_Polynomial:
    def __init__ (self, e, context):
        #set_trace()
        self._context = context
        self._init(e.expand())

    def _init(self, e):
        self._p = []
        res = []
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
        self._p = sorted(self._p)
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

    def coefficients (self):
        for p in self._p:
            yield p._coeff
    def is_monic (self):
        if self._p:
            return self._p[0].is_monic()
        return True
    def normalize (self):
        if self._p:
            self._p = [_ for _ in self._p if _._coeff and not bool(_._coeff == 0)]
            c = self._p[0]._coeff
            self._p = [ DTerm((_._coeff / c) * _._d, self._context) for _ in self._p]
    def __nonzero__ (self):
        return self._p
    def expression (self):
        return sum(_._coeff * _._d for _ in self._p)
    def __lt__ (self, other):
        return self._p[0] < other._p[0]
    def __le__ (self, other):
        return self._p[0] <= other._p[0]
    def __ge__ (self, other):
        return self._p[0] >= other._p[0]
    def __gt__ (self, other):
        return self._p[0] > other._p[0]
    def __eq__ (self, other):
        #todo pythonify
        for a, b in zip (self._p, other._p):
            if a != b: return False
        return True
    def __neq__ (self, other):
        return self._p[0] != other._p[0]
    def show(self):
        self.expression().show()
    def __sub__ (self, other):
        for o in other._p:
            found = False
            for s in self._p:
                if s._d == o._d:
                    s._coeff -= o._coeff
                    found = True
                    break
        if not found:
            self._p.append(o)
            self._p[-1]._coeff *= Integer(-1)
        return Differential_Polynomial(self.expression(), self._context)
    def __add__ (self, other):
        for o in other._p:
            found = False
            for s in self._p:
                if s._d == o._d:
                    s._coeff += o._coeff
                    found = True
                    break
            if not found:
                self._p.append(o)
        return Differential_Polynomial(self.expression(), self._context)        
    def __mul__ (self, other):
        for t in self._p:
             t._coeff *= other
        return Differential_Polynomial(self.expression(), self._context)    
    def __copy__(self):
        newone = type(self)(self.expression(), self._context)
        return newone

# ToDo: Janet_Basis as class as this object has properties like rank, order ....
def Reorder (S, context, ascending = False):
    res=sorted(S)
    if ascending :
        res.reverse()
    return res
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
    assert e2.is_monic()
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
    assert (m in M)
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
    return mult                