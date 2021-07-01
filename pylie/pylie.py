import sage.all
from collections.abc import Iterable
import functools

def tangent_vector(f):
    # https://doc.sagemath.org/html/en/reference/manifolds/sage/manifolds/differentiable/tangent_vector.html?highlight=partial%20differential
    # XXX:  There is TangentVector in Sage but a little bit more complicated. Does it pay to use that one ?
    from sage.calculus.var import var
    from sage.calculus.functional import diff
    t = var("t")
    newvars = [var("x%s" % i) for i in f.variables()]
    for o, n in zip(f.variables(), newvars):
        f = f.subs({o: o+t*n})
    d = diff(f, t).limit(t=0)
    return [d.coefficient(_) for _ in newvars]

#
def order_of_derivative (e):
    opr = e.operator ()
    opd = e.operands ()
    if not isinstance(opr, sage.symbolic.operators.FDerivativeOperator):
        return [0] * len (e.variables())
    res = [opr.parameter_set().count(i) for i in range (len(opd))]
    return res

def highest_order_of_derivative(e):
    # xxx _of_ in function name is annyoing
    e      = e if isinstance(e, Iterable) else [e]
    return max([sum (order_of_derivative(_)) for _ in e])

def __lt__ (a,b):
    '''
    sorts functions lexicographically
    '''
    astr = a.operator().__str__()
    bstr = b.operator().__str__()
    if astr < bstr:
        return -1
    if astr > bstr:
        return 1
    return 0

def is_derivative(e):
    '''checks whether an expression 'e' is a derivative'''
    try :
        return isinstance(e.operator(), sage.symbolic.operators.FDerivativeOperator)
    except AttributeError:
        return False

def is_function(e):
    '''checks whether an expression 'e' is a function'''
    try :
        # XXX this must done more sagemathic if possible
        return "NewSymbolicFunction" in e.operator ().__class__.__name__ and \
            e.operands() != []
    except AttributeError:
        return False
