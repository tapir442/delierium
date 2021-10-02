# +
# #!/usr/bin/env python
# coding: utf-8
# -


# strange ! this import works in every other module
from sage.all import *
from collections.abc import Iterable
import functools

def tangent_vector(f):
    """
    >>> from delierium import *
    >>> x,y,z = sage.all.var ("x y z")
    >>> fun   = sage.all.function ("fun")(x,y,z)
    >>> fun   = x**2 - 3*y**4 - z*x*y + z - x  
    >>> tangent_vector (fun)
    [-y*z + 2*x - 1, -12*y^3 - x*z, -x*y + 1]
    >>> fun = x**2 + 2*y**3 - 3*z**4
    >>> tangent_vector (fun)
    [2*x, 6*y^2, -12*z^3]
    >>> fun = x**2 
    >>> tangent_vector (fun)    
    [2*x]
    """
    t = var("t")
    newvars = [var("x%s" % i) for i in f.variables()]
    for o, n in zip(f.variables(), newvars):
        f = f.subs({o: o+t*n})
    d = diff(f, t).limit(t=0)
    return [d.coefficient(_) for _ in newvars]

#


def order_of_derivative(e):
    '''Returns the vector of the orders of a derivative respect to its variables
    >>> from delierium import *
    >>> x,y,z = sage.all.var ("x,y,z")
    >>> f = sage.all.function("f")(x,y,z)
    >>> d = sage.all.diff(f, x,x,y,z,z,z)
    >>> order_of_derivative (d)
    [2, 1, 3]
    '''
    opr = e.operator()
    opd = e.operands()
    if not isinstance(opr, sage.symbolic.operators.FDerivativeOperator):
        return [0] * len(e.variables())
    res = [opr.parameter_set().count(i) for i in range(len(opd))]
    return res

# def highest_order_of_derivative(e):
#    # xxx _of_ in function name is annyoing
#    e      = e if isinstance(e, Iterable) else [e]
#    return max([sum (order_of_derivative(_)) for _ in e])


def __lt__(a, b):
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
    '''checks whether an expression 'e' is a pure derivative
    >>> from delierium import *
    >>> x = var('x')
    >>> f = function ('f')(x)
    >>> is_derivative (f)
    False
    >>> is_derivative (diff(f,x))
    True
    >>> is_derivative (diff(f,x)*x)
    False
    '''
    try:
        return isinstance(e.operator(), sage.symbolic.operators.FDerivativeOperator)
    except AttributeError:
        pass


def is_function(e):
    '''checks whether an expression 'e' is a pure function without any 
    derivative as a factor
    
    >>> from delierium import *
    >>> x = var('x')
    >>> f = function ('f')(x)
    >>> is_function (f)
    True
    >>> is_function (diff(f,x))
    False
    >>> is_function (x*diff(f,x))
    False
    '''
    try:
        # XXX this must done more sagemathic if possible
        return "NewSymbolicFunction" in e.operator().__class__.__name__ and \
            e.operands() != []
    except AttributeError:
        pass
    
if __name__ == "__main__":
    import doctest
    doctest.testmod()    
