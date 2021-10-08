# +
# #!/usr/bin/env python
# coding: utf-8
# -


# strange ! this import works in every other module
from sage.calculus.functional import diff
from sage.calculus.var import function, var
from collections.abc import Iterable
from sage.symbolic.operators import FDerivativeOperator

def tangent_vector(f):
    r"""
    Do a tangent vector

    DEFINITION:

    missing

    INPUT:

    - ``f`` - symbolic expressinf of type 'function'

    OUTPUT:

    the tangent vector

    .. NOTE::

    none so far

    ..

    EXAMPLES: compute the tangent vector of

    ::
    sage: from delierium.helpers import tangent_vector
    sage: x,y,z = var ("x y z")
    sage: tangent_vector (x**2 - 3*y**4 - z*x*y + z - x)
    [-y*z + 2*x - 1, -12*y^3 - x*z, -x*y + 1]
    sage: tangent_vector (x**2 + 2*y**3 - 3*z**4)
    [2*x, 6*y^2, -12*z^3]
    sage: tangent_vector (x**2)
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
    >>> x,y,z = var ("x,y,z")
    >>> f = function("f")(x,y,z)
    >>> d = diff(f, x,x,y,z,z,z)
    >>> from delierium.helpers import order_of_derivative
    >>> order_of_derivative (d)
    [2, 1, 3]
    '''
    opr = e.operator()
    opd = e.operands()
    if not is_derivative (e):
        return [0] * len(e.variables())
    res = [opr.parameter_set().count(i) for i in range(len(opd))]
    return res

def highest_order_of_derivative(e):
    # xxx _of_ in function name is annyoing
    e      = e if isinstance(e, Iterable) else [e]
    return max([sum (order_of_derivative(_)) for _ in e])


#def __lt__(a, b):
#    '''
#    sorts functions lexicographically
#    '''
#    astr = a.operator().__str__()
#   bstr = b.operator().__str__()
#    if astr < bstr:
#        return -1
#    if astr > bstr:
#        return 1
#    return 0


def is_derivative(e):
    '''checks whether an expression 'e' is a pure derivative

    >>> from delierium.helpers import is_derivative
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
        return isinstance(e.operator(), FDerivativeOperator)
    except AttributeError:
        pass


def is_function(e):
    '''checks whether an expression 'e' is a pure function without any
    derivative as a factor

    >>> from delierium.helpers import is_function
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


def vector_to_monomial(v, sort=None):
    '''
    >>> from delierium.helpers import vector_to_monomial
    >>> vector_to_monomial ([1,2,3,4])
    x1*x2^2*x3^3*x4^4
    '''
    from functools import reduce
    from operator import __mul__
    vars = var(" ".join('x%s' % _ for _ in range(1, len(v)+1)))
    return reduce(__mul__, [v**e for v, e in zip(vars, v)], 1)

def monomial_to_vector(m, sort=None):
    '''
    >>> from delierium.helpers import monomial_to_vector
    >>> x1,x3,x3 = var("x1 x2 x3")
    >>> monomial_to_vector (x1**4 * x2**2 * x3**1)
    [4, 2, 1]
    >>> x1,x3,x3 = var("x1 x2 x3")
    >>> monomial_to_vector (x2**2 * x3**1)
    [0, 2, 1]
    '''
    res = []
    for _m in m.operands():
        if _m.operands ():
            res.append (_m.operands()[1])
        else:
            res.append (1)
    return res


if __name__ == "__main__":
    import doctest
    doctest.testmod()
