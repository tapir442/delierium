import sage.all
from collections.abc import Iterable
import functools

@functools.cache
def eq(d1, d2):
    '''This cheap trick gives as a lot of performance gain
    because maxima comparisons are expensive,and we can expect
    a lot of the same comparisons over and over again
    '''
    return bool (d1==d2)



def tangent_vector(f):
    # https://doc.sagemath.org/html/en/reference/manifolds/sage/manifolds/differentiable/tangent_vector.html?highlight=partial%20differential
    # XXX:  There is TangentVector in Sage but a little bit more complicated. Does it pay to use that one ?
    r"""
    Do a tangent vector

    DEFINITION:

    missing

    INPUT:

    - ``f`` - symbolic expression of type 'function'

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
    '''Returns the vector of the orders of a derivative respect to its variables

    >>> x,y,z = var ("x,y,z")
    >>> f = function("f")(x,y,z)
    >>> d = diff(f, x,x,y,z,z,z)
    >>> from delierium.helpers import order_of_derivative
    >>> order_of_derivative (d)
    [2, 1, 3]
    '''
    opr = e.operator ()
    opd = e.operands ()
    if not isinstance(opr, sage.symbolic.operators.FDerivativeOperator):
        return [0] * len (e.variables())
    res = [opr.parameter_set().count(i) for i in range (len(opd))]
    return res

#def highest_order_of_derivative(e):
#    # xxx _of_ in function name is annyoing
#    e      = e if isinstance(e, Iterable) else [e]
#    return max([sum (order_of_derivative(_)) for _ in e])

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
    try :
        return isinstance(e.operator(), sage.symbolic.operators.FDerivativeOperator)
    except AttributeError:
        return False

#Don't cache ! slows down
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
    if hasattr (e, "operator"):
        return "NewSymbolicFunction" in e.operator ().__class__.__name__ and \
            e.operands() != []
    return False
#    try :
#        # XXX this must done more sagemathic if possible
#        return "NewSymbolicFunction" in e.operator ().__class__.__name__ and \
#            e.operands() != []
#    except AttributeError:
#        return False


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


def monomial_to_vector(m, no_of_variables, sort=None):
    '''
    >>> from delierium.helpers import monomial_to_vector
    >>> x1,x3,x3 = var("x1 x2 x3")
    >>> monomial_to_vector (x1**4 * x2**2 * x3**1, 3)
    [4, 2, 1]
    >>> x1,x3,x3 = var("x1 x2 x3")
    >>> monomial_to_vector (x2**2 * x3**1, 3)
    [0, 2, 1]
    '''
    res = []
    vars = var(" ".join('x%s' % _ for _ in range(1, no_of_variables+1)))
    operands = m.operands()
    def get_exponent(v, o):
        for _o in o:
            ops = _o.operands()
            if ops:
                if bool(v == ops[0]):
                    return ops[1]
            else:
                if bool(v == _o):
                    return 1

        return 0
    for _var in vars:
        res.append (get_exponent (_var, operands))
    return res
