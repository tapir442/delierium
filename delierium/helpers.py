import sage.all
import functools
from sage.calculus.var import var, function
from sage.calculus.functional import diff
from sage.symbolic.operators import FDerivativeOperator
import more_itertools

@functools.cache
def eq(d1, d2):
    '''This cheap trick gives as a lot of performance gain (> 80%!)
    because maxima comparisons are expensive,and we can expect
    a lot of the same comparisons over and over again.
    All other caching is neglegible compared to this here
    70 % of the time is spent here!
    '''
    return bool(d1 == d2)


def tangent_vector(f):
    # https://doc.sagemath.org/html/en/reference/manifolds/sage/manifolds/differentiable/tangent_vector.html?highlight=partial%20differential
    # XXX:  There is TangentVector in Sage but a little bit more complicated.
    # Does it pay to use that one ?
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
    t = var("t")
    newvars = [var("x%s" % i) for i in f.variables()]
    for o, n in zip(f.variables(), newvars):
        f = f.subs({o: o+t*n})
    d = diff(f, t).limit(t=0)
    return [d.coefficient(_) for _ in newvars]

def order_of_derivative(e, required_len=0):
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
    if not isinstance(opr, sage.symbolic.operators.FDerivativeOperator):
        return [0] * max((len(e.variables()), required_len))
    res = [opr.parameter_set().count(i) for i in range(len(opd))]
    return res


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
        return False

def is_function(e):
    '''checks whether an expression 'e' is a pure function without any
    derivative as a factor

    >>> x = var('x')
    >>> f = function ('f')(x)
    >>> is_function (f)
    True
    >>> is_function (diff(f,x))
    False
    >>> is_function (x*diff(f,x))
    False
    >>> is_function (x*f)
    False
    '''
    if hasattr(e, "operator"):
        return "NewSymbolicFunction" in e.operator().__class__.__name__ and \
            e.operands() != []
    return False


def compactify(*vars):
    pairs = list(more_itertools.pairwise(vars))
    if not pairs:
        return [vars[0]]
    result = []
    for pair in pairs:
        if isinstance(pair[0], Integer):
            continue
        elif isinstance(pair[1], Integer):
            result.extend([pair[0]] * pair[1])
        else:
            result.append(pair[0])
    return result


@functools.cache
def adiff(f, context, *vars):
    use_func_diff = any("NewSymbolicFunction" in v.__class__.__name__ for v in vars)
    for op in f.operands():
        if "NewSymbolicFunction" in op.operator().__class__.__name__ :
            use_func_diff = True
    if use_func_diff:
        for v in vars:
            if "NewSymbolicFunction" in v.__class__.__name__:
                f = func_diff(f,  v(context._independent[1]))
            else:
                xx = SR.var("xx")
                gg = f.subs({context._independent[0](context._independent[1]):xx})
                gg = diff(gg, v)
                f=gg.subs({xx:context._independent[0](context._independent[1])})
    else:
        f = f.diff(*vars)
    return f


def is_op_du(expr_op, u):
    is_derivative = isinstance(
        expr_op,
        sage.symbolic.operators.FDerivativeOperator
    )
    if is_derivative:
        # Returns True if the differentiated function is `u`.
        return expr_op.function() == u.operator()
    else:
        return False


def iter_du_orders(expr, u):
    for sub_expr in expr.operands():
        if sub_expr == []:
            # hit end of tree
            continue
        elif is_op_du(sub_expr.operator(), u):
            # yield order of differentiation
            yield len(sub_expr.operator().parameter_set())
        else:
            # iterate into sub expression
            for order in iter_du_orders(sub_expr, u):
                yield order


def func_diff(L, u_in):
    """ `u` must be a callable symbolic expression
    """
#    https://ask.sagemath.org/question/7929/computing-variational-derivatives/
    x = u_in.variables()[0]
    u = u_in.function(x)

    # This variable name must not collide
    # with an existing one.
    # who will call a variable "tapir"
    # nobody else does this...
    t = SR.var('tapir')
    result = SR(0)

    # `orders` is the set of all
    # orders of differentiation of `u`
    orders = set(iter_du_orders(L, u)).union((0,))

    for c in orders:
        du = u(x).diff(x, c)
        sign = Integer(-1)**c

        # Temporarily replace all `c`th derivatives of `u` with `t`;
        # differentiate; then substitute back.
        dL_du = L.subs({du: t}).diff(t).subs({t: du})

        # Append intermediate term to `result`
        result += sign * dL_du.diff(x, c)

    return result
