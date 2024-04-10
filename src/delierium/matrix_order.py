"""matrix_order"""

import sage.all # pylint: disable=W0611
from sage.matrix.constructor import identity_matrix  # pylint: disable=E0611
from sage.matrix.constructor import matrix  # pylint: disable=E0611
from sage.calculus.var import var  # pylint: disable=W0611,E0611
from sage.calculus.var import function  # pylint: disable=W0611,E0611
from sage.calculus.functional import diff  # pylint: disable=W0611
from sage.modules.free_module_element import vector  # pylint: disable=E0611

from delierium.helpers import is_derivative, is_function

from functools import cache

#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#


def insert_row(mat, k, row):
    """Use this as insert_row is only defined for integer matrices :("""
    return matrix(mat.rows()[:k]+[row] + mat.rows()[k:])


def Mlex(funcs, variables):  # pylint: disable=C0103
    '''Generates the "cotes" according to Riquier for the lex ordering
    INPUT : funcs: a tuple of functions (tuple for caching reasons)
            variables: a tuple of variables
            these are not used directly , just their lenght is interasting, but
            so the consumer doesn't has the burden of computing the length of
            list but the lists directly from context
    OUTPUT: a matrix which when multiplying an augmented vector (func + var)
            gives the vector in lex order

            same applies mutatis mutandis for Mgrlex and Mgrevlex

    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
    >>> Mlex ((f,g), [x,y,z])
    [0 0 0 2 1]
    [1 0 0 0 0]
    [0 1 0 0 0]
    [0 0 1 0 0]
    >>> x,y = var ("x y")
    >>> w = function("w")(x,y)
    >>> z = function("z")(x,y)
    >>> Mlex((z,w), (x,y))
    [0 0 2 1]
    [1 0 0 0]
    [0 1 0 0]
    '''
    no_funcs = len(funcs)
    no_vars = len(variables)
    i = identity_matrix(no_vars)
    i = insert_row(i, 0, [0]*no_vars)
    for j in range(no_funcs, 0, -1):
        i = i.augment(vector([j] + [0]*no_vars))
    return i


def Mgrlex(funcs, variables):  # pylint: disable=C0103
    '''Generates the "cotes" according to Riquier for the grlex ordering
    >>> x,y,z = var ("x y z")
    >>> f = function("f")(x,y,z)
    >>> g = function("g")(x,y,z)
    >>> h = function("h")(x,y,z)
    >>> Mgrlex ((f,g,h), [x,y,z])
    [1 1 1 0 0 0]
    [0 0 0 3 2 1]
    [1 0 0 0 0 0]
    [0 1 0 0 0 0]
    [0 0 1 0 0 0]
    '''
    m = Mlex(funcs, variables)
    m = insert_row(m, 0, [1]*len(variables)+[0]*len(funcs))
    return m


def Mgrevlex(funcs, variables):  # pylint: disable=C0103
    '''Generates the "cotes" according to Riquier for the grevlex ordering
    >>> _ = var ("x y z")
    >>> f = function("f")(*_)
    >>> g = function("g")(*_)
    >>> h = function("h")(*_)
    >>> Mgrevlex ((f,g,h), [x,y,z])
    [ 1  1  1  0  0  0]
    [ 0  0  0  3  2  1]
    [ 0  0 -1  0  0  0]
    [ 0 -1  0  0  0  0]
    [-1  0  0  0  0  0]
    '''
    no_funcs = len(funcs)
    no_vars = len(variables)
    l = matrix([1]*no_vars + [0]*no_funcs)
    l = insert_row(l, 1, vector([0]*no_vars + list(range(no_funcs, 0, -1))))
    for idx in range(no_vars):
        _v = vector([0]*(no_vars+no_funcs))
        _v[no_vars-idx-1] = -1
        l = insert_row(l, 2+idx, _v)
    return l

class Context:
    """Define the context for comparisons, orders, etc."""
    def __init__(self, dependent, independent, weight = Mgrevlex):
        """ sorting : (in)dependent [i] > (in)dependent [i+i]
        which means: descending
        """
        self._independent = tuple(independent)
        self._dependent = tuple((_.operator() if is_function(_) else _
                                 for _ in dependent))
        self._weight = weight(self._dependent, self._independent)

    @cache
    def gt(self, v1: vector, v2: vector) -> int:
        """Computes the weighted difference vector of v1 and v2
        and returns 'True' if the first nonzero entry is > 0
        """
        r = self._weight * (vector(v1)-vector(v2))
        for entry in r:
            if entry:
                return entry > 0
        return False

        return _gt(self._weight, v1, v2)

    @cache
    def lt(self, v1, v2):
        """Checks if v1 < v2."""
        return v1 != v2 and not self.gt(v1, v2)

    @cache
    def is_ctxfunc(self, f):
        """Check if 'f' is in the list of independet variables."""
        if f in self._dependent:
            return True
        if hasattr(f, "function") and f.function().operator() in self._dependent:
            return True
        return False


    def order_of_derivative(self, e):
        """Returns the vector of the orders of a derivative respect to its variables

        >>> x,y,z = var ("x,y,z")
        >>> f = function("f")(x,y,z)
        >>> ctx = Context([f], [x,y,z])
        >>> d = diff(f, x,x,y,z,z,z)
        >>> ctx.order_of_derivative (d)
        [2, 1, 3]
        """
        res = [0] * len(e.variables())
        if not is_derivative(e):
            return res
        for idx, variable in enumerate(e.variables()):
            # XXX. here seems to be the crucial part: order can depend on:
            # - either the order given by sage by
            # -- sage order
            # -- order given by the order given by function definition
            # - the order given by context
            i = self._independent.index(variable)
            res[i] = e.operator().parameter_set().count(idx)
        return res


if __name__ == "__main__":
    import doctest
    doctest.testmod()
