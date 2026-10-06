"""Matrix_Order"""

from collections.abc import Callable, Iterable, Sequence
from functools import cache

from sympy import Basic, Matrix, eye

__all__ = [
    "Context",
    "Mgrevlex",
    "Mgrlex",
    "Mlex",
]

# a term order: the weight matrix for the dependent and independent variables
WeightFunction = Callable[[Sequence[Basic], Sequence[Basic]], Matrix]

#
# standard weight matrices for lex, grlex and grevlex order
# according to 'Term orders and Rankings' Schwarz, pp 43.
#


def Mlex(funcs: Sequence[Basic], variables: Sequence[Basic]) -> Matrix:  # noqa: N802  # pylint: disable=invalid-name
    '''Generates the "cotes" according to Riquier for the lex ordering
    INPUT : funcs: a tuple of functions (tuple for caching reasons)
            variables: a tuple of variables
            these are not used directly , just their lenght is interasting, but
            so the consumer doesn't has the burden of computing the length of
            list but the lists directly from context
    OUTPUT: a matrix which when multiplying an augmented vector (func + var)
            gives the vector in lex order

            same applies mutatis mutandis for Mgrlex and Mgrevlex

    >>> from sympy import Function, symbols
    >>> x, y, z = symbols("x y z")
    >>> f = Function("f")(x, y, z)
    >>> g = Function("g")(x, y, z)
    >>> h = Function("h")(x, y, z)
    >>> print(Mlex((f, g), [x, y, z]))
    Matrix([[0, 0, 0, 2, 1], [1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]])
    >>> x, y = symbols("x y")
    >>> w = Function("w")(x, y)
    >>> z = Function("z")(x, y)
    >>> print(Mlex((z, w), (x, y)))
    Matrix([[0, 0, 2, 1], [1, 0, 0, 0], [0, 1, 0, 0]])
    '''
    no_funcs = len(funcs)
    no_vars = len(variables)
    i = eye(no_vars)
    i = i.row_insert(0, Matrix(1, no_vars, [0] * no_vars))
    for j in range(no_funcs, 0, -1):
        i = i.row_join(Matrix([j] + [0] * no_vars))
    return i


def Mgrlex(funcs: Sequence[Basic], variables: Sequence[Basic]) -> Matrix:  # noqa: N802  # pylint: disable=invalid-name
    '''Generates the "cotes" according to Riquier for the grlex ordering
    >>> from sympy import Function, symbols
    >>> x,y,z = symbols("x y z")
    >>> f = Function("f")(x,y,z)
    >>> g = Function("g")(x,y,z)
    >>> h = Function("h")(x,y,z)
    >>> print(Mgrlex((f,g,h), [x,y,z])) # doctest: +NORMALIZE_WHITESPACE
    Matrix([[1, 1, 1, 0, 0, 0], [0, 0, 0, 3, 2, 1], [1, 0, 0, 0, 0, 0], \
[0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]])
    '''
    m = Mlex(funcs, variables)
    first_row = Matrix(1, len(variables) + len(funcs), [1] * len(variables) + [0] * len(funcs))
    return m.row_insert(0, first_row)


def Mgrevlex(funcs: Sequence[Basic], variables: Sequence[Basic]) -> Matrix:  # noqa: N802  # pylint: disable=invalid-name
    '''Generates the "cotes" according to Riquier for the grevlex ordering
    >>> from sympy import Function, symbols
    >>> x, y, z = symbols("x y z")
    >>> f = Function("f")(x, y, z)
    >>> g = Function("g")(x, y, z)
    >>> h = Function("h")(x, y, z)
    >>> print(Mgrevlex ((f,g,h), [x,y,z]))
    Matrix([[1, 1, 1, 0, 0, 0], [0, 0, 0, 3, 2, 1], \
[0, 0, -1, 0, 0, 0], [0, -1, 0, 0, 0, 0], [-1, 0, 0, 0, 0, 0]])
    '''
    no_funcs = len(funcs)
    no_vars = len(variables)
    cols = no_funcs + no_vars
    first_row = [1] * no_vars + [0] * no_funcs
    l = Matrix(1, cols, first_row)
    second_row = Matrix(1, cols, [0] * no_vars + list(range(no_funcs, 0, -1)))
    l = l.row_insert(cols, second_row)
    for idx in range(no_vars):
        row = Matrix(1, cols, [0] * cols)
        row[no_vars - idx - 1] = -1
        l = l.row_insert(2 + idx, row)
    return l


class Context:  # pylint: disable=too-few-public-methods,too-many-instance-attributes  # the public API are the cached callables
    """Define the context for comparisons, orders, etc."""

    def __init__(
        self,
        dependent: Iterable[Basic],
        independent: Iterable[Basic],
        weight: WeightFunction = Mgrevlex,
    ) -> None:
        """sorting : (in)dependent [i] > (in)dependent [i+i]
        which means: descending
        """
        self.independent = tuple(independent)
        self.dependent = tuple(dependent)
        self.sort_order = weight
        # LHDP.normalize makes the coefficients coprime polynomials instead
        # of dividing by the leading coefficient (see JanetBasis)
        self.fraction_free = False
        # LHDPs made while this is set are not normalized (janet_basis.
        # reduce_by_system normalizes only its result)
        self.defer_normalize = False
        # the rows of the weight matrix, as Python ints where they are integers
        self._weight = [
            [int(w) if w.is_Integer else w for w in row]
            for row in weight(self.dependent, self.independent).tolist()
        ]
        # per-instance caches; functools.cache on the methods themselves
        # would keep every Context alive for the lifetime of the process
        self.gt = cache(self._gt)
        self.is_dependent = cache(self._is_dependent)
        self.order_of_derivative = cache(self._order_of_derivative)

    def _gt(self, v1: Sequence[int], v2: Sequence[int]) -> bool:
        """v1 ranks above v2: the first nonzero entry of the weight matrix
        times v1 - v2 is positive. v1, v2 are comparison vectors (see
        janet_basis.ComparisonVector); equal ones are not greater."""
        difference = [a - b for a, b in zip(v1, v2, strict=True)]
        for row in self._weight:
            if entry := sum(w * d for w, d in zip(row, difference, strict=True)):
                return bool(entry > 0)
        return False

    def _is_dependent(self, f: Basic) -> bool:
        """Check if 'f' is in the list of dependent variables."""
        return f in self.dependent

    def _order_of_derivative(self, e: Basic) -> list[int]:
        """Returns the vector of the orders of a derivative respect to its variables

        >>> from sympy import Function, diff, symbols
        >>> x, y, z = symbols("x,y,z")
        >>> f = Function("f")(x, y, z)
        >>> ctx = Context([f], [x, y, z])
        >>> d = f.diff(x, x, y, z, z, z)
        >>> ctx.order_of_derivative(d)
        [2, 1, 3]
        """
        res = [0] * len(e.args[0].args)
        if not e.is_Derivative:
            return res
        for variable in e.variables:
            i = self.independent.index(variable)
            res[i] += 1  # count
        return res


if __name__ == "__main__":
    import doctest

    doctest.testmod()
