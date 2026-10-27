"""Janet division: the multiplier and nonmultiplier variables of monomials
(exponent vectors), Janet classes and the minimal Janet completion of a
set of monomials. Used by janet_basis for the differential polynomials,
whose leading derivatives are such monomials.
"""

from collections import namedtuple
from collections.abc import Iterable, Sequence

from delierium.helpers import profile_if_enabled

__all__ = ["MultiplierClass", "in_janet_class", "janet_completion", "vec_degree", "vec_multipliers"]


def vec_degree(v: int, m: Sequence[int]) -> int:
    """The degree of the monomial m in the variable v.

    >>> vec_degree(1, (2, 3))
    3
    """
    return m[v]


@profile_if_enabled
def vec_multipliers(
    m: Sequence[int], M: Iterable[Sequence[int]], Vars: Sequence[int]
) -> tuple[list[int], list[int]]:
    """multipliers and nonmultipliers for differential vectors aka tuples

    m   : a tuple representing a differential vector
    M   : the complete set of differential vectors
    Vars: a tuple representing the order of indizes in m
          Examples:
              (0,1,2) means first index in m represents the highest variable
              (2,1,0) means last index in m represents the highest variable

    Returns (multipliers, nonmultipliers), as lists of indices in m.

    Follows the Maple procedure Janet in Amir Hashemi's invbasis,
    https://amirhashemi.iut.ac.ir/sites/amirhashemi.iut.ac.ir/files//file_basepage/invbasis.txt

    ......................................................
    The doctest example is from Schwarz, Example C.1, p. 384
    This example is in on variables x1,x2,x3, with x3 the highest rated variable.
    So we have to specify (2,1,0) to represent this

    >>> M = [(2, 2, 3), (3, 0, 3), (3, 1, 1), (0, 1, 1)]
    >>> r = vec_multipliers(M[0], M, (2, 1, 0))
    >>> print(M[0], r[0], r[1])
    (2, 2, 3) [2, 1, 0] []
    >>> r = vec_multipliers(M[1], M, (2, 1, 0))
    >>> print(M[1], r[0], r[1])
    (3, 0, 3) [2, 0] [1]
    >>> r = vec_multipliers(M[2], M, (2, 1, 0))
    >>> print(M[2], r[0], r[1])
    (3, 1, 1) [1, 0] [2]
    >>> r = vec_multipliers(M[3], M, (2, 1, 0))
    >>> print(M[3], r[0], r[1])
    (0, 1, 1) [1] [0, 2]
    >>> N = [[0, 2], [2, 0], [1, 1]]
    >>> r = vec_multipliers(N[0], N, (0, 1))
    >>> print(r)
    ([1], [0])
    >>> r = vec_multipliers(N[1], N, (0, 1))
    >>> print(r)
    ([0, 1], [])
    >>> r = vec_multipliers(N[2], N, (0, 1))
    >>> print(r)
    ([1], [0])
    >>> r = vec_multipliers(N[0], N, (1, 0))
    >>> print(r)
    ([1, 0], [])
    >>> r = vec_multipliers(N[1], N, (1, 0))
    >>> print(r)
    ([0], [1])
    >>> r = vec_multipliers(N[2], N, (1, 0))
    >>> print(r)
    ([0], [1])
    >>> # next example form Gerdt/Blinkov: Janet-like monomial divisiom, Table1
    >>> # x1 -> Index 2
    >>> # x2 -> Index 1 (this is easy)
    >>> # x3 -> Index 0
    >>> U = [[0, 0, 5], [1, 2, 2], [2, 0, 2], [1, 4, 0], [2, 1, 0], [5, 0, 0]]
    >>> vec_multipliers(U[0], U, (2, 1, 0))
    ([2, 1, 0], [])
    >>> vec_multipliers(U[1], U, (2, 1, 0))
    ([1, 0], [2])
    >>> vec_multipliers(U[2], U, (2, 1, 0))
    ([0], [1, 2])
    >>> vec_multipliers(U[3], U, (2, 1, 0))
    ([1, 0], [2])
    >>> vec_multipliers(U[4], U, (2, 1, 0))
    ([0], [1, 2])
    >>> vec_multipliers(U[5], U, (2, 1, 0))
    ([0], [1, 2])
    >>> # the first variable is compared with its own maximal degree
    >>> V = [(0, 2), (1, 0)]
    >>> vec_multipliers(V[0], V, (0, 1))
    ([1], [0])
    >>> vec_multipliers(V[1], V, (0, 1))
    ([0, 1], [])
    >>> vec_multipliers(V[0], V[:1], (0, 1))
    ([0, 1], [])
    >>> # Iohara/Malbos, Example 3.2.6: five variables, the last index is the highest
    >>> W = [
    ...     (0, 0, 0, 1, 1),
    ...     (0, 0, 1, 0, 1),
    ...     (0, 1, 0, 0, 1),
    ...     (0, 0, 0, 2, 0),
    ...     (0, 0, 1, 1, 0),
    ...     (0, 0, 2, 0, 0),
    ... ]
    >>> for w in W:
    ...     print(w, *vec_multipliers(w, W, (4, 3, 2, 1, 0)))
    (0, 0, 0, 1, 1) [4, 3, 2, 1, 0] []
    (0, 0, 1, 0, 1) [4, 2, 1, 0] [3]
    (0, 1, 0, 0, 1) [4, 1, 0] [2, 3]
    (0, 0, 0, 2, 0) [3, 2, 1, 0] [4]
    (0, 0, 1, 1, 0) [2, 1, 0] [3, 4]
    (0, 0, 2, 0, 0) [2, 1, 0] [3, 4]
    """
    # Janet: the highest variable is a multiplier if m has the maximal degree in it
    d = max((vec_degree(Vars[0], u) for u in M), default=0)
    mult = []
    if vec_degree(Vars[0], m) == d:
        mult.append(Vars[0])
    for j, v in enumerate(Vars[1:], start=1):
        dd = [vec_degree(x, m) for x in Vars[:j]]
        V = [u for u in M if [vec_degree(x, u) for x in Vars[:j]] == dd]
        if vec_degree(v, m) == max((vec_degree(v, u) for u in V), default=0):
            mult.append(v)
    return mult, sorted(set(Vars) - set(mult))


# an element of S with its multiplier and nonmultiplier variables
MultiplierClass = namedtuple("MultiplierClass", ["monom", "dp", "multipliers", "nonmultipliers"])


def in_janet_class(
    monom: Sequence[int],
    base: Sequence[int],
    multipliers: Iterable[int],
    nonmultipliers: Iterable[int],
) -> bool:
    """monom lies in the Janet class of base: it is base multiplied by
    multiplier variables only (Schwarz, p. 383).

    >>> in_janet_class((2, 1), (1, 1), [0], [1]), in_janet_class((2, 2), (1, 1), [0], [1])
    (True, False)
    """
    return all(monom[i] >= base[i] for i in multipliers) and all(
        monom[i] == base[i] for i in nonmultipliers
    )


def janet_completion(monomials: Iterable[Sequence[int]], n: int) -> set[tuple[int, ...]]:
    """The minimal Janet completion of a set of monomials (exponent vectors).

    Unlike complete(), which adds all missing prolongations of a pass at
    once, only the lowest one (by degree) is added before the Janet classes
    are computed again; so no element is added that a lower prolongation
    would already cover (Gerdt, Blinkov, minimal involutive bases).

    >>> sorted(janet_completion([(0, 1, 1), (1, 1, 0)], 3))
    [(0, 1, 1), (1, 1, 0)]
    >>> sorted(janet_completion([(0, 0, 2), (1, 1, 0)], 3))
    [(0, 0, 2), (1, 0, 2), (1, 1, 0)]
    >>> sorted(janet_completion([(0, 1, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)], 3))
    [(0, 1, 1), (1, 0, 2), (1, 1, 1), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
    """
    result = {tuple(m) for m in monomials}
    while True:
        orders = list(result)
        classes = [(m, *vec_multipliers(m, orders, range(n))) for m in orders]
        missing = set()
        for m, _, nonmultipliers in classes:
            for k in nonmultipliers:
                raised = list(m)
                raised[k] += 1
                if not any(in_janet_class(raised, o, mult, non) for o, mult, non in classes):
                    missing.add(tuple(raised))
        if not missing:
            return result
        result.add(min(missing, key=lambda m: (sum(m), tuple(reversed(m)))))
