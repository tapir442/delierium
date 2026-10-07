"""The type of a Lie algebra of dimension at most 4 in Lie's classification
of the complex Lie algebras, with Schwarz's names (Algorithmic Lie Theory
for Solving Ordinary Differential Equations, section 3.4): l1, l2,1, l2,2,
l3,1 ... l3,6, l4,1 ... l4,17 (#11).

The type is decided by invariants: the dimensions of the derived series,
nilpotency, the center, the rank of the Killing form and, for the solvable
algebras, the Jordan form of ad X on the derived algebra (or on g'/g'') for
an X outside it, whose eigenvalue ratios are the parameters. Over the
complex numbers, so the rotations so(3) are sl(2) (l3,1) and the Euclidean
algebra e(2) is l3,2 with c = -1. Parameters that depend on symbols are
taken for generic values of them.

Two corrections of Schwarz's listing: l4,7 has a derived algebra of
dimension 3 (U1, U2, U2 + U3), not 2; and l4,9 with a = 1 is l4,14 (Schwarz
derives both from l4,6, with b = 0 and with a = 1, b = 0), so l4,9 needs
a != 1 as l4,14 is listed separately.
"""

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from sympy import Expr, Matrix, cancel, default_sort_key, eye, simplify, sympify

if TYPE_CHECKING:
    from delierium.lie_algebra import LieAlgebra

__all__ = ["LieAlgebraType", "lie_algebra_type"]


@dataclass(frozen=True)
class LieAlgebraType:
    """A type of Schwarz's listing, e.g. l3,2 with parameters {"c": -1}."""

    name: str
    parameters: dict[str, Expr] = field(default_factory=dict)

    def __str__(self) -> str:
        if not self.parameters:
            return self.name
        values = ", ".join(f"{k} = {v}" for k, v in self.parameters.items())
        return f"{self.name}({values})"


def lie_algebra_type(algebra: "LieAlgebra") -> LieAlgebraType | None:
    """The type of algebra in Lie's classification (Schwarz 3.4), None if
    its dimension is above 4."""
    r = algebra.dimension
    derived = algebra.derived_series()
    d1 = derived[1] if len(derived) > 1 else r
    if r == 1:
        return LieAlgebraType("l1")
    if r == 2:
        return LieAlgebraType("l2,2" if d1 == 0 else "l2,1")
    if r == 3:
        return _dimension_3(algebra, d1)
    if r == 4:
        return _dimension_4(algebra, derived)
    return None


def _dimension_3(algebra: "LieAlgebra", d1: int) -> LieAlgebraType:
    if d1 == 0:
        return LieAlgebraType("l3,6")
    if d1 == 3:
        return LieAlgebraType("l3,1")
    if d1 == 1:
        return LieAlgebraType("l3,5" if algebra.is_nilpotent() else "l3,4")
    # d1 == 2: the derived algebra is abelian, ad X acts on it invertibly
    blocks = _jordan_blocks(_ad_on(algebra, _derived(algebra)))
    if len(blocks) == 1:
        return LieAlgebraType("l3,3")
    lam1, lam2 = _two_eigenvalues(blocks)
    return LieAlgebraType("l3,2", {"c": _canonical([lam2 / lam1, lam1 / lam2])})


def _dimension_4(algebra: "LieAlgebra", derived: list[int]) -> LieAlgebraType:
    d1 = derived[1] if len(derived) > 1 else 4
    d2 = derived[2] if len(derived) > 2 else d1
    if d1 == 0:
        return LieAlgebraType("l4,17")
    if d1 == 1:
        return LieAlgebraType("l4,16" if algebra.is_nilpotent() else "l4,15")
    if d1 == 3 and d2 == 3:
        return LieAlgebraType("l4,1")
    if d1 == 3 and d2 == 1:
        return _heisenberg_ideal(algebra)
    if d1 == 3:
        return _abelian_ideal_3(algebra)
    return _derived_dimension_2(algebra)


def _heisenberg_ideal(algebra: "LieAlgebra") -> LieAlgebraType:
    """g' is the Heisenberg algebra with center g'': ad X on g'/g''."""
    g1 = _derived(algebra)
    g2 = algebra._span_of_brackets(g1, g1)  # pylint: disable=protected-access
    # a basis of g' starting with g'': the induced map is the lower block
    basis = _extend(g2, g1)
    induced = _ad_on(algebra, basis)[1:, 1:]
    blocks = _jordan_blocks(induced)
    if len(blocks) == 1:
        return LieAlgebraType("l4,4")
    lam1, lam2 = _two_eigenvalues(blocks)
    return LieAlgebraType("l4,5", {"c": 1 + _canonical([lam2 / lam1, lam1 / lam2])})


def _abelian_ideal_3(algebra: "LieAlgebra") -> LieAlgebraType:
    """g' abelian of dimension 3: the Jordan form of ad X on it."""
    blocks = _jordan_blocks(_ad_on(algebra, _derived(algebra)))
    sizes = sorted(size for _, size in blocks)
    if sizes == [3]:
        return LieAlgebraType("l4,2")
    if sizes == [1, 2]:
        mu = next(lam for lam, size in blocks if size == 2)
        nu = next(lam for lam, size in blocks if size == 1)
        if cancel(nu - mu) == 0:
            return LieAlgebraType("l4,7")
        return LieAlgebraType("l4,3", {"c": cancel(mu / (nu - mu))})
    lams = [lam for lam, _ in blocks]
    options = [
        (cancel(lams[j] / lams[i]), cancel(lams[k] / lams[i]))
        for i, j, k in [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]
    ]
    a, b = min(options, key=lambda ab: (_size(ab[0]) + _size(ab[1]), default_sort_key(ab)))
    return LieAlgebraType("l4,6", {"a": a, "b": b})


def _derived_dimension_2(algebra: "LieAlgebra") -> LieAlgebraType:
    if algebra.is_nilpotent():
        return LieAlgebraType("l4,13")
    center = algebra.center()
    if center.rows == 0:
        # l2,1 + l2,1 (Killing form of rank 2) or l4,12 (rank 1)
        return LieAlgebraType(
            "l4,10" if algebra.killing_form().rank(simplify=True) == 2 else "l4,12"
        )
    g1 = _derived(algebra)
    if Matrix.vstack(g1, center).rank(simplify=True) == g1.rows:
        return LieAlgebraType("l4,11")  # the center lies in g'
    # a 3-dimensional algebra plus the center: ad X on g', X outside g' + center
    blocks = _jordan_blocks(_ad_on(algebra, g1, Matrix.vstack(g1, center)))
    if len(blocks) == 1:
        return LieAlgebraType("l4,8")
    lam1, lam2 = _two_eigenvalues(blocks)
    if cancel(lam1 - lam2) == 0:
        return LieAlgebraType("l4,14")
    return LieAlgebraType("l4,9", {"a": _canonical([lam2 / lam1, lam1 / lam2])})


def _derived(algebra: "LieAlgebra") -> Matrix:
    g = eye(algebra.dimension)
    return algebra._span_of_brackets(g, g)  # pylint: disable=protected-access


def _outside(algebra: "LieAlgebra", subspace: Matrix) -> Matrix:
    """A basis vector (row) not in the span of the rows of subspace."""
    r = algebra.dimension
    for i in range(r):
        e = eye(r)[i, :]
        if Matrix.vstack(subspace, e).rank(simplify=True) > subspace.rank(simplify=True):
            return e
    raise ValueError("the subspace is everything")


def _ad_on(algebra: "LieAlgebra", basis: Matrix, avoid: Matrix | None = None) -> Matrix:
    """The matrix of ad X on the invariant subspace spanned by the rows of
    basis, in that basis, for a basis vector X outside avoid (default:
    the subspace)."""
    r, c = algebra.dimension, algebra.structure_constants
    x = _outside(algebra, basis if avoid is None else avoid)
    ad = Matrix(r, r, lambda k, j: sum(x[i] * c[i][j][k] for i in range(r)))
    images = ad * basis.T  # columns: ad X of the basis vectors
    solution, _ = basis.T.gauss_jordan_solve(images)
    return solution.applyfunc(cancel)


def _extend(sub: Matrix, space: Matrix) -> Matrix:
    """A basis of the row space of space, starting with the rows of sub."""
    rows = sub
    for i in range(space.rows):
        candidate = Matrix.vstack(rows, space[i, :])
        if candidate.rank(simplify=True) > rows.rank(simplify=True):
            rows = candidate
    return rows


def _jordan_blocks(m: Matrix) -> list[tuple[Expr, int]]:
    """(eigenvalue, size) of the Jordan blocks of m."""
    _, j = m.jordan_form()
    blocks: list[tuple[Expr, int]] = []
    i = 0
    while i < j.rows:
        size = 1
        while i + size < j.rows and simplify(j[i + size - 1, i + size]) != 0:
            size += 1
        blocks.append((simplify(j[i, i]), size))
        i += size
    return blocks


def _two_eigenvalues(blocks: list[tuple[Expr, int]]) -> tuple[Expr, Expr]:
    """The eigenvalues of a diagonalizable 2x2 matrix from its blocks."""
    if len(blocks) != 2:
        raise ValueError(f"expected two Jordan blocks of size 1, got {blocks}")
    return blocks[0][0], blocks[1][0]


def _size(e: Expr) -> int:
    return len(str(e))


def _canonical(options: list[Expr]) -> Expr:
    """The representative of a parameter defined up to the given choices
    (c or 1/c): a number of absolute value at most 1, or else the shortest."""
    options = [cancel(sympify(o)) for o in options]

    def key(o: Expr) -> tuple[int, int, tuple[object, ...]]:
        small = o.is_number and abs(o) <= 1
        return (0 if small else 1, _size(o), default_sort_key(o))

    return min(options, key=key)
