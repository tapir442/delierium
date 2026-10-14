"""One-dimensional optimal systems of a Lie algebra (#44, experimental).

Two generators v, w of a Lie algebra g are equivalent if Ad(g) v = c w for
an element g of the group and a constant c != 0; a similarity reduction by v
then gives the invariant solutions of a reduction by w, transformed. An
optimal system lists one generator of every class (Olver 3.3, Hydon 10.2).

The adjoint action of exp(eps x) on v = sum_i a_i X_i is

    Ad exp(eps x) v = v - eps [x, v] + eps**2/2 [x, [x, v]] - ...,

i.e. a -> a exp(-eps M_x) with (M_x)_ik = sum_j x_j c_ji^k (Hydon (10.27),
with the opposite sign convention). Invariants of this action and the
adjoint matrices are the tools of Hu, Li and Chen (A direct algorithm of
one-dimensional optimal system for the group invariant solutions, J. Math.
Phys. 56 (2015) 053504, arXiv:1411.3797), who choose the representatives by
hand. Here they are found level by level along a chain of ideals
g = W_0 > W_1 > ... > W_m = 0 (the derived series down to the perfect part,
its radical, the derived series of the radical), as in Ovsiannikov's method:
the coordinates of the quotient W_k / W_k+1 are normalized by the subgroup
fixing the coordinates of the levels above, through one-parameter subgroups
of a basis of its Lie algebra and the scalings, branching where a pivot can
vanish. Candidates of a level that are equivalent under the whole group are
merged (found numerically); homogeneous polynomial invariants of the action
on the quotient g / W_k+1 decide that two candidates are not equivalent where
they can.

Complete by construction (every generator is equivalent to a representative);
not equivalent where the invariants show it, otherwise only not found
equivalent: OptimalSystem.unseparated lists those pairs.
"""

import random
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, field
from itertools import combinations_with_replacement, pairwise
from typing import TYPE_CHECKING, Any

import mpmath
from sympy import (
    Expr,
    I,
    Matrix,
    Poly,
    Symbol,
    cancel,
    cos,
    cosh,
    exp,
    expand_complex,
    eye,
    factor_list,
    lambdify,
    prod,
    simplify,
    sin,
    sinh,
    solve,
    sympify,
    zeros,
)

if TYPE_CHECKING:
    from delierium.lie_algebra import LieAlgebra

__all__ = ["OptimalSystem", "adjoint_invariants", "adjoint_matrix", "optimal_system"]

_EPS = Symbol("epsilon", real=True)

# structure constants c[i][j][k], [X_i, X_j] = sum_k c[i][j][k] X_k
type Constants = list[list[list[Expr]]]
# a one-parameter subgroup: x_1, ..., x_n of exp(eps x) and mu of the scaling e^(mu eps)
type Move = tuple[Expr, ...]


@dataclass
class OptimalSystem:
    """Representatives of the classes of one-dimensional subalgebras, as
    combinations of the basis symbols X1, X2, ... with real parameters c1,
    c2, ... (one class for each value), and the pairs of representatives
    (indices) that are not equivalent numerically but not separated by the
    invariants either."""

    representatives: list[Expr]
    parameters: list[Symbol] = field(default_factory=list)
    unseparated: list[tuple[int, int]] = field(default_factory=list)

    def __len__(self) -> int:
        """The number of representatives.

        >>> len(OptimalSystem([Symbol('X1')]))
        1
        """
        return len(self.representatives)


def adjoint_matrix(algebra: "LieAlgebra", x: Sequence[Any], epsilon: Expr = _EPS) -> Matrix:
    """The matrix A of Ad exp(epsilon x) on the coordinates: the generator
    sum_i a_i X_i goes to sum_k (a A)_k X_k (Hydon's A(j, epsilon) for x the
    j-th unit vector).

    >>> from delierium import LieAlgebra
    >>> e = Symbol('e')
    >>> sl2 = LieAlgebra.from_structure_constants(
    ...     [
    ...         [[0, 0, 0], [1, 0, 0], [0, 2, 0]],
    ...         [[-1, 0, 0], [0, 0, 0], [0, 0, 1]],
    ...         [[0, -2, 0], [0, 0, -1], [0, 0, 0]],
    ...     ]
    ... )
    >>> adjoint_matrix(sl2, [1, 0, 0], e)
    Matrix([
    [   1,    0, 0],
    [  -e,    1, 0],
    [e**2, -2*e, 1]])
    """
    c = algebra.structure_constants
    return _move_matrix(c, (*map(sympify, x), sympify(0))).xreplace({_EPS: epsilon})


def adjoint_invariants(algebra: "LieAlgebra", max_degree: int = 4) -> list[Expr]:
    """Functionally independent homogeneous polynomial invariants of the
    adjoint action in the coordinates a1, a2, ... of sum_i a_i X_i, up to
    max_degree (Hu, Li and Chen 2.1: solve the linear PDEs of invariance).

    The Killing form of sl(2), and a4 for the symmetries of the KdV equation
    (Olver 3.3):

    >>> from delierium import LieAlgebra
    >>> sl2 = LieAlgebra.from_structure_constants(
    ...     [
    ...         [[0, 0, 0], [1, 0, 0], [0, 2, 0]],
    ...         [[-1, 0, 0], [0, 0, 0], [0, 0, 1]],
    ...         [[0, -2, 0], [0, 0, -1], [0, 0, 0]],
    ...     ]
    ... )
    >>> adjoint_invariants(sl2)
    [-4*a1*a3 + a2**2]
    """
    c = algebra.structure_constants
    n = len(c)
    a = [Symbol(f"a{i + 1}", real=True) for i in range(n)]
    return _polynomial_invariants(c, list(range(n)), a, max_degree)


def optimal_system(algebra: "LieAlgebra") -> OptimalSystem:
    """A one-dimensional optimal system of the algebra (experimental).

    The non-abelian two-dimensional algebra [X1, X2] = X1 (Hydon, Example
    10.1) and sl(2) (Example 10.2, [X1, X2] = X1, [X1, X3] = 2 X2,
    [X2, X3] = X3: X3 where the Killing form vanishes, X2 where it is
    positive, X1 + X3 where it is negative):

    >>> from delierium import LieAlgebra
    >>> a1 = LieAlgebra.from_structure_constants([[[0, 0], [1, 0]], [[-1, 0], [0, 0]]])
    >>> optimal_system(a1).representatives
    [X1, X2]
    >>> sl2 = LieAlgebra.from_structure_constants(
    ...     [
    ...         [[0, 0, 0], [1, 0, 0], [0, 2, 0]],
    ...         [[-1, 0, 0], [0, 0, 0], [0, 0, 1]],
    ...         [[0, -2, 0], [0, 0, -1], [0, 0, 0]],
    ...     ]
    ... )
    >>> optimal_system(sl2).representatives
    [X3, X2, X1 + X3]
    """
    if algebra.dimension == 0:
        return OptimalSystem([])
    classifier = _Classifier(algebra.structure_constants)
    families = classifier.run()
    symbols = algebra.basis_symbols
    names = {p: Symbol(f"c{k + 1}", real=True) for k, p in enumerate(_parameters(families))}
    representatives = [
        sum((e.xreplace(names) * X for e, X in zip(f.a, symbols, strict=True)), sympify(0))
        for f in families
    ]
    return OptimalSystem(
        representatives, list(names.values()), classifier.unseparated_pairs(families)
    )


def _parameters(families: list["_Family"]) -> list[Symbol]:
    """The parameters of the families, in order of appearance.

    >>> p = Symbol('p')
    >>> _parameters([_Family([1, p], [p]), _Family([0, 1], [])])
    [p]
    """
    seen: list[Symbol] = []
    for f in families:
        for e in f.a:
            for p in sorted(sympify(e).free_symbols, key=str):
                if p not in seen:
                    seen.append(p)
    return seen


# ---------------------------------------------------------------- linear algebra


def _bracket(c: Constants, u: Sequence[Any], w: Sequence[Any]) -> list[Expr]:
    """The coordinates of [u, w].

    >>> _bracket([[[0, 0], [1, 0]], [[-1, 0], [0, 0]]], [0, 1], [1, 0])
    [-1, 0]
    """
    n = len(c)
    return [
        sympify(sum(u[i] * w[j] * c[i][j][k] for i in range(n) for j in range(n))) for k in range(n)
    ]


def _row_space(vectors: list[list[Expr]], n: int) -> Matrix:
    """A basis (rows) of the span of the vectors.

    >>> _row_space([[1, 2], [2, 4]], 2)
    Matrix([[1, 2]])
    """
    if not vectors:
        return zeros(0, n)
    reduced, pivots = Matrix(vectors).rref(simplify=True)
    return reduced[: len(pivots), :]


def _brackets(c: Constants, U: Matrix, W: Matrix) -> Matrix:
    """A basis of [span U, span W].

    >>> _brackets([[[0, 0], [1, 0]], [[-1, 0], [0, 0]]], eye(2), eye(2))
    Matrix([[1, 0]])
    """
    return _row_space(
        [_bracket(c, list(u), list(w)) for u in U.tolist() for w in W.tolist()], len(c)
    )


def _radical(c: Constants, ideal: Matrix) -> Matrix:
    """The solvable radical of the subalgebra spanned by the rows of ideal:
    the orthogonal complement of its derived algebra in its Killing form
    (Cartan's criterion).

    >>> sl2_plus_center = [
    ...     [[0, 0, 0, 0], [1, 0, 0, 0], [0, 2, 0, 0], [0, 0, 0, 0]],
    ...     [[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]],
    ...     [[0, -2, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
    ...     [[0, 0, 0, 0]] * 4,
    ... ]
    >>> _radical(sl2_plus_center, eye(4))
    Matrix([[0, 0, 0, 1]])
    """
    n, d = len(c), ideal.rows
    gram_inverse = (ideal * ideal.T).inv()

    def coordinates(v: list[Expr]) -> list[Expr]:
        return list(Matrix([v]) * ideal.T * gram_inverse)

    rows = [list(ideal.row(i)) for i in range(d)]
    h = [[coordinates(_bracket(c, rows[i], rows[j])) for j in range(d)] for i in range(d)]
    ad = [Matrix(d, d, lambda k, j, i=i: h[i][j][k]) for i in range(d)]
    killing = Matrix(d, d, lambda i, j: (ad[i] * ad[j]).trace())
    derived = _brackets(h, eye(d), eye(d))
    if derived.rows == 0:
        return ideal
    null = (derived * killing).nullspace()
    return _row_space([list(v.T * ideal) for v in null], n)


def _ideal_chain(c: Constants) -> list[Matrix]:
    """g = W_0 > W_1 > ... > W_m = 0, ideals of g: the derived series down to
    the perfect part P, the radical of P, its derived series.

    The heat equation (Olver 3.3, Hu-Li-Chen (23)): g, its radical
    <v1, v3, v5> and the center <v3> of that:

    >>> chain = _ideal_chain(_heat())
    >>> [w.rows for w in chain]
    [6, 3, 1, 0]
    """
    n = len(c)
    chain = [eye(n)]
    current = eye(n)
    while current.rows:
        derived = _brackets(c, current, current)
        if derived.rows == current.rows:
            break
        chain.append(derived)
        current = derived
    if current.rows == 0:
        return chain
    radical = _radical(c, current)
    if radical.rows == current.rows:
        return chain
    chain.append(radical)
    current = radical
    while current.rows:
        current = _brackets(c, current, current)
        chain.append(current)
    return chain


def _adapted_basis(chain: list[Matrix], n: int) -> tuple[Matrix, list[list[int]]]:
    """The rows of a basis through the chain (a complement of W_k+1 in W_k
    for each k, the original basis vectors where possible) and the indices
    of each level.

    >>> P, levels = _adapted_basis(_ideal_chain(_heat()), 6)
    >>> [list(P.row(i)).index(1) + 1 for i in range(6)], levels
    ([2, 4, 6, 1, 5, 3], [[0, 1, 2], [3, 4], [5]])
    """
    rows: list[list[Expr]] = []
    levels = []
    units = [list(r) for r in eye(n).tolist()]
    for upper, lower in pairwise(chain):
        current = [list(r) for r in lower.tolist()]
        level = []
        # unit vectors first, then the rows of the ideal
        for r in [u for u in units if Matrix.vstack(upper, Matrix([u])).rank() == upper.rows]:
            if Matrix([*current, r]).rank() > len(current):
                current.append(r)
                level.append(r)
        for r in upper.tolist():
            if Matrix([*current, r]).rank() > len(current):
                current.append(r)
                level.append(r)
        levels.append(list(range(len(rows), len(rows) + len(level))))
        rows += level
    return Matrix(rows), levels


def _change_basis(c: Constants, P: Matrix) -> Constants:
    """The structure constants in the basis Y_i = sum_a P[i, a] X_a.

    >>> _change_basis([[[0, 0], [1, 0]], [[-1, 0], [0, 0]]], Matrix([[0, 1], [1, 0]]))
    [[[0, 0], [0, -1]], [[0, 1], [0, 0]]]
    """
    n = len(c)
    inverse = P.inv()
    out = [[[sympify(0)] * n for _ in range(n)] for _ in range(n)]
    for i in range(n):
        for j in range(n):
            v = Matrix([_bracket(c, list(P.row(i)), list(P.row(j)))]) * inverse
            for k in range(n):
                out[i][j][k] = simplify(v[k])
    return out


def _move_matrix(c: Constants, s: Move) -> Matrix:
    """a -> a exp(-eps M_x) e^(mu eps) for s = (x, mu): exponentials of
    eps, also for the hyperbolic functions, cos and sin for rotations.

    >>> _move_matrix([[[0, 0], [1, 0]], [[-1, 0], [0, 0]]], (0, 1, 0))
    Matrix([
    [exp(epsilon), 0],
    [           0, 1]])
    """
    n = len(c)
    x, mu = s[:n], s[n]
    M = Matrix(n, n, lambda i, k: sum(x[j] * c[j][i][k] for j in range(n)))
    A = (-_EPS * M).exp() if any(e != 0 for e in M) else eye(n)
    A = A.applyfunc(lambda e: simplify(e.rewrite(exp)))
    if A.has(I):
        A = A.applyfunc(lambda e: simplify(expand_complex(e.rewrite(cos))))
    A = A.applyfunc(
        lambda e: e.replace(lambda t: isinstance(t, (cosh, sinh)), lambda t: t.rewrite(exp))
    )
    return A * exp(mu * _EPS)


def _infinitesimal(c: Constants, a: Sequence[Expr], s: Move) -> list[Expr]:
    """d/d eps of a exp(-eps M_x) e^(mu eps) at 0: -a M_x + mu a.

    >>> _infinitesimal([[[0, 0], [1, 0]], [[-1, 0], [0, 0]]], [1, 1], (1, 0, 0))
    [-1, 0]
    """
    n = len(c)
    x, mu = s[:n], s[n]
    return [
        cancel(-sum(a[i] * x[j] * c[j][i][k] for i in range(n) for j in range(n)) + mu * a[k])
        for k in range(n)
    ]


# ---------------------------------------------------------------- invariants


def _polynomial_invariants(
    c: Constants, coordinates: list[int], a: list[Symbol], max_degree: int
) -> list[Expr]:
    """Functionally independent homogeneous polynomials in the a_k, k in
    coordinates (those of a quotient g / W), invariant under the adjoint
    action of g, up to max_degree.

    >>> a = [Symbol(f'a{i}') for i in range(1, 5)]
    >>> _polynomial_invariants(_kdv(), [0, 1, 2, 3], a, 3)
    [a4]
    """
    n = len(c)
    full = [a[i] if i in coordinates else sympify(0) for i in range(n)]
    variables = [a[i] for i in coordinates]
    fields = []
    for j in range(n):
        d = _infinitesimal(c, full, tuple(int(t == j) for t in range(n + 1)))
        fields.append([d[i] for i in coordinates])
    expected = len(variables) - Matrix(fields).rank(simplify=True)
    found: list[Expr] = []
    for degree in range(1, max_degree + 1):
        if len(found) == expected:
            break
        monomials = [prod(m) for m in combinations_with_replacement(variables, degree)]
        unknowns = [Symbol(f"u{t}") for t in range(len(monomials))]
        phi = sum((u * m for u, m in zip(unknowns, monomials, strict=True)), sympify(0))
        equations: list[Expr] = []
        for f in fields:
            e = sum((f[t] * phi.diff(v) for t, v in enumerate(variables)), sympify(0))
            equations += Poly(e.expand(), *variables).coeffs() if e != 0 else []
        if equations:
            system = Matrix(
                [[Poly(e, *unknowns).coeff_monomial(u) for u in unknowns] for e in equations]
            )
            null = system.nullspace()
        else:
            null = [
                Matrix([int(t == s) for t in range(len(unknowns))]) for s in range(len(unknowns))
            ]
        for v in null:
            candidate = sum((v[t] * monomials[t] for t in range(len(monomials))), sympify(0))
            candidate = Poly(candidate, *variables).primitive()[1].as_expr()
            if _independent([*found, candidate], variables):
                found.append(candidate)
    return found


def _independent(functions: list[Expr], variables: list[Symbol]) -> bool:
    """Whether the functions are functionally independent (Jacobian of full
    rank at a random point).

    >>> x, y = Symbol('x'), Symbol('y')
    >>> _independent([x * y, x**2 * y**2], [x, y]), _independent([x, y], [x, y])
    (False, True)
    """
    rng = random.Random(len(functions))
    point = {v: rng.randint(2, 50) for v in variables}
    jacobian = Matrix([[f.diff(v) for v in variables] for f in functions]).xreplace(point)
    return jacobian.rank() == len(functions)


def _separated(p: list[Expr], q: list[Expr], invariants: list[Expr], a: list[Symbol]) -> bool:
    """Whether no real lambda != 0 gives phi(q) = lambda**deg(phi) phi(p) for
    all the (homogeneous) invariants phi: p and q are not equivalent.

    >>> a1, a2, a3 = a = [Symbol('a1'), Symbol('a2'), Symbol('a3')]
    >>> killing = a2**2 - 4 * a1 * a3
    >>> (
    ...     _separated([1, 0, 1], [0, 1, 0], [killing], a),
    ...     _separated([1, 0, 0], [0, 0, 2], [killing], a),
    ... )
    (True, False)
    """
    pairs = []
    for phi in invariants:
        d = Poly(phi, *a).total_degree()
        u = phi.xreplace(dict(zip(a, p, strict=True)))
        v = phi.xreplace(dict(zip(a, q, strict=True)))
        if not (u.is_number and v.is_number):
            continue
        if (u == 0) != (v == 0):
            return True
        if u != 0:
            if d % 2 == 0 and (u > 0) != (v > 0):
                return True
            pairs.append((d, v / u))
    # lambda**d = r for all pairs: |lambda| from one, then check the others
    for d, r in pairs:
        for e, s in pairs:
            if simplify(abs(r) ** e - abs(s) ** d) != 0:
                return True
    return False


# ---------------------------------------------------------------- families


@dataclass
class _Family:
    """The generators sum a_k Y_k (a in the parameters, which are free real
    numbers) with the expressions nonzero != 0."""

    a: list[Expr]
    params: list[Symbol]
    nonzero: list[Expr] = field(default_factory=list)


def _substitute(f: _Family, sub: dict[Symbol, Expr]) -> _Family | None:
    """f with parameter values; None if a condition fails.

    >>> p, q = Symbol('p'), Symbol('q')
    >>> _substitute(_Family([p, q], [p, q], [q]), {q: 0}) is None
    True
    """
    nonzero = []
    for e in f.nonzero:
        e = cancel(sympify(e).xreplace(sub))
        if e == 0:
            return None
        if not e.is_number:
            nonzero.append(e)
    a = [cancel(sympify(e).xreplace(sub)) for e in f.a]
    return _Family(a, [p for p in f.params if p not in sub], nonzero)


def _zero_branch(f: _Family, e: Expr) -> _Family | None:
    """f with the condition e = 0 (solved for its last parameter).

    >>> p, q = Symbol('p'), Symbol('q')
    >>> _zero_branch(_Family([p, q], [p, q]), p - 2 * q).a
    [p, p/2]
    """
    free = [p for p in f.params if e.has(p)]
    if not free:
        return f if e == 0 else None
    solutions = solve(e, free[-1], dict=True)
    if len(solutions) != 1:
        raise NotImplementedError(f"optimal system: condition {e} = 0 (#44)")
    return _substitute(f, solutions[0])


def _negated(f: _Family) -> _Family:
    """-f, the same subalgebra.

    >>> _negated(_Family([1, -2], [])).a
    [-1, 2]
    """
    return _Family([-e for e in f.a], f.params, f.nonzero)


class _Classifier:
    """Normalization level by level (see the module docstring), in the
    basis adapted to the chain of ideals."""

    def __init__(self, c: Constants) -> None:
        """The adapted basis and its structure constants.

        >>> _Classifier(_kdv()).levels
        [[0], [1, 2], [3]]
        """
        self.n = len(c)
        self.P, self.levels = _adapted_basis(_ideal_chain(c), self.n)
        self.c = _change_basis(c, self.P)
        self.full: list[Move] = [
            tuple(sympify(int(i == j)) for i in range(self.n + 1)) for j in range(self.n + 1)
        ]
        self._matrices: dict[Move, Matrix] = {}
        self._invariants: dict[int, list[Expr]] = {}
        self.a = [Symbol(f"a{i + 1}", real=True) for i in range(self.n)]
        self.counter = 0

    def matrix(self, s: Move) -> Matrix:
        """The (cached) matrix of the move s.

        >>> _Classifier(_kdv()).matrix((0, 0, 0, 0, 1))
        Matrix([
        [exp(epsilon),            0,            0,            0],
        [           0, exp(epsilon),            0,            0],
        [           0,            0, exp(epsilon),            0],
        [           0,            0,            0, exp(epsilon)]])
        """
        if s not in self._matrices:
            self._matrices[s] = _move_matrix(self.c, s)
        return self._matrices[s]

    def run(self) -> list[_Family]:
        """The representatives, in the original basis.

        >>> [f.a for f in _Classifier(_kdv()).run()]  # doctest: +NORMALIZE_WHITESPACE
        [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 1, 1, 0], [0, 1, -1, 0], [0, 0, 0, 1]]
        """
        params = [Symbol(f"p{i + 1}", real=True) for i in range(self.n)]
        families = self.level(_Family(list(params), list(params)), 0, list(self.full))
        return [
            _Family([simplify(e) for e in Matrix([f.a]) * self.P], f.params, f.nonzero)
            for f in families
        ]

    def level(self, f: _Family, k: int, stab: list[Move]) -> list[_Family]:
        """The representatives of f, normal in the levels from k on; stab
        fixes the coordinates of the levels above.

        >>> cl = _Classifier(_kdv())
        >>> [g.a for g in cl.level(_Family([1, 0, 0, Symbol('p')], [Symbol('p')]), 1, [])]
        [[1, 0, 0, p]]
        """
        if k == len(self.levels):
            return [f] if any(e != 0 for e in f.a) else []
        index = self.levels[k]
        above = [i for level in self.levels[:k] for i in level]
        candidates = self.normalize(f, index, stab)
        candidates.sort(key=lambda g: sum(1 for i in index if g.a[i] != 0))
        candidates = self.merge(candidates, above + index)
        out = []
        for g in candidates:
            for h, s in self.stabilizer(g, above + index, stab):
                out += self.level(h, k + 1, s)
        return out

    # ---------------------------------------------------------- normalization

    def normalize(self, f: _Family, index: list[int], stab: list[Move]) -> list[_Family]:
        """Families covering f, normal in the coordinates index: killed by
        moves linear in eps or rotations, scaled to +-1.

        >>> cl = _Classifier(_kdv())
        >>> p, q = Symbol('p'), Symbol('q')
        >>> [g.a for g in cl.normalize(_Family([0, p, q, 0], [p, q]), [1, 2], cl.full)]
        [[0, 1, 1, 0], [0, 1, -1, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 0]]

        The last one is not lost: the deeper levels are free.
        """
        for k, pivot, A in self.kills(f, index, stab):
            pk = f.a[k]
            condition = cancel(pivot.xreplace({pk: 0})) if pk in f.params else pivot
            if condition == 0:
                continue
            kept = [e for e in f.nonzero if not e.has(pk) and self.invariant_under(f, e, A)]
            killed = _Family(
                [sympify(0) if i == k else f.a[i] for i in range(self.n)],
                [p for p in f.params if p != pk],
                kept + ([condition] if not condition.is_number else []),
            )
            out = self.normalize(killed, index, stab)
            if not pivot.is_number:
                for factor, _ in factor_list(pivot)[1]:
                    g = _zero_branch(f, factor)
                    if g is not None:
                        out += self.normalize(g, index, stab)
            return out
        for k, A in self.rotations(f, index, stab):
            pk = f.a[k]
            rotated = _Family(
                [sympify(0) if i == k else f.a[i] for i in range(self.n)],
                [p for p in f.params if p != pk],
                [e for e in f.nonzero if not e.has(pk) and self.invariant_under(f, e, A)],
            )
            return self.normalize(rotated, index, stab)
        return self.scale(f, index, stab)

    def invariant_under(self, f: _Family, e: Expr, A: Matrix) -> bool:
        """Whether the move with matrix A leaves e unchanged on f.

        >>> cl = _Classifier(_kdv())
        >>> p = Symbol('p')
        >>> cl.invariant_under(_Family([p, 0, 0, 1], [p]), p, cl.matrix((1, 0, 0, 0, 0)))
        True
        """
        b = Matrix([f.a]) * A
        values = {x: b[i] for i, x in enumerate(f.a) if x in f.params}
        return simplify(e.xreplace(values) - e) == 0

    def kills(
        self, f: _Family, index: list[int], stab: list[Move]
    ) -> list[tuple[int, Expr, Matrix]]:
        """(k, pivot, A): a move with matrix A makes coordinate k linear in
        eps with the coefficient pivot, keeping the zeros of the level;
        pivots invariant under all of stab first (their condition survives),
        then moves changing many coordinates (the others do not undo them).

        >>> cl = _Classifier(_kdv())
        >>> p = [Symbol(f'p{i}') for i in range(4)]
        >>> [(k, pivot) for k, pivot, _ in cl.kills(_Family(p, p), [0], cl.full)]
        []
        """
        a = Matrix([f.a])
        found = []
        for s in stab:
            A = self.matrix(s)
            b = (a * A).applyfunc(cancel)
            if any(f.a[i] == 0 and simplify(b[i]) != 0 for i in index):
                continue
            changed = sum(
                1 for i in range(self.n) for j in range(self.n) if i != j and A[i, j] != 0
            )
            for k in index:
                if f.a[k] == 0 or not b[k].is_polynomial(_EPS):
                    continue
                poly = Poly(b[k], _EPS)
                if poly.degree() == 1:
                    pivot = cancel(poly.coeff_monomial(_EPS))
                    invariant = all(self.invariant_under(f, pivot, self.matrix(t)) for t in stab)
                    found.append((not invariant, -changed, k, pivot, A))
        found.sort(key=lambda m: (m[0], m[1]))
        return [(k, pivot, A) for _, _, k, pivot, A in found]

    def rotations(
        self, f: _Family, index: list[int], stab: list[Move]
    ) -> Iterator[tuple[int, Matrix]]:
        """(k, A): a move rotates coordinate k (cos and sin of eps), keeping
        the zeros of the level; a rotation can always make it 0.

        >>> cl = _Classifier(_so3())
        >>> p = [Symbol(f'p{i}') for i in range(3)]
        >>> next(cl.rotations(_Family(p, p), [0, 1, 2], cl.full))[0]
        1
        """
        a = Matrix([f.a])
        for s in stab:
            A = self.matrix(s)
            if not A.has(cos):
                continue
            b = (a * A).applyfunc(simplify)
            if any(f.a[i] == 0 and b[i] != 0 for i in index):
                continue
            for k in index:
                if f.a[k] != 0 and b[k].has(cos, sin) and not b[k].has(exp):
                    yield k, A

    def scale(self, f: _Family, index: list[int], stab: list[Move]) -> list[_Family]:
        """Parameters of the level set to +-1 (or 0) where the moves acting
        by exponentials on it can; numbers of the level stay fixed.

        >>> cl = _Classifier(_kdv())
        >>> p = Symbol('p')
        >>> [g.a for g in cl.scale(_Family([p, 0, 0, 0], [p]), [0], cl.full)]
        [[1, 0, 0, 0], [0, 0, 0, 0]]
        """
        chosen = self.scalable(f, index, stab)
        if not chosen:
            return [f]
        p = f.a[chosen[0]]
        out = []
        # the factor -1 is always free (the scalings are positive): -1 only
        # needs a branch of its own if a nonzero number is already fixed
        signs = (1, -1) if any(e != 0 and e.is_number for e in f.a) else (1,)
        for sign in signs:
            g = _substitute(f, {p: sympify(sign)})
            if g is not None:
                out += self.normalize(g, index, stab)
        if p not in f.nonzero:
            g = _zero_branch(f, p)
            if g is not None:
                out += self.normalize(g, index, stab)
        return out

    def scalable(self, f: _Family, index: list[int], stab: list[Move]) -> list[int]:
        """The coordinates of the level that are parameters and that the
        scaling moves change while keeping its numbers.

        >>> cl = _Classifier(_kdv())
        >>> p = Symbol('p')
        >>> cl.scalable(_Family([p, 0, 0, 0], [p]), [0], cl.full)
        [0]
        """
        a = Matrix([f.a])
        weights = []
        for s in stab:
            w = self.exponents(f, a * self.matrix(s), index)
            if w is not None and any(e != 0 for e in w):
                weights.append(w)
        if not weights:
            return []
        position = {i: t for t, i in enumerate(index)}
        directions = eye(len(weights))
        support = [i for i in index if f.a[i] != 0]
        fixed = [i for i in support if f.a[i] not in f.params]
        if fixed:
            null = Matrix([[w[position[i]] for w in weights] for i in fixed]).nullspace()
            if not null:
                return []
            directions = Matrix.hstack(*null)
        return [
            i
            for i in support
            if f.a[i] in f.params
            and (Matrix([[w[position[i]] for w in weights]]) * directions).rank() > 0
        ]

    def exponents(self, f: _Family, b: Matrix, index: list[int]) -> list[Expr] | None:
        """w with b_i = e^(w_i eps) a_i on the level, None if the move does
        not act so.

        >>> cl = _Classifier(_kdv())
        >>> p = Symbol('p')
        >>> f = _Family([p, 0, 0, 0], [p])
        >>> cl.exponents(f, Matrix([f.a]) * cl.matrix((0, 0, 0, 0, 1)), [0])
        [1]
        """
        w = []
        for i in index:
            if f.a[i] == 0:
                if simplify(b[i]) != 0:
                    return None
                w.append(sympify(0))
                continue
            r = simplify(b[i] / f.a[i])
            if r == 1:
                w.append(sympify(0))
            elif (
                r.func == exp
                and r.args[0].is_polynomial(_EPS)
                and Poly(r.args[0], _EPS).degree() == 1
                and not r.args[0].free_symbols - {_EPS}
            ):
                w.append(Poly(r.args[0], _EPS).coeff_monomial(_EPS))
            else:
                return None
        return w

    # ---------------------------------------------------------- stabilizer

    def stabilizer(
        self, f: _Family, fixed: list[int], stab: list[Move]
    ) -> list[tuple[_Family, list[Move]]]:
        """The moves of span(stab) fixing the coordinates fixed of f, with
        branches where the parameters change the rank.

        >>> cl = _Classifier(_kdv())
        >>> f = _Family([1, 0, 0, Symbol('p')], [Symbol('p')])
        >>> [len(s) for _, s in cl.stabilizer(f, [0], cl.full)]
        [4]
        """
        columns = [[_infinitesimal(self.c, f.a, s)[i] for i in fixed] for s in stab]
        A = Matrix(columns).T
        out = []
        for g, null in _nullspace_cases(A, f):
            moves = []
            for v in null:
                combination = [
                    cancel(sum(v[t] * stab[t][i] for t in range(len(stab))))
                    for i in range(self.n + 1)
                ]
                lead = next(e for e in combination if e != 0)
                moves.append(tuple(cancel(e / lead) for e in combination))
            out.append((g, moves))
        return out

    # ---------------------------------------------------------- merging

    def merge(self, candidates: list[_Family], coordinates: list[int]) -> list[_Family]:
        """The candidates without those equivalent (on coordinates) to an
        earlier one.

        >>> cl = _Classifier(_sl2())
        >>> [g.a for g in cl.merge([_Family([0, 0, 1], []), _Family([1, 0, 0], [])], [0, 1, 2])]
        [[0, 0, 1]]
        """
        keep: list[_Family] = []
        for g in candidates:
            if any(not sympify(g.a[i]).is_number for i in coordinates):
                keep.append(g)
                continue
            numeric = [h for h in keep if all(sympify(h.a[i]).is_number for i in coordinates)]
            if not any(
                self.equivalent(g, h, coordinates) or self.equivalent(g, _negated(h), coordinates)
                for h in numeric
            ):
                keep.append(g)
        return keep

    def quotient_invariants(self, coordinates: list[int]) -> list[Expr]:
        """The invariants of the action on the quotient with these
        coordinates (cached by their number).

        >>> _Classifier(_kdv()).quotient_invariants([0])
        [a1]
        """
        key = len(coordinates)
        if key not in self._invariants:
            self._invariants[key] = _polynomial_invariants(self.c, coordinates, self.a, 4)
        return self._invariants[key]

    def equivalent(self, g: _Family, h: _Family, coordinates: list[int], tries: int = 12) -> bool:
        """Whether g is mapped to h on the coordinates by the group: not if
        the invariants separate them, else searched numerically (Levenberg-
        Marquardt on a word of one-parameter subgroups and the scaling).

        >>> cl = _Classifier(_sl2())
        >>> cl.equivalent(_Family([0, 0, 1], []), _Family([1, 0, 0], []), [0, 1, 2])
        True
        >>> cl.equivalent(_Family([1, 0, 1], []), _Family([1, 0, 0], []), [0, 1, 2])
        False
        """
        if all(simplify(g.a[i] - h.a[i]) == 0 for i in coordinates):
            return True
        if all(g.a[i] == 0 for i in coordinates) or all(h.a[i] == 0 for i in coordinates):
            return False
        invariants = self.quotient_invariants(coordinates)
        a = [self.a[i] for i in coordinates]
        if _separated([g.a[i] for i in coordinates], [h.a[i] for i in coordinates], invariants, a):
            return False
        return _numerically_equivalent(
            [self.matrix(s) for s in self.full * 2],
            [g.a[i] for i in range(self.n)],
            {i: h.a[i] for i in coordinates},
            tries,
        )

    def unseparated_pairs(self, families: list[_Family]) -> list[tuple[int, int]]:
        """Pairs of numeric representatives (original basis) that the
        invariants do not separate on any quotient g / W_k+1 (an equivalence
        of generators is one of their images in the quotient; a zero image
        is only equivalent to zero).

        >>> cl = _Classifier(_kdv())
        >>> cl.unseparated_pairs([_Family([0, 1, 1, 0], []), _Family([0, 1, -1, 0], [])])
        [(0, 1)]
        >>> cl.unseparated_pairs([_Family([0, 1, 1, 0], []), _Family([0, 0, 0, 1], [])])
        []
        """
        inverse = self.P.inv()
        vectors = [list(Matrix([f.a]) * inverse) for f in families]
        out = []
        for i, p in enumerate(vectors):
            for j in range(i + 1, len(vectors)):
                q = vectors[j]
                if any(not sympify(e).is_number for e in p + q):
                    continue
                if not any(self.separated_on(p, q, k) for k in range(len(self.levels))):
                    out.append((i, j))
        return out

    def separated_on(self, p: list[Expr], q: list[Expr], k: int) -> bool:
        """Whether the images of p and q (adapted basis) in g / W_k+1 are
        not equivalent by their invariants.

        >>> cl = _Classifier(_kdv())
        >>> cl.separated_on([1, 0, 0, 0], [0, 1, 0, 0], 0)
        True
        """
        coordinates = [i for level in self.levels[: k + 1] for i in level]
        u, v = [p[i] for i in coordinates], [q[i] for i in coordinates]
        if all(e == 0 for e in u) != all(e == 0 for e in v):
            return True
        a = [self.a[i] for i in coordinates]
        return _separated(u, v, self.quotient_invariants(coordinates), a)


def _nullspace_cases(A: Matrix, f: _Family) -> list[tuple[_Family, list[Matrix]]]:
    """Nullspaces of A for f and for the special parameter values where a
    pivot vanishes (fraction free elimination).

    >>> p = Symbol('p')
    >>> [
    ...     (g.a, len(null))
    ...     for g, null in _nullspace_cases(Matrix([[p, 1], [0, 0]]), _Family([p], [p]))
    ... ]
    [([p], 1)]
    >>> [(g.a, len(null)) for g, null in _nullspace_cases(Matrix([[p, 0]]), _Family([p], [p]))]
    [([p], 1), ([0], 2)]
    """
    M = [[cancel(e) for e in row] for row in A.tolist()]
    rows, cols = A.shape
    special: list[Expr] = []
    done_rows: list[int] = []
    done_cols: list[int] = []
    while True:
        entries = [
            (i, j)
            for i in range(rows)
            if i not in done_rows
            for j in range(cols)
            if j not in done_cols and M[i][j] != 0
        ]
        if not entries:
            break
        # a numeric pivot where there is one: no special values
        i, j = next(((i, j) for i, j in entries if M[i][j].is_number), entries[0])
        pivot = M[i][j]
        if not pivot.is_number:
            special.append(pivot)
        for t in range(rows):
            if t != i and M[t][j] != 0:
                factor = M[t][j]
                M[t] = [cancel(pivot * x - factor * y) for x, y in zip(M[t], M[i], strict=True)]
        done_rows.append(i)
        done_cols.append(j)
    out = [(f, A.applyfunc(cancel).nullspace(simplify=True))]
    for pivot in special:
        for factor, _ in factor_list(pivot)[1]:
            if factor.is_number or any(cancel(factor - e) == 0 for e in f.nonzero):
                continue
            g = _zero_branch(f, factor)
            if g is not None:
                out += _nullspace_cases(A.xreplace(_parameter_values(f, g)), g)
    return out


def _parameter_values(f: _Family, g: _Family) -> dict[Symbol, Expr]:
    """The values of the parameters of f that are no parameters of g.

    >>> p, q = Symbol('p'), Symbol('q')
    >>> _parameter_values(_Family([p, q], [p, q]), _Family([p, 2 * p], [p]))
    {q: 2*p}
    """
    return {x: y for x, y in zip(f.a, g.a, strict=True) if x in f.params and x not in g.params}


def _numerically_equivalent(
    matrices: list[Matrix], start: list[Expr], target: dict[int, Expr], tries: int
) -> bool:
    """Whether start * A_1(e_1) * ... * A_m(e_m) has the target values for
    some real e (Levenberg-Marquardt from random starts).

    >>> e = Symbol('epsilon', real=True)
    >>> A = Matrix([[1, e], [0, 1]])
    >>> _numerically_equivalent([A], [1, 0], {1: 3}, 4)
    True
    """
    unknowns = [Symbol(f"e{t}", real=True) for t in range(len(matrices))]
    product = Matrix([start])
    for A, e in zip(matrices, unknowns, strict=True):
        product = product * A.xreplace({_EPS: e})
    residuals = [product[i] - v for i, v in target.items()]
    F = lambdify([unknowns], residuals, "mpmath")
    m = len(unknowns)
    rng = random.Random(1)
    with mpmath.workdps(20):

        def residual(x: Any) -> Any:
            try:
                return mpmath.matrix(F(list(x)))
            except (OverflowError, ValueError, ZeroDivisionError):
                return None

        for _ in range(tries):
            x = mpmath.matrix([rng.uniform(-2, 2) for _ in range(m)])
            r = residual(x)
            if r is not None and _levenberg_marquardt(residual, x, r, m):
                return True
    return False


def _levenberg_marquardt(residual: Any, x: Any, r: Any, m: int) -> bool:
    """Whether the iteration from x reaches a zero of residual.

    >>> with mpmath.workdps(20):
    ...     f = lambda x: mpmath.matrix([x[0] ** 2 - 4])
    ...     _levenberg_marquardt(f, mpmath.matrix([1]), f(mpmath.matrix([1])), 1)
    True
    """
    lam = mpmath.mpf(1)
    for _ in range(80):
        norm = mpmath.norm(r)
        if norm < mpmath.mpf(10) ** -14:
            return True
        J = _jacobian(residual, x, r, m)
        if J is None:
            return False
        for _ in range(30):
            JJ = J * J.T
            for q in range(JJ.rows):
                JJ[q, q] += lam
            try:
                y = x - J.T * mpmath.lu_solve(JJ, r)
            except ZeroDivisionError:
                return False
            ry = residual(y)
            # bounded: far out, the scalings come arbitrarily close to the
            # boundary of the orbit (0 for instance)
            if ry is not None and mpmath.norm(ry) < norm and mpmath.norm(y) < 30:
                x, r = y, ry
                lam = max(lam / 10, mpmath.mpf(10) ** -25)
                break
            lam *= 10
        else:
            return False
    return False


def _jacobian(residual: Any, x: Any, r: Any, m: int) -> Any:
    """The Jacobian of residual at x (r = residual(x)) by forward
    differences, None if residual fails near x.

    >>> with mpmath.workdps(20):
    ...     f = lambda x: mpmath.matrix([x[0] * x[1]])
    ...     J = _jacobian(f, mpmath.matrix([2, 3]), f(mpmath.matrix([2, 3])), 2)
    >>> [round(float(J[0, t]), 6) for t in range(2)]
    [3.0, 2.0]
    """
    h = mpmath.mpf(10) ** -12
    J = mpmath.matrix(len(r), m)
    for t in range(m):
        y = x.copy()
        y[t] += h
        ry = residual(y)
        if ry is None:
            return None
        for q, (value, base) in enumerate(zip(ry, r, strict=True)):
            J[q, t] = (value - base) / h
    return J


# ---------------------------------------------------------------- examples


def _constants(n: int, table: dict[tuple[int, int], dict[int, int]]) -> Constants:
    """Structure constants from [X_i, X_j] = sum_k table[i, j][k] X_k
    (indices from 1, i < j).

    >>> _constants(2, {(1, 2): {1: 1}})
    [[[0, 0], [1, 0]], [[-1, 0], [0, 0]]]
    """
    c = [[[sympify(0)] * n for _ in range(n)] for _ in range(n)]
    for (i, j), value in table.items():
        for k, x in value.items():
            c[i - 1][j - 1][k - 1] = sympify(x)
            c[j - 1][i - 1][k - 1] = -sympify(x)
    return c


def _sl2() -> Constants:
    """sl(2), Hydon's basis: [X1, X2] = X1, [X1, X3] = 2 X2, [X2, X3] = X3.

    >>> _sl2()[0][2]
    [0, 2, 0]
    """
    return _constants(3, {(1, 2): {1: 1}, (1, 3): {2: 2}, (2, 3): {3: 1}})


def _so3() -> Constants:
    """so(3): [X1, X2] = X3, [X2, X3] = X1, [X3, X1] = X2.

    >>> _so3()[0][1]
    [0, 0, 1]
    """
    return _constants(3, {(1, 2): {3: 1}, (2, 3): {1: 1}, (1, 3): {2: -1}})


def _kdv() -> Constants:
    """The symmetries d_x, d_t, t d_x + d_u, x d_x + 3 t d_t - 2 u d_u of the
    KdV equation (Olver 3.3).

    >>> _kdv()[1][3]
    [0, 3, 0, 0]
    """
    return _constants(4, {(1, 4): {1: 1}, (2, 3): {1: 1}, (2, 4): {2: 3}, (3, 4): {3: -2}})


def _heat() -> Constants:
    """The six-dimensional symmetry algebra of the heat equation (Olver 3.3,
    Hu-Li-Chen Table 3).

    >>> _heat()[1][5]
    [0, 0, -2, 4, 0, 0]
    """
    return _constants(
        6,
        {
            (1, 4): {1: 1},
            (1, 5): {3: -1},
            (1, 6): {5: 2},
            (2, 4): {2: 2},
            (2, 5): {1: 2},
            (2, 6): {4: 4, 3: -2},
            (4, 5): {5: 1},
            (4, 6): {6: 2},
        },
    )
