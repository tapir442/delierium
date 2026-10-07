"""Lie algebras of symmetry generators: commutators, structure constants and
the structure derived from them (#11).

A generator is a vector field X = xi^1 d/dz_1 + ... + xi^n d/dz_n on the
coordinates z (independent variables first, then the dependent ones, as in
the symmetry catalogue). From a basis X_1, ..., X_r of a Lie algebra,
`LieAlgebra` computes the structure constants c_ij^k of

    [X_i, X_j] = sum_k c_ij^k X_k

and from them the commutator table, the derived and lower central series,
solvability, nilpotency, the center and the Killing form (Baumann 2.2,
Hydon 5.2, Bluman-Anco 2.5, Schwarz 3.4). The generators can be given; they do
not have to come from delierium (#9).
"""

import random
from collections.abc import Iterable, Sequence
from functools import cached_property, reduce
from itertools import product
from math import prod
from typing import TYPE_CHECKING, Any

from sympy import (
    Derivative,
    Dummy,
    Expr,
    Function,
    Matrix,
    Pow,
    Rational,
    Symbol,
    binomial,
    cancel,
    cos,
    cot,
    count_ops,
    csc,
    denom,
    expand_power_exp,
    expand_trig,
    ilcm,
    nan,
    oo,
    sec,
    simplify,
    sin,
    sympify,
    tan,
    together,
    zeros,
    zoo,
)
from sympy import exp as exp_
from sympy.core.function import AppliedUndef
from sympy.functions.elementary.hyperbolic import HyperbolicFunction
from sympy.functions.elementary.trigonometric import TrigonometricFunction
from sympy.polys.matrices import DomainMatrix

if TYPE_CHECKING:
    from delierium.janet_basis import JanetBasis
    from delierium.lie_algebra_types import LieAlgebraType

__all__ = [
    "LieAlgebra",
    "NotClosedError",
    "VectorField",
]


class NotClosedError(ValueError):
    """The commutator of two generators is not in their span."""


class VectorField:
    """X = sum_i coefficients[i] d/dcoordinates[i].

    >>> x, y = Symbol('x'), Symbol('y')
    >>> rotation = VectorField([-y, x], [x, y])
    >>> rotation(x**2 + y**2)
    0
    >>> rotation
    -y*D(x) + x*D(y)
    """

    def __init__(self, coefficients: Sequence[Any], coordinates: Sequence[Symbol]) -> None:
        if len(coefficients) != len(coordinates):
            raise ValueError("one coefficient per coordinate")
        self.coefficients = tuple(sympify(c) for c in coefficients)
        self.coordinates = tuple(coordinates)

    def __call__(self, f: Any) -> Expr:
        """X applied to the function f of the coordinates."""
        f = sympify(f)
        return sum(
            (c * f.diff(z) for c, z in zip(self.coefficients, self.coordinates, strict=True)),
            sympify(0),
        )

    def commutator(self, other: "VectorField") -> "VectorField":
        """[X, Y] with the components X(Y^k) - Y(X^k).

        >>> x, y = Symbol('x'), Symbol('y')
        >>> VectorField([1, 0], [x, y]).commutator(VectorField([x, y], [x, y]))
        D(x)
        """
        if self.coordinates != other.coordinates:
            raise ValueError("vector fields on different coordinates")
        return VectorField(
            [
                cancel(self(b) - other(a))
                for a, b in zip(self.coefficients, other.coefficients, strict=True)
            ],
            self.coordinates,
        )

    def is_zero(self) -> bool:
        return all(simplify(c) == 0 for c in self.coefficients)

    def __repr__(self) -> str:
        terms = [
            f"{'' if c == 1 else ('-' if c == -1 else f'{c}*')}D({z})"
            for c, z in zip(self.coefficients, self.coordinates, strict=True)
            if c != 0
        ]
        return " + ".join(terms).replace("+ -", "- ") if terms else "0"


class _RationalAtPoints:
    """Writes the transcendental functions of a coordinate z in new symbols,
    shared by all coefficients of one linear system:

    - sin(k z), cos(k z), tan, cot, sec, csc (k an integer):
      sin(z) = 2 t/(1 + t**2), cos(z) = (1 - t**2)/(1 + t**2);
    - exp((k + c m) z) and the hyperbolic functions: exp(k z) w**c, w for
      exp(m z);
    - z**(k + c m), m symbolic (a parameter): z**k p**c, p for z**m;

    k a number, c an integer, m free of the coordinates. z, sin(z), cos(z),
    exp(m z), z**m are algebraically independent apart from sin**2 + cos**2 = 1
    (for generic parameters), which the parametrization keeps: an identity in
    z holds iff it holds for z, t, w, p independent. So at random rational
    z, t, w, p the values are rational and every identity among them is kept
    (sin(x)**2*cos(x) + cos(x)**3 = cos(x), sin(2 x) = 2 sin(x) cos(x),
    x**(2 a) = (x**a)**2, x**(a + 1) = x x**a), where independent symbols for
    sin(5/3), cos(5/3) or (8/5)**a, (8/5)**(2 a) would lose them.

    >>> from sympy import exp
    >>> x, a = Symbol('x'), Symbol('a')
    >>> r = _RationalAtPoints([x])
    >>> r(sin(2 * x) + x ** (a + 1) * exp(-2 * a * x))
    _p_x_a*x/_w_x_a**2 + 4*_t_x*(1 - _t_x**2)/(_t_x**2 + 1)**2
    """

    def __init__(self, coordinates: Sequence[Symbol]) -> None:
        self.coordinates = set(coordinates)
        self.symbols: dict[tuple[Any, ...], Symbol] = {}

    def symbol(self, *key: Any) -> Symbol:
        if key not in self.symbols:
            self.symbols[key] = Dummy("_".join(map(str, key)))
        return self.symbols[key]

    def split(self, q: Expr) -> tuple[Expr, Expr, Expr] | None:
        """(k, c, m) with q = k + c m, k a number, c an integer, m free of
        the coordinates and with a positive leading coefficient (so that
        x**(1 - a) and x**(2 - a) share the symbol of x**a), or None."""
        k, rest = q.as_coeff_Add()
        c, m = rest.as_coeff_Mul()
        if not c.is_Integer or m.is_Number or m.free_symbols & self.coordinates:
            return None
        if m.could_extract_minus_sign():
            c, m = -c, -m
        return k, c, m

    def __call__(self, e: Expr) -> Expr:
        if not e.has(TrigonometricFunction, HyperbolicFunction, exp_, Pow):
            return e
        e = e.replace(lambda f: isinstance(f, HyperbolicFunction), lambda f: f.rewrite(exp_))
        for f, by in (
            (tan, lambda u: sin(u) / cos(u)),
            (cot, lambda u: cos(u) / sin(u)),
            (sec, lambda u: 1 / cos(u)),
            (csc, lambda u: 1 / sin(u)),
        ):
            e = e.replace(lambda g, f=f: isinstance(g, f), lambda g, by=by: by(g.args[0]))
        e = expand_power_exp(expand_trig(e))
        for z in self.coordinates:
            if e.has(sin(z), cos(z)):
                t = self.symbol("t", z)
                e = e.xreplace({sin(z): 2 * t / (1 + t**2), cos(z): (1 - t**2) / (1 + t**2)})
            e = e.replace(
                lambda g, z=z: self._exponent_of(g, z) is not None,
                lambda g, z=z: self._exponential(g, z),
            )
            e = e.replace(
                lambda g, z=z: isinstance(g, Pow) and g.base == z and self.split(g.exp) is not None,
                lambda g, z=z: self._power(g, z),
            )
        return e

    def _exponent_of(self, g: Expr, z: Symbol) -> Expr | None:
        """q for g = exp(q z), q an integer or k + c m, else None."""
        if not isinstance(g, exp_):
            return None
        q = g.args[0] / z
        if q.free_symbols & self.coordinates or not (q.is_Integer or self.split(q)):
            return None
        return q

    def _exponential(self, g: Expr, z: Symbol) -> Expr:
        q = self._exponent_of(g, z)
        assert q is not None
        if q.is_Integer:
            return self.symbol("w", z, 1) ** q
        k, c, m = self.split(q)  # type: ignore[misc]
        return exp_(k * z) * self.symbol("w", z, m) ** c

    def _power(self, g: Expr, z: Symbol) -> Expr:
        k, c, m = self.split(g.exp)  # type: ignore[misc]
        return z**k * self.symbol("p", z, m) ** c


class LieAlgebra:
    """The Lie algebra spanned by linearly independent vector fields.

    The rotations of the plane and of space:

    >>> x, y, z = Symbol('x'), Symbol('y'), Symbol('z')
    >>> so3 = LieAlgebra([[0, -z, y], [z, 0, -x], [-y, x, 0]], [x, y, z])
    >>> so3.commutator_table()
    Matrix([
    [  0, -X3,  X2],
    [ X3,   0, -X1],
    [-X2,  X1,   0]])
    >>> so3.is_solvable(), so3.is_semisimple()
    (False, True)

    The symmetries d/dx, x d/dx + y d/dy of y'' = y'**2 / y (dimension 2 is
    always solvable):

    >>> a = LieAlgebra([[1, 0], [x, y]], [x, y])
    >>> a.derived_series()
    [2, 1, 0]
    >>> a.is_solvable(), a.is_abelian(), a.is_nilpotent()
    (True, False, False)
    """

    def __init__(self, generators: Sequence[Any], coordinates: Sequence[Symbol]) -> None:
        self.coordinates = tuple(coordinates)
        self.generators = [
            g if isinstance(g, VectorField) else VectorField(g, self.coordinates)
            for g in generators
        ]
        self.dimension = len(self.generators)
        self.basis_symbols = [Symbol(f"X{i + 1}") for i in range(self.dimension)]

    @classmethod
    def from_structure_constants(cls, c: Sequence[Sequence[Sequence[Any]]]) -> "LieAlgebra":
        """The abstract Lie algebra with [X_i, X_j] = sum_k c[i][j][k] X_k
        (no generators as vector fields).

        >>> h = LieAlgebra.from_structure_constants(
        ...     [
        ...         [[0, 0, 0], [0, 0, 1], [0, 0, 0]],
        ...         [[0, 0, -1], [0, 0, 0], [0, 0, 0]],
        ...         [[0, 0, 0], [0, 0, 0], [0, 0, 0]],
        ...     ]
        ... )
        >>> h.commutator_table()
        Matrix([
        [  0, X3, 0],
        [-X3,  0, 0],
        [  0,  0, 0]])
        >>> h.is_nilpotent(), h.is_abelian()
        (True, False)
        """
        r = len(c)
        constants = [[[sympify(c[i][j][k]) for k in range(r)] for j in range(r)] for i in range(r)]
        if any(
            constants[i][j][k] != -constants[j][i][k]
            for i in range(r)
            for j in range(r)
            for k in range(r)
        ):
            raise ValueError("structure constants must be antisymmetric: c[i][j] = -c[j][i]")
        algebra = cls([], [])
        algebra.dimension = r
        algebra.basis_symbols = [Symbol(f"X{i + 1}") for i in range(r)]
        algebra.__dict__["structure_constants"] = constants  # the cached_property's value
        return algebra

    @classmethod
    def from_janet_basis(
        cls, janet: "JanetBasis", point: Sequence[Any] | None = None
    ) -> "LieAlgebra":
        """The Lie algebra of the solutions of a Janet basis of determining
        equations, without solving them (#11; Schwarz, Lie's relations,
        Theorems 3.17-3.19). The unknown functions of the Janet basis are
        the components of the generators, in the order of its variables
        (xi along x, eta along y, ...), as for the catalogue.

        A solution is determined by the values of the parametric
        derivatives at a regular point z0; X_k is the one where the k-th of
        them (parametric_derivatives()) is 1 and the others 0. Every
        derivative of a solution at z0 is then a linear combination of
        these values (its normal form modulo the Janet basis), and so are
        the derivatives of [X_i, X_j], a solution as well: c_ij^k is its k-th
        parametric derivative at z0. The basis depends on z0 (point, by
        default the first regular point with small integer coordinates),
        the algebra up to isomorphism does not.

        The Killing vectors of the plane (xi_x = eta_y = xi_y + eta_x = 0):
        translations and the rotation, the Euclidean algebra e(2).
        symmetry_algebra (delierium.classification) does this for the
        determining equations of a differential equation.

        >>> from sympy import Function, diff
        >>> from delierium.janet_basis import JanetBasis
        >>> x, y = Symbol('x'), Symbol('y')
        >>> xi, eta = Function('xi')(x, y), Function('eta')(x, y)
        >>> killing = [diff(xi, x), diff(eta, y), diff(xi, y) + diff(eta, x)]
        >>> e2 = LieAlgebra.from_janet_basis(JanetBasis(killing, [xi, eta], [x, y]))
        >>> e2.dimension, e2.derived_series(), e2.is_nilpotent()
        (3, [3, 2, 0], False)
        """
        functions, coordinates = list(janet.context.dependent), list(janet.context.independent)
        if len(functions) != len(coordinates):
            raise ValueError("one unknown function (generator component) per variable")
        parametric = janet.parametric_derivatives()
        if parametric is None:
            raise ValueError("infinitely many parametric derivatives: no finite Lie algebra")
        if not parametric:
            return cls.from_structure_constants([])
        keys = [_derivative_key(p, functions, coordinates) for p in parametric]
        top = max((sum(alpha) for _, alpha in keys), default=0) + 1
        indices = [
            alpha for alpha in product(range(top + 1), repeat=len(coordinates)) if sum(alpha) <= top
        ]
        normal_forms = _normal_forms(janet, keys, indices)
        jets = _jets_at_point(normal_forms, coordinates, janet.assumed_nonzero(), point)
        r, n = len(parametric), len(coordinates)

        def bracket_value(i: int, j: int, a: int, beta: tuple[int, ...]) -> Expr:
            """d^beta [X_i, X_j]^a at z0 (Leibniz' rule)."""
            total = sympify(0)
            for b in range(n):
                e_b = tuple(int(m == b) for m in range(n))
                for gamma in product(*(range(m + 1) for m in beta)):
                    rest = tuple(bm - gm + em for bm, gm, em in zip(beta, gamma, e_b, strict=True))
                    weight = prod(binomial(bm, gm) for bm, gm in zip(beta, gamma, strict=True))
                    total += weight * (
                        jets[b, gamma][i] * jets[a, rest][j] - jets[b, gamma][j] * jets[a, rest][i]
                    )
            return total

        c: list[list[list[Expr]]] = [[[sympify(0)] * r for _ in range(r)] for _ in range(r)]
        for i in range(r):
            for j in range(i + 1, r):
                for k, (a, beta) in enumerate(keys):
                    value = cancel(bracket_value(i, j, a, beta))
                    c[i][j][k], c[j][i][k] = value, -value
        return cls.from_structure_constants(c)

    @cached_property
    def structure_constants(self) -> list[list[list[Expr]]]:
        """c[i][j][k] with [X_i, X_j] = sum_k c[i][j][k] X_k; NotClosedError
        if a commutator is not a constant linear combination of the
        generators."""
        r = self.dimension
        c: list[list[list[Expr]]] = [[[sympify(0)] * r for _ in range(r)] for _ in range(r)]
        for i in range(r):
            for j in range(i + 1, r):
                coeffs = self._coordinates_of(self.generators[i].commutator(self.generators[j]))
                for k in range(r):
                    c[i][j][k] = coeffs[k]
                    c[j][i][k] = -coeffs[k]
        return c

    def _coordinates_of(self, v: VectorField) -> list[Expr]:
        """The constants a_k with v = sum_k a_k X_k (they may depend on
        parameters, not on the coordinates); NotClosedError if there are none.

        The identity v = sum_k a_k X_k at random points of the coordinates
        determines the a_k (the X_k being independent); the result is
        verified exactly on the vector fields."""
        r = self.dimension
        if r == 0 or v.is_zero():
            return [sympify(0)] * r
        for exact in (False, True):
            a = self._solve_at_points(v, exact)
            if a is not None and self._is_combination(v, a):
                return a
        raise NotClosedError(f"{v!r} is not a linear combination of the generators")

    def _solve_at_points(self, v: VectorField, exact: bool) -> list[Expr] | None:
        """a with sum_k a_k X_k(p) = v(p) at random points p, or None.

        Unless exact, sin, cos, exp, ... of the coordinates are written
        rationally in new variables (_rational_at_points), and the
        transcendental numbers left at the points (sin(a*5/3), exp(3*a/2),
        ...) are replaced by new symbols, so that the linear algebra is over
        rational functions (fast); a relation between them that this loses
        can only make a solution fail the exact check."""
        r, n = self.dimension, len(self.coordinates)
        coefficients = [
            [*(g.coefficients[m] for g in self.generators), v.coefficients[m]] for m in range(n)
        ]
        variables = list(self.coordinates)
        if not exact:
            rational = _RationalAtPoints(self.coordinates)
            coefficients = [[rational(c) for c in row] for row in coefficients]
            variables += sorted(rational.symbols.values(), key=str)
        values = _values_at_points(coefficients, variables, r + 2)
        if values is None:
            return None
        rows = [row[:-1] for row in values]
        rhs = [row[-1] for row in values]
        A = Matrix(rows).row_join(Matrix(rhs))
        back: dict[Expr, Expr] = {}
        if not exact:
            transcendental = {
                e: Dummy()
                for e in A.atoms(Function, Pow)
                if isinstance(e, Function) or not e.exp.is_Integer
            }
            A = A.xreplace(transcendental)
            back = {d: e for e, d in transcendental.items()}
        try:
            M = DomainMatrix.from_Matrix(A).to_field()
            reduced, pivots = M.rref()
        except Exception:  # pylint: disable=broad-exception-caught  # a domain SymPy cannot build
            return None
        if r in pivots or list(pivots[:r]) != list(range(r)):
            return None  # inconsistent or the generators look dependent
        R = reduced.to_Matrix()
        a = [cancel(R[k, r]) for k in range(r)]
        return [e.xreplace(back) for e in a]

    def _is_combination(self, v: VectorField, a: Sequence[Expr]) -> bool:
        return all(
            simplify(
                v.coefficients[m]
                - sum(a[k] * self.generators[k].coefficients[m] for k in range(self.dimension))
            )
            == 0
            for m in range(len(self.coordinates))
        )

    def commutator_table(self) -> Matrix:
        """[X_i, X_j] in terms of the basis symbols X1, X2, ..."""
        r, c, X = self.dimension, self.structure_constants, self.basis_symbols
        return Matrix(r, r, lambda i, j: sum((c[i][j][k] * X[k] for k in range(r)), sympify(0)))

    def _span_of_brackets(self, left: Matrix, right: Matrix) -> Matrix:
        """A basis (rows, coordinates in X_1..X_r) of [span(left), span(right)]."""
        r, c = self.dimension, self.structure_constants
        vectors = [
            [sum(u[i] * w[j] * c[i][j][k] for i in range(r) for j in range(r)) for k in range(r)]
            for u in left.tolist()
            for w in right.tolist()
        ]
        return _row_basis(vectors, r)

    def derived_series(self) -> list[int]:
        """Dimensions of g, [g, g], [[g, g], [g, g]], ... until it is stable."""
        current = Matrix.eye(self.dimension) if self.dimension else zeros(0, 0)
        dims = [self.dimension]
        while current.rows:
            nxt = self._span_of_brackets(current, current)
            if nxt.rows == current.rows:
                break
            dims.append(nxt.rows)
            current = nxt
        return dims

    def lower_central_series(self) -> list[int]:
        """Dimensions of g, [g, g], [g, [g, g]], ... until it is stable."""
        g = Matrix.eye(self.dimension) if self.dimension else zeros(0, 0)
        current = g
        dims = [self.dimension]
        while current.rows:
            nxt = self._span_of_brackets(g, current)
            if nxt.rows == current.rows:
                break
            dims.append(nxt.rows)
            current = nxt
        return dims

    def is_abelian(self) -> bool:
        return all(e == 0 for e in self.commutator_table())

    def is_solvable(self) -> bool:
        return self.derived_series()[-1] == 0

    def is_nilpotent(self) -> bool:
        return self.lower_central_series()[-1] == 0

    def center(self) -> Matrix:
        """A basis (rows, in X_1..X_r) of the center: the a with
        sum_i a_i c_ij^k = 0 for all j, k."""
        r, c = self.dimension, self.structure_constants
        conditions = Matrix([[c[i][j][k] for i in range(r)] for j in range(r) for k in range(r)])
        if not r:
            return zeros(0, 0)
        null = (
            conditions.nullspace() if conditions.rows else [Matrix.eye(r)[:, i] for i in range(r)]
        )
        return Matrix([list(v) for v in null]) if null else zeros(0, r)

    def killing_form(self) -> Matrix:
        """K_ij = trace(ad X_i ad X_j), (ad X_i)_kj = c_ij^k."""
        r, c = self.dimension, self.structure_constants
        ad = [Matrix(r, r, lambda k, j, i=i: c[i][j][k]) for i in range(r)]
        return Matrix(r, r, lambda i, j: cancel((ad[i] * ad[j]).trace()))

    def type(self) -> "LieAlgebraType | None":
        """The type in Lie's classification of the complex Lie algebras of
        dimension at most 4, with Schwarz's names (section 3.4), None above
        (delierium.lie_algebra_types).

        >>> x, y = Symbol('x'), Symbol('y')
        >>> print(LieAlgebra([[1, 0], [0, 1], [y, -x]], [x, y]).type())  # e(2)
        l3,2(c = -1)
        >>> print(LieAlgebra([[1, 0], [0, 1], [0, y]], [x, y]).type())
        l3,4
        """
        from delierium.lie_algebra_types import (  # pylint: disable=import-outside-toplevel
            lie_algebra_type,
        )

        return lie_algebra_type(self)

    def is_semisimple(self) -> bool:
        """Cartan's criterion: the Killing form is nondegenerate."""
        return self.dimension > 0 and simplify(self.killing_form().det()) != 0


def _derivative_key(
    e: Expr, functions: list[Expr], coordinates: list[Symbol]
) -> tuple[int, tuple[int, ...]]:
    """(index of the function, multi-index over the coordinates) of a
    derivative of one of the functions, or of the function itself."""
    if isinstance(e, Derivative):
        counts = dict(e.variable_count)
        return functions.index(e.expr), tuple(int(counts.get(z, 0)) for z in coordinates)
    return functions.index(e), (0,) * len(coordinates)


def _normal_forms(
    janet: "JanetBasis", keys: list[tuple[int, tuple[int, ...]]], indices: list[tuple[int, ...]]
) -> dict[tuple[int, tuple[int, ...]], list[Expr]]:
    """For each unknown function a and multi-index alpha in indices: the
    coefficients of the normal form of d^alpha f_a modulo janet in the
    parametric derivatives (whose keys are keys)."""
    functions, coordinates = list(janet.context.dependent), list(janet.context.independent)
    t = [Dummy(f"t{k}") for k in range(len(keys))]
    result = {}
    for a, f in enumerate(functions):
        for alpha in indices:
            orders = [(z, n) for z, n in zip(coordinates, alpha, strict=True) if n]
            remainder = janet.representation(f.diff(*orders) if orders else f)[1]
            atoms = remainder.atoms(Derivative) | (remainder.atoms(AppliedUndef) & set(functions))
            linear = remainder.xreplace(
                {e: t[keys.index(_derivative_key(e, functions, coordinates))] for e in atoms}
            )
            result[a, alpha] = [linear.diff(tk) for tk in t]
    return result


def _jets_at_point(
    normal_forms: dict[tuple[int, tuple[int, ...]], list[Expr]],
    coordinates: list[Symbol],
    assumed_nonzero: list[Expr],
    point: Sequence[Any] | None,
) -> dict[tuple[int, tuple[int, ...]], list[Expr]]:
    """normal_forms at point, or else at the first point with small
    coordinates (integers first, then fractions: sin(4*pi*x) vanishes at
    every integer x) where they are finite and the factors the Janet basis
    assumes nonzero do not vanish."""
    if point is not None:
        candidates: Iterable[tuple[Any, ...]] = [tuple(point)]
    else:
        values = [0, 1, -1, 2, -2, Rational(1, 3), Rational(-1, 3), Rational(3, 7)]
        candidates = sorted(
            product(values, repeat=len(coordinates)),
            key=lambda p: (sum(not isinstance(v, int) for v in p), sum(abs(v) for v in p)),
        )
    # vanishing at a singular point: the denominators and the assumptions
    singular = {denom(together(c)) for row in normal_forms.values() for c in row}
    singular_list = sorted(
        {f for f in singular | set(assumed_nonzero) if not f.is_number}, key=count_ops
    )  # the small ones first: they usually reject a point
    for candidate in candidates:
        at = dict(zip(coordinates, map(sympify, candidate), strict=True))
        if any(_vanishes_or_pole(f, at) for f in singular_list):
            continue
        jets = {key: [cancel(c.subs(at)) for c in row] for key, row in normal_forms.items()}
        if not any(c.has(zoo, nan, oo) for row in jets.values() for c in row):
            return jets
    raise ValueError(
        f"{tuple(point)} is not a regular point" if point is not None else "no regular point found"
    )


def _vanishes_or_pole(f: Expr, at: dict[Symbol, Expr]) -> bool:
    value = f.subs(at)
    value = value if value.is_number else cancel(value)
    return value == 0 or value.has(zoo, nan, oo)


def _row_basis(vectors: list[list[Expr]], r: int) -> Matrix:
    if not vectors:
        return zeros(0, r)
    reduced, pivots = Matrix(vectors).rref(simplify=True)
    return reduced[: len(pivots), :]


def _values_at_points(
    coefficients: list[list[Expr]], variables: list[Symbol], count: int
) -> list[list[Expr]] | None:
    """The rows of coefficients at count random points of the variables
    (one block of rows per point), or None. Points where a coefficient has
    a pole (y = x for 1/(y - x)) are skipped. The variables are taken at
    perfect L-th powers, L the lcm of the denominators of the rational
    exponents: then u**(-4/3) and the like are rational there, not new
    algebraic numbers."""
    rng = random.Random(0)
    exponents = [
        e.exp
        for row in coefficients
        for c in row
        for e in c.atoms(Pow)
        if e.exp.is_Rational and not e.exp.is_Integer
    ]
    power = reduce(ilcm, (e.q for e in exponents), 1)
    values: list[list[Expr]] = []
    points = 0
    for _ in range(20 * count):
        if points == count:
            return values
        point = {z: Rational(rng.randint(2, 9), rng.randint(2, 5)) ** power for z in variables}
        block = [[c.subs(point) for c in row] for row in coefficients]
        if any(e.has(zoo, nan, oo) for row in block for e in row):
            continue
        points += 1
        values += block
    return values if points == count else None
