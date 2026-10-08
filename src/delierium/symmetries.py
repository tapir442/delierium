"""lie_symmetries: the Lie point symmetries of a differential equation in one
call, from the determining equations to the dimension and structure of the
symmetry algebra (#10). The low-level functions it combines stay available:
overdetermined_system_ode/pde, determining_janet_basis, symmetry_algebra,
verify_symmetries."""

from collections.abc import Iterable, Sequence
from functools import cached_property
from typing import Any

from sympy import Basic, Expr, oo

from delierium.infinitesimals import (
    Variables,
    VerificationResult,
    _determining_system,
    _initials,
    convert_to_iterable,
    verify_symmetries,
)
from delierium.janet_basis import JanetBasis
from delierium.lie_algebra import LieAlgebra
from delierium.matrix_order import Mgrevlex, WeightFunction

__all__ = ["LieSymmetries", "lie_symmetries"]


class LieSymmetries:  # pylint: disable=too-many-instance-attributes
    """The Lie point symmetries of a scalar ODE, a system of ODEs or a scalar
    PDE; see lie_symmetries. Everything is computed on first access.

    equations, dependent, independent: as given (lists)
    determining_equations: the linear determining equations
    infinitesimals: their unknown functions, one per coordinate
    coordinates: the independent variables, then the dependent ones as
        plain symbols (y for y(x)), the arguments of the infinitesimals
    janet_basis: the Janet basis of the determining equations
    dimension: the dimension of the symmetry algebra (oo if infinite)
    assumptions: the expressions assumed nonzero: the initials of the
        equations and the factors the Janet basis divides by
    parameter_conditions: the special parameter values the Janet basis
        excludes (see group_classification for them)
    algebra: the Lie algebra (finite dimension only), from the Janet basis
    """

    def __init__(
        self,
        equations: Expr | Iterable[Expr],
        dependent: Variables,
        independent: Variables,
        sort_order: WeightFunction = Mgrevlex,
    ) -> None:
        self.equations = [equations] if isinstance(equations, Basic) else list(equations)
        self.dependent = convert_to_iterable(dependent)
        self.independent = convert_to_iterable(independent)
        self.sort_order = sort_order
        system, functions, coordinates = _determining_system(
            self.equations, self.dependent, self.independent
        )
        self.determining_equations: list[Expr] = system
        self.infinitesimals: list[Expr] = functions
        self.coordinates: list[Basic] = coordinates

    @cached_property
    def janet_basis(self) -> JanetBasis:
        return JanetBasis(
            self.determining_equations, self.infinitesimals, self.coordinates, self.sort_order
        )

    @property
    def dimension(self) -> Any:
        return self.janet_basis.rank()

    @property
    def is_finite(self) -> bool:
        return bool(self.dimension != oo)

    @cached_property
    def assumptions(self) -> list[Expr]:
        result = _initials(self.equations, self.dependent, self.independent)
        for e in self.janet_basis.assumed_nonzero():
            if e not in result:
                result.append(e)
        return result

    @property
    def parameter_conditions(self) -> list[list[Expr]]:
        return self.janet_basis.parameter_conditions()

    @cached_property
    def algebra(self) -> LieAlgebra:
        """ValueError if the algebra is infinite."""
        return LieAlgebra.from_janet_basis(self.janet_basis)

    def verify(self, generators: Sequence[Sequence[Any]]) -> list[VerificationResult]:
        """verify_symmetries for the generators, each a tuple with one
        component per coordinate."""
        return verify_symmetries(self.equations, self.dependent, self.independent, generators)

    def __repr__(self) -> str:
        return f"LieSymmetries({self.equations}, dimension {self.dimension})"


def lie_symmetries(
    equations: Expr | Iterable[Expr],
    dependent: Variables,
    independent: Variables,
    sort_order: WeightFunction = Mgrevlex,
) -> LieSymmetries:
    """The Lie point symmetries of a scalar ODE, a system of ODEs or a scalar
    PDE (equations = 0), as a LieSymmetries object: determining equations,
    Janet basis, dimension, assumptions, algebra, and verify() for given
    generators.

    The Blasius equation: two symmetries, the translation and a scaling,
    a non-abelian algebra:

    >>> from sympy import Function, Symbol, diff
    >>> x, y_ = Symbol("x"), Symbol("y")
    >>> y = Function("y")(x)
    >>> blasius = diff(y, x, 3) + y * diff(y, x, 2)
    >>> s = lie_symmetries(blasius, y, x)
    >>> s.dimension, s.coordinates, s.algebra.type().name
    (2, [x, y], 'l2,1')
    >>> [bool(r) for r in s.verify([(1, 0), (x, -y_), (x, y_)])]
    [True, True, False]

    The heat equation has infinitely many:

    >>> t = Symbol("t")
    >>> u = Function("u")(x, t)
    >>> heat = lie_symmetries(diff(u, t) - diff(u, x, 2), u, [x, t])
    >>> heat.dimension, heat.is_finite
    (oo, False)
    """
    return LieSymmetries(equations, dependent, independent, sort_order)
