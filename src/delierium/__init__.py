"""delierium: Lie point symmetries of differential equations with Janet bases.

The public interface is what this package exports (``from delierium import
...``):

* everything at once: lie_symmetries (a LieSymmetries object: determining
  equations, Janet basis, dimension, assumptions, algebra, verify())
* determining equations: overdetermined_system_ode, overdetermined_system_odes,
  overdetermined_system_pde, make_infinitesimal, create_infinitesimals,
  prolongation; verify_symmetry, verify_symmetries (a given generator
  substituted into them: VerificationResult); scaling_symmetries (by linear
  algebra on the exponents, without the determining equations)
* Janet bases: JanetBasis, determining_janet_basis (of the determining
  equations; rank() is the dimension of the symmetry algebra),
  janet_basis_from_ode, janet_basis_from_odes,
  is_janet_basis_of, is_janet_basis_of_ode, is_janet_basis_of_odes,
  integrability_conditions, JanetType, and the result types LHDP, LHDPList
* group classification: classify (cases of a linear system with parameters,
  each with its Janet basis), group_classification (cases of the symmetries
  of a differential equation with parameters), Case
* symmetry algebras: symmetry_algebra (the Lie algebra of the point
  symmetries of a differential equation, from its determining equations
  without solving them)
* algebraic Thomas decomposition: thomas_decomposition (polynomial equations
  and inequations split into simple systems with disjoint solutions),
  SimpleSystem
* rankings: Context, Mgrevlex, Mgrlex, Mlex
* printing in the notation of Lie: ltf, lie_form, lie_derivative_printer
* Lie algebras: LieAlgebra (of generators, of a Janet basis of determining
  equations or from structure constants; commutator table, derived and lower
  central series, center, Killing form, type in Lie's classification up to
  dimension 4: LieAlgebraType), VectorField, NotClosedError
* operators: euler_operator, frechet_derivative, adjoint_frechet_derivative,
  variational_derivative
* pictures: the module delierium.visualization (staircase diagrams of Janet
  bases, generators as vector fields, flows); it needs matplotlib
  (``pip install delierium[plot]``) and is not imported by ``import delierium``

The modules' ``__all__`` list in addition building blocks of the algorithms
(e.g. delierium.janet_basis.complete_system, vec_multipliers); they may
change. Every other name is internal.

``delierium.__version__`` is the version of the installed package, from its
metadata; the only place it is written is ``pyproject.toml``.
"""

from importlib.metadata import version as _version

from .classification import Case, classify, group_classification, symmetry_algebra
from .derivative_operators import (
    adjoint_frechet_derivative,
    euler_operator,
    frechet_derivative,
    variational_derivative,
)
from .helpers import lie_derivative_printer, lie_form, ltf, make_infinitesimal
from .infinitesimals import (
    VerificationResult,
    create_infinitesimals,
    determining_janet_basis,
    is_janet_basis_of_ode,
    is_janet_basis_of_odes,
    janet_basis_from_ode,
    janet_basis_from_odes,
    overdetermined_system_ode,
    overdetermined_system_odes,
    overdetermined_system_pde,
    prolongation,
    verify_symmetries,
    verify_symmetry,
)
from .janet_basis import (
    LHDP,
    JanetBasis,
    JanetType,
    LHDPList,
    integrability_conditions,
    is_janet_basis_of,
)
from .lie_algebra import LieAlgebra, NotClosedError, VectorField
from .lie_algebra_types import LieAlgebraType
from .matrix_order import Context, Mgrevlex, Mgrlex, Mlex
from .scaling import scaling_symmetries
from .symmetries import LieSymmetries, lie_symmetries
from .thomas import SimpleSystem, thomas_decomposition

__version__ = _version("delierium")

__all__ = [
    "LHDP",
    "Case",
    "Context",
    "JanetBasis",
    "JanetType",
    "LHDPList",
    "LieAlgebra",
    "LieAlgebraType",
    "LieSymmetries",
    "Mgrevlex",
    "Mgrlex",
    "Mlex",
    "NotClosedError",
    "SimpleSystem",
    "VectorField",
    "VerificationResult",
    "__version__",
    "adjoint_frechet_derivative",
    "classify",
    "create_infinitesimals",
    "determining_janet_basis",
    "euler_operator",
    "frechet_derivative",
    "group_classification",
    "integrability_conditions",
    "is_janet_basis_of",
    "is_janet_basis_of_ode",
    "is_janet_basis_of_odes",
    "janet_basis_from_ode",
    "janet_basis_from_odes",
    "lie_derivative_printer",
    "lie_form",
    "lie_symmetries",
    "ltf",
    "make_infinitesimal",
    "overdetermined_system_ode",
    "overdetermined_system_odes",
    "overdetermined_system_pde",
    "prolongation",
    "scaling_symmetries",
    "symmetry_algebra",
    "thomas_decomposition",
    "variational_derivative",
    "verify_symmetries",
    "verify_symmetry",
]
