"""delierium: Lie point symmetries of differential equations with Janet bases.

The public interface is what this package exports (``from delierium import
...``):

* determining equations: overdetermined_system_ode, overdetermined_system_odes,
  overdetermined_system_pde, make_infinitesimal, create_infinitesimals,
  prolongation
* Janet bases: JanetBasis, janet_basis_from_ode, janet_basis_from_odes,
  is_janet_basis_of, is_janet_basis_of_ode, is_janet_basis_of_odes,
  integrability_conditions, JanetType, and the result types LHDP, LHDPList
* rankings: Context, Mgrevlex, Mgrlex, Mlex
* printing in the notation of Lie: ltf, lie_form, lie_derivative_printer
* operators: euler_operator, frechet_derivative, adjoint_frechet_derivative,
  variational_derivative
* pictures: the module delierium.visualization (staircase diagrams of Janet
  bases, generators as vector fields, flows); it needs matplotlib
  (``pip install delierium[plot]``) and is not imported by ``import delierium``

The modules' ``__all__`` list in addition building blocks of the algorithms
(e.g. delierium.janet_basis.complete_system, vec_multipliers); they may
change. Every other name is internal.
"""

from .derivative_operators import (
    adjoint_frechet_derivative,
    euler_operator,
    frechet_derivative,
    variational_derivative,
)
from .helpers import lie_derivative_printer, lie_form, ltf, make_infinitesimal
from .infinitesimals import (
    create_infinitesimals,
    is_janet_basis_of_ode,
    is_janet_basis_of_odes,
    janet_basis_from_ode,
    janet_basis_from_odes,
    overdetermined_system_ode,
    overdetermined_system_odes,
    overdetermined_system_pde,
    prolongation,
)
from .janet_basis import (
    LHDP,
    JanetBasis,
    JanetType,
    LHDPList,
    integrability_conditions,
    is_janet_basis_of,
)
from .matrix_order import Context, Mgrevlex, Mgrlex, Mlex

__all__ = [
    "LHDP",
    "Context",
    "JanetBasis",
    "JanetType",
    "LHDPList",
    "Mgrevlex",
    "Mgrlex",
    "Mlex",
    "adjoint_frechet_derivative",
    "create_infinitesimals",
    "euler_operator",
    "frechet_derivative",
    "integrability_conditions",
    "is_janet_basis_of",
    "is_janet_basis_of_ode",
    "is_janet_basis_of_odes",
    "janet_basis_from_ode",
    "janet_basis_from_odes",
    "lie_derivative_printer",
    "lie_form",
    "ltf",
    "make_infinitesimal",
    "overdetermined_system_ode",
    "overdetermined_system_odes",
    "overdetermined_system_pde",
    "prolongation",
    "variational_derivative",
]
