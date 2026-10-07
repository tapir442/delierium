"""Group classification: the Janet bases of a linear system with parameters,
split into disjoint cases instead of assuming the parameter conditions
nonzero (#16, the linear first step of the Thomas decomposition #58).

A Janet basis divides by coefficients it assumes nonzero; those depending
only on the parameters are its parameter conditions
(JanetBasis.parameter_conditions). classify branches on each of them: the
generic case, where none holds, and for each condition the case where it
holds (and the earlier ones do not), computed again with the condition
substituted, recursively. A special case whose Janet basis is that of the
generic case is merged into it.

group_classification does the same for the Lie point symmetries of a scalar
differential equation, computing each case from the equation itself: there
are also cases where two powers of jet variables with symbolic exponents
coincide, which the determining equations of the generic case do not show
(infinitesimals.jet_power_conditions).
"""

from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass, field

from sympy import (
    Basic,
    Derivative,
    Dummy,
    Expr,
    I,
    Poly,
    PolynomialError,
    default_sort_key,
    factor_list,
    nan,
    numer,
    solve,
    together,
    zoo,
)

from delierium.helpers import finish_substitution
from delierium.infinitesimals import (
    _leading_derivative,
    create_infinitesimals,
    determining_condition,
    jet_power_conditions,
    order,
    split_jet_coefficients,
)
from delierium.janet_basis import LHDP, JanetBasis, nonzero_factors, split_assumptions
from delierium.lie_algebra import LieAlgebra
from delierium.matrix_order import Mgrevlex, WeightFunction
from delierium.thomas import thomas_decomposition

__all__ = ["Case", "classify", "group_classification", "symmetry_algebra"]

# rule -> (Janet basis there, the conditions to branch on)
_Builder = Callable[[dict[Basic, Expr]], tuple[JanetBasis, list[list[Expr]]]]


@dataclass
class Case:
    """One case of a classification: the parameter values (rule), the
    conditions that do not hold (inequations, each a list of expressions
    that do not all vanish) and the Janet basis there."""

    rule: dict[Basic, Expr]
    inequations: list[list[Expr]]
    janet: JanetBasis = field(repr=False)

    def rank(self) -> object:
        """The rank of the Janet basis: the dimension of the symmetry
        algebra for the determining equations of a differential equation."""
        return self.janet.rank()

    def __str__(self) -> str:
        values = ", ".join(f"{k} = {v}" for k, v in self.rule.items()) or "generic"
        excluded = "; ".join(" or ".join(f"{e} != 0" for e in ineq) for ineq in self.inequations)
        return f"{values}{' (' + excluded + ')' if excluded else ''}: rank {self.rank()}"


def classify(
    S: Basic | Iterable[Basic],
    dependent: Iterable[Basic],
    independent: Iterable[Basic],
    sort_order: WeightFunction = Mgrevlex,
    max_depth: int = 4,
) -> list[Case]:
    """The cases of the linear system S with respect to its parameters (the
    symbols other than the independent variables), the generic case first.

    The cases are disjoint: a special case holds where its rule does and none
    of its inequations vanishes. max_depth limits the nesting of special
    cases (conditions within conditions).

    >>> from sympy import Function, diff, symbols
    >>> x, y, a = symbols("x y a")
    >>> z = Function("z")(x, y)
    >>> for case in classify([diff(z, x) - a * diff(z, y), a * diff(z, y, 2)], [z], [x, y]):
    ...     print(case)
    generic (a != 0): rank 2
    a = 0: rank oo
    """
    equations = [S] if isinstance(S, Expr) else list(S)
    dependent, independent = list(dependent), list(independent)

    def build(rule: dict[Basic, Expr]) -> tuple[JanetBasis, list[list[Expr]]]:
        system = [e.subs(rule) for e in equations]
        janet = JanetBasis(system, dependent, independent, sort_order)
        return janet, janet.parameter_conditions()

    return _classify(build, {}, [], max_depth)


def group_classification(
    eq: Expr,
    dependent: Basic,
    independent: Iterable[Basic],
    sort_order: WeightFunction = Mgrevlex,
    max_depth: int = 4,
) -> list[Case]:
    """The cases of the Lie point symmetries of the scalar differential
    equation eq = 0 (one dependent variable, e.g. u(x, t)) with respect to
    its parameters, the generic case first; Case.rank() is the dimension of
    the symmetry algebra. Each case is computed from eq with the parameter
    values substituted.

    >>> from sympy import Function, diff, symbols
    >>> x, t, n = symbols("x t n")
    >>> u = Function("u")(x, t)
    >>> for case in group_classification(diff(u, t) - diff(diff(u, x) ** n, x), u, [x, t]):
    ...     print(case)
    generic (n != 0; n - 1 != 0; n + 1 != 0): rank 5
    n = 0: rank oo
    n = 1: rank oo
    n = -1: rank oo

    (n = -1 is linearizable by a hodograph transformation.)
    """
    independent = list(independent)
    variables = [*independent, sp_symbol(dependent)]

    def build(rule: dict[Basic, Expr]) -> tuple[JanetBasis, list[list[Expr]]]:
        special = eq.subs(rule)
        janet, condition = _determining_janet_basis(special, dependent, independent, sort_order)
        conditions = _initial_conditions(special, dependent, independent)
        for c in [*janet.parameter_conditions(), *jet_power_conditions(condition, [dependent])]:
            if c not in conditions and not any(e.has(*variables) for e in c):
                conditions.append(c)
        return janet, conditions

    return _classify(build, {}, [], max_depth)


def symmetry_algebra(
    eq: Expr,
    dependent: Basic,
    independent: Iterable[Basic],
    sort_order: WeightFunction = Mgrevlex,
) -> LieAlgebra:
    """The Lie algebra of the point symmetries of the scalar differential
    equation eq = 0 (one dependent variable, e.g. y(x) or u(x, t)), from the
    Janet basis of its determining equations, without solving them
    (LieAlgebra.from_janet_basis). The parameters of eq are assumed generic;
    ValueError if the algebra is infinite.

    y'' = y'**2/y is linearizable: sl(3), simple of dimension 8. Burgers'
    equation: dimension 5, sl(2) acting irreducibly on the abelian ideal of
    d/dx and the Galilean boost, so the algebra is perfect ([g, g] = g):

    >>> from sympy import Function, diff, symbols
    >>> x, t = symbols("x t")
    >>> y = Function("y")(x)
    >>> sl3 = symmetry_algebra(diff(y, x, 2) - diff(y, x) ** 2 / y, y, [x])
    >>> sl3.dimension, sl3.is_semisimple()
    (8, True)
    >>> u = Function("u")(x, t)
    >>> burgers = symmetry_algebra(diff(u, t) - diff(u, x, 2) - u * diff(u, x), u, [x, t])
    >>> burgers.dimension, burgers.is_solvable(), burgers.derived_series()
    (5, False, [5])
    """
    janet, _ = _determining_janet_basis(eq, dependent, list(independent), sort_order)
    return LieAlgebra.from_janet_basis(janet)


def _determining_janet_basis(
    eq: Expr, dependent: Basic, independent: list[Basic], sort_order: WeightFunction
) -> tuple[JanetBasis, Expr]:
    """The Janet basis of the determining equations of eq (unknown
    functions: the infinitesimals in the order of the coordinates, the
    independent variables, then the dependent one as a plain symbol) and
    the symmetry condition they come from."""
    infinitesimals = create_infinitesimals([dependent], independent)
    plain = {dependent: sp_symbol(dependent)}
    functions = [infinitesimals[v].xreplace(plain) for v in [*independent, dependent]]
    condition = determining_condition(eq, [dependent], independent, infinitesimals)
    system = [
        finish_substitution(e).xreplace(plain)
        for e in split_jet_coefficients(condition, [dependent])
    ]
    janet = JanetBasis(system, functions, [*independent, plain[dependent]], sort_order)
    return janet, condition


def _initial_conditions(eq: Expr, dependent: Basic, independent: list[Basic]) -> list[list[Expr]]:
    """The parameter conditions of the initial of eq, the coefficient of its
    highest derivative: deriving the determining equations divides by it
    (solving for the highest derivative), so where it vanishes the equation
    is a different one."""
    _, highest = order(eq, [dependent], independent)
    if not highest:
        return []
    leader = _leading_derivative(eq, highest, [dependent])
    h = Dummy()
    try:
        initial = Poly(numer(together(eq.xreplace({leader: h}))), h).LC()
    except PolynomialError:
        return []
    # the jet variables and the dependent variable are variables as well
    variables = {d: Dummy() for d in initial.atoms(Derivative)} | {dependent: Dummy()}
    initial = initial.xreplace(variables)
    return split_assumptions(nonzero_factors([initial]), [*independent, *variables.values()])[0]


def sp_symbol(f: Basic) -> Basic:
    """The plain symbol for the dependent variable f, e.g. u for u(x, t)."""
    from sympy import Symbol  # pylint: disable=import-outside-toplevel

    return Symbol(f.func.__name__)


def _classify(
    build: _Builder,
    rule: dict[Basic, Expr],
    inequations: list[list[Expr]],
    depth: int,
) -> list[Case]:
    janet, conditions = build(rule)
    generic = Case(rule, list(inequations), janet)
    if depth == 0:
        return [generic]
    special: list[Case] = []
    excluded: list[list[Expr]] = []  # conditions handled before: they do not hold
    for condition in conditions:
        for solution, initials in _solutions(condition):
            outer = _inequations(
                [[e.subs(solution) for e in ineq] for ineq in [*inequations, *excluded]]
                + [[e] for e in initials]
            )
            if outer is None:
                continue  # contradicts a condition that does not hold here
            cases = _classify(
                build,
                {**{k: v.subs(solution) for k, v in rule.items()}, **solution},
                outer,
                depth - 1,
            )
            if len(cases) == 1 and _same_basis(janet, solution, cases[0].janet):
                continue  # the generic Janet basis holds here as well
            special += cases
            generic.inequations.append(condition)
        excluded.append(condition)
    generic.inequations = _inequations(generic.inequations) or []
    return [generic, *special]


def _inequations(inequations: list[list[Expr]]) -> list[list[Expr]] | None:
    """The inequations (each: not all of its expressions vanish) without the
    vanishing expressions, those that always hold and duplicates; None if
    one of them cannot hold (all its expressions vanish)."""
    result: list[list[Expr]] = []
    for ineq in inequations:
        nonzero = [e for e in (e.simplify() for e in ineq) if e != 0]
        if not nonzero:
            return None
        if any(e.is_number for e in nonzero):
            continue  # a nonzero number: holds everywhere
        primitive = [e.as_content_primitive()[1] for e in nonzero]  # 2*a: a
        normalized = sorted(
            {-e if e.could_extract_minus_sign() else e for e in primitive}, key=default_sort_key
        )
        if normalized not in result:
            result.append(normalized)
    return result


def _solutions(condition: Sequence[Expr]) -> list[tuple[dict[Basic, Expr], list[Expr]]]:
    """The real solutions of the polynomial equations condition, each with the
    expressions it assumes nonzero.

    They come from an algebraic Thomas
    decomposition (#58): disjoint simple systems, each solved for its
    leaders from the lowest up; the inequations of a system are the
    assumptions. In a simple system the initial of each equation and its
    discriminant do not vanish, so the roots are distinct and the solutions
    disjoint."""
    polys = [numer(together(e)).expand() for e in condition]
    polys = [f for f in polys if f != 0]
    if not polys:
        return [({}, [])]
    if any(f.is_number for f in polys):
        return []  # a nonzero constant vanishes nowhere
    variables = sorted(set().union(*(f.free_symbols for f in polys)), key=default_sort_key)
    results = []
    for system in thomas_decomposition(polys, variables=variables):
        for solution in _solve_triangular(system.equations, variables):
            assumed = [
                factor for e in system.inequations for factor, _ in factor_list(e.subs(solution))[1]
            ]
            results.append((solution, assumed))
    return results


def _solve_triangular(equations: list[Expr], variables: list[Basic]) -> list[dict[Basic, Expr]]:
    """The real solutions of the equations of a simple system, its leaders
    in terms of the free variables: each equation solved for its leader
    after substituting the solutions of the lower ones."""
    solutions: list[dict[Basic, Expr]] = [{}]
    for equation in reversed(equations):  # lowest leader first
        leader = next(v for v in variables if equation.has(v))
        extended = []
        for solution in solutions:
            try:
                roots: list[Expr] = list(solve(equation.subs(solution), leader))
            except NotImplementedError:
                roots = []
            extended += [{**solution, leader: root} for root in roots if not root.has(I)]
        solutions = extended
    return solutions


def _same_basis(janet: JanetBasis, solution: dict[Basic, Expr], other: JanetBasis) -> bool:
    """janet's basis with solution substituted is other's (both fully
    reduced with leading coefficients 1, so unique for the ranking)."""
    substituted = [e.expression().subs(solution) for e in janet.S]
    if any(e.has(zoo, nan) for e in substituted):
        return False
    candidate = [LHDP(e, other.context) for e in substituted]
    candidate = [e for e in candidate if e.terms]
    return sorted(map(str, candidate)) == sorted(map(str, other.S))
