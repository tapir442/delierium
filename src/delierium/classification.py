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
"""

from collections.abc import Iterable, Sequence
from dataclasses import dataclass, field

from sympy import Basic, Expr, I, Poly, default_sort_key, nan, numer, solve, together, zoo

from delierium.janet_basis import LHDP, JanetBasis
from delierium.matrix_order import Mgrevlex, WeightFunction

__all__ = ["Case", "classify"]


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
    return _classify(equations, dependent, independent, sort_order, {}, [], max_depth)


def _classify(
    equations: list[Basic],
    dependent: list[Basic],
    independent: list[Basic],
    sort_order: WeightFunction,
    rule: dict[Basic, Expr],
    inequations: list[list[Expr]],
    depth: int,
) -> list[Case]:
    janet = JanetBasis(equations, dependent, independent, sort_order)
    generic = Case(rule, list(inequations), janet)
    if depth == 0:
        return [generic]
    special: list[Case] = []
    excluded: list[list[Expr]] = []  # conditions handled before: they do not hold
    for condition in janet.parameter_conditions():
        for solution, initials in _solutions(condition):
            outer = _inequations(
                [[e.subs(solution) for e in ineq] for ineq in [*inequations, *excluded]]
                + [[e] for e in initials]
            )
            if outer is None:
                continue  # contradicts a condition that does not hold here
            cases = _classify(
                [e.subs(solution) for e in equations],
                dependent,
                independent,
                sort_order,
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
        normalized = sorted(
            {-e if e.could_extract_minus_sign() else e for e in nonzero}, key=default_sort_key
        )
        if normalized not in result:
            result.append(normalized)
    return result


def _solutions(condition: Sequence[Expr]) -> list[tuple[dict[Basic, Expr], list[Expr]]]:
    """The real solutions of the polynomial equations condition, each with
    the initials it assumes nonzero, as in an algebraic Thomas decomposition:
    an equation is solved for its leading symbol only where its initial (the
    leading coefficient) does not vanish; where it does, the initial and the
    rest of the equation are new equations."""
    polys = [numer(together(e)).expand() for e in condition]
    polys = [f for f in polys if f != 0]
    if not polys:
        return [({}, [])]
    f, rest = polys[0], polys[1:]
    if f.is_number:
        return []  # a nonzero constant vanishes nowhere
    leader = sorted(f.free_symbols, key=default_sort_key)[0]
    poly = Poly(f, leader)
    initial = poly.LC()
    results = []
    if not initial.is_number:
        # initial = 0: the equation without its leading term
        results += _solutions([initial, f - initial * leader ** poly.degree(), *rest])
    try:
        roots = solve(f, leader)
    except NotImplementedError:
        roots = []
    for root in roots:
        if root.has(I):
            continue
        for solution, initials in _solutions([e.subs(leader, root) for e in rest]):
            value = root.subs(solution)
            assumed = [initial.subs(solution)] if not initial.is_number else []
            results.append(({leader: value, **solution}, assumed + initials))
    return results


def _same_basis(janet: JanetBasis, solution: dict[Basic, Expr], other: JanetBasis) -> bool:
    """janet's basis with solution substituted is other's (both fully
    reduced with leading coefficients 1, so unique for the ranking)."""
    substituted = [e.expression().subs(solution) for e in janet.S]
    if any(e.has(zoo, nan) for e in substituted):
        return False
    candidate = [LHDP(e, other.context) for e in substituted]
    candidate = [e for e in candidate if e.terms]
    return sorted(map(str, candidate)) == sorted(map(str, other.S))
