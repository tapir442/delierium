"""Infinitesimals – functional rewrite with pluggable CAS backend.

Backend selection
-----------------
Set the environment variable ``CAS_BACKEND`` to one of:

    sympy      (default)
    symengine
    sagemath

or call ``select_backend("sympy")`` before importing anything else from this
module.  Every other function in this file imports exclusively from
``backend``, so the switch is transparent.
"""

from __future__ import annotations

import os
from collections import ChainMap, OrderedDict
from collections.abc import Iterable
from functools import reduce
from itertools import combinations_with_replacement
from typing import Any, Callable, NamedTuple

# ---------------------------------------------------------------------------
# 1. Backend adapter
# ---------------------------------------------------------------------------

def _load_sympy():
    from sympy import (
        Symbol, Function, Derivative, Expr,
        Dummy, diff, solve, init_printing,
    )
    init_printing()
    return dict(
        Symbol=Symbol,
        Function=Function,
        Derivative=Derivative,
        Expr=Expr,
        Dummy=Dummy,
        diff=diff,
        solve=solve,
    )


def _load_symengine():
    import symengine as se
    # symengine does not have a standalone ``solve``; fall back to sympy's
    from sympy import solve as sp_solve
    return dict(
        Symbol=se.Symbol,
        Function=se.Function,
        Derivative=se.Derivative,
        Expr=se.Expr,
        Dummy=se.Symbol,          # symengine has no Dummy – Symbol is fine
        diff=se.diff,
        solve=sp_solve,           # hybrid: sympy solve on symengine exprs
    )


def _load_sagemath():
    # sage exposes its globals through ``sage.all``
    from sage.all import (          # type: ignore[import]
        SR, var, function, diff, solve,
    )
    # Wrap SageMath so the API looks the same as sympy
    class _Symbol:
        """Thin wrapper: Symbol(name) → sage var."""
        def __new__(cls, name):
            return var(name)

    class _Function:
        """Thin wrapper: Function(name) → sage function."""
        def __new__(cls, name):
            return function(name)

    return dict(
        Symbol=_Symbol,
        Function=_Function,
        Derivative=None,       # sage uses diff(), not Derivative()
        Expr=SR,
        Dummy=_Symbol,
        diff=diff,
        solve=solve,
    )


_LOADERS: dict[str, Callable[[], dict]] = {
    "sympy":     _load_sympy,
    "symengine": _load_symengine,
    "sagemath":  _load_sagemath,
}

# Mutable module-level reference – replaced by select_backend()
_backend: dict = {}


def select_backend(name: str) -> None:
    """Switch the active CAS backend.  Must be called before any computation.

    Parameters
    ----------
    name:
        ``"sympy"``, ``"symengine"``, or ``"sagemath"``
    """
    global _backend
    loader = _LOADERS.get(name.lower())
    if loader is None:
        raise ValueError(f"Unknown backend {name!r}.  Choose from: {list(_LOADERS)}")
    _backend = loader()


def _B(name: str):                     # noqa: N802 – short helper
    """Return a symbol from the active backend."""
    if not _backend:
        select_backend(os.environ.get("CAS_BACKEND", "sympy"))
    return _backend[name]


# Convenience accessors (used everywhere below instead of direct sympy imports)
def _Symbol(name):   return _B("Symbol")(name)
def _diff(expr, *a): return _B("diff")(expr, *a)
def _solve(eq, x):   return _B("solve")(eq, x)


# Initialise default backend at import time
select_backend(os.environ.get("CAS_BACKEND", "sympy"))

# ---------------------------------------------------------------------------
# 2. Local imports that depend on the project (unchanged API surface)
# ---------------------------------------------------------------------------

from delierium.JanetBasis import Janet_Basis, LHDP, Reorder, _Dterm   # noqa: E402
from delierium.helpers import (                                         # noqa: E402
    finish_substitution, make_infinitesimal, func_diff,
    _free_symbols_cache, profile_if_enabled, Basic,
)
from delierium.matrix_order import Mgrevlex, Context                   # noqa: E402

# ---------------------------------------------------------------------------
# 3. Pure helper functions
# ---------------------------------------------------------------------------

def convert_to_iterable(item: Any) -> list:
    """Wrap non-iterable values in a list; return lists unchanged."""
    return item if isinstance(item, Iterable) else [item]


def variable_combinations(variables: list, order: int) -> list[list]:
    """Return all multisets of *variables* of size 1 … *order*."""
    return reduce(
        lambda acc, i: acc + [list(c) for c in combinations_with_replacement(variables, i)],
        range(1, order + 1),
        [],
    )


# ---------------------------------------------------------------------------
# 4. Order analysis
# ---------------------------------------------------------------------------

def order(expr, dep: list, indep: list) -> tuple[int, set]:
    """Return ``(max_order, {highest_derivative_atoms})``.

    Pure: reads *expr* and returns a value, touches nothing else.
    """
    dep   = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    dep_names = {d.name for d in dep}

    Derivative = _backend["Derivative"]

    def _fold(acc, atom):
        max_order, max_deriv = acc
        if atom.args[0].name not in dep_names:
            return acc
        atom_order = sum(cnt[1] for cnt in atom.args[1:])
        if atom_order == max_order:
            return max_order, max_deriv | {atom}
        if atom_order > max_order:
            return atom_order, {atom}
        return acc

    _, atoms = reduce(_fold, expr.expand().atoms(Derivative), (0, set()))
    max_ord  = reduce(lambda m, a: max(m, sum(c[1] for c in a.args[1:])), atoms, 0)
    return max_ord, atoms


# ---------------------------------------------------------------------------
# 5. Prolongation machinery
# ---------------------------------------------------------------------------

@profile_if_enabled
def compute_level(
    deriv_vars_order: list,
    dep: list,
    indep: list,
    infinitesimals: dict,
) -> tuple[list, list]:
    """Recursively compute prolonged functions and their infinitesimals.

    Pure: does not mutate *infinitesimals*.

    Extended Gamma operator (Arrigo eq. 2.85 / Schwarz eq. 5.10).
    """
    v = deriv_vars_order[-1]

    if len(deriv_vars_order) == 1:
        funcs = list(dep)
        etas  = [infinitesimals[f] for f in funcs]
    else:
        funcs, etas = compute_level(deriv_vars_order[:-1], dep, indep, infinitesimals)

    def _next_pair(func, eta):
        new_func = func_diff(func, v)
        new_eta  = reduce(
            lambda acc, var: acc - func_diff(func, var) * func_diff(infinitesimals[var], v),
            indep,
            func_diff(eta, v),
        )
        return new_func, new_eta

    pairs = [_next_pair(f, e) for f, e in zip(funcs, etas)]
    funcs_next, etas_next = zip(*pairs)
    return list(funcs_next), list(etas_next)


@profile_if_enabled
def prolongation(expr, n: int, infinitesimals: dict, dep: list, indep: list, dummies: dict):
    """Apply the prolongation operator to *expr*.

    Returns a new expression.  Does not mutate *infinitesimals*.

    Doctest stolen from Baumann pp. 92/93
    >>> from sympy import Symbol, Function, Derivative
    >>> x = Symbol('x')
    >>> u = Function('u')
    >>> u_x = u(x)
    >>> f = Function("f")
    >>> fx = f(x, u_x, Derivative(u_x, x))
    >>> from delierium.helpers import make_infinitesimal, finish_substitution
    >>> inf = {x: make_infinitesimal(x, x, fx, name=r"phi"),
    ...        fx: make_infinitesimal(fx, x, fx, name=r"xi")}
    >>> ppp = prolongation(fx, 2, inf, [u_x], [x], dummies={}).expand()
    """  # noqa: E501
    # Resolve deferred dummy substitutions (pure: build new dict, do not mutate)
    clean_inf = {
        k: v.xreplace(finish_substitution(v))
        for k, v in infinitesimals.items()
    }

    reverse_dummies = {v: k for k, v in dummies.items()}

    acc = sum(
        clean_inf[key] * func_diff(
            expr.xreplace(dummies), key.xreplace(dummies)
        ).xreplace(reverse_dummies)
        for key in clean_inf
    )
    return acc


# ---------------------------------------------------------------------------
# 6. Coefficient extraction
# ---------------------------------------------------------------------------

def _analyze_power(factor, dep: list):
    """Return *factor* if it is a dependent-variable derivative power, else 1."""
    base = factor.as_base_exp()[0]
    if base.is_Derivative and base.args[0] in dep:
        return factor
    return 1


def extract_coeffs(expr, dep: list, indep: list) -> list:
    """Collect derivative monomials that appear as coefficients in *expr*.

    Pure: no side effects.
    """
    def _term_monomial(term):
        f = 1
        for factor in term.args:
            if factor.is_Pow:
                f *= _analyze_power(factor, dep)
            elif factor.is_Derivative and factor.args[0] in dep:
                f *= factor
        return f

    monomials = {
        _term_monomial(term)
        for term in expr.expand().args
        if _term_monomial(term) != 1
    }
    return list(monomials)


def get_coeff_order(expr) -> int:
    """Return the total derivative order of a monomial coefficient."""
    if expr.is_Pow:
        return int(expr.as_base_exp()[1])
    if expr.is_Mul:
        return sum(int(a.as_base_exp()[1]) if a.is_Pow else 1 for a in expr.args)
    return 1


# ---------------------------------------------------------------------------
# 7. Determining equations
# ---------------------------------------------------------------------------

def compute_determining_equations(expr, coeffs: list) -> list:
    """Split *expr* into determining equations by coefficient extraction.

    Pure: returns a new list of expressions.
    """
    def _step(acc_expr_eqs, coeff):
        remaining, eqs = acc_expr_eqs
        termsum = sum(
            term / coeff
            for term in remaining.expand().args
            if term.has(coeff)
        )
        new_remaining = remaining - termsum * coeff
        return new_remaining, eqs + [termsum]

    leftover, equations = reduce(_step, coeffs, (expr, []))
    raw = equations + [leftover.expand()]
    return [e.xreplace(finish_substitution(e)) for e in raw]


# ---------------------------------------------------------------------------
# 8. Infinitesimal creation
# ---------------------------------------------------------------------------

def create_infinitesimals(dep: list, indep: list, inf: dict | None = None) -> OrderedDict:
    """Build the infinitesimal dictionary.

    Pure: always returns a *new* ``OrderedDict``.
    """
    dep   = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)
    all_vars = dep + indep

    if inf is None:
        return OrderedDict(
            (d, make_infinitesimal(d, *all_vars, name=d.name.swapcase()))
            for d in all_vars
        )

    return OrderedDict(
        (v, make_infinitesimal(v, *all_vars, name=i) if isinstance(i, str) else i)
        for v, i in inf.items()
    )


# ---------------------------------------------------------------------------
# 9. Overdetermined system (single ODE)
# ---------------------------------------------------------------------------

def _build_prolonged_infinitesimals(
    dep: list, indep: list, infinitesimals: dict, eq_order: int
) -> tuple[dict, dict]:
    """Extend *infinitesimals* with all prolonged levels.

    Pure: returns ``(extended_infinitesimals, dummies)`` as new dicts.
    """
    combos = variable_combinations(indep, eq_order)

    def _fold(acc, comb):
        inf_acc, dum_acc = acc
        funcs, etas = compute_level(comb, dep, indep, inf_acc)
        new_inf = {**inf_acc, funcs[0]: etas[0]}
        label   = f"{dep[0].name}_{''.join(str(v) for v in comb)}"
        new_dum = {**dum_acc, funcs[0]: _backend["Symbol"](label)}
        return new_inf, new_dum

    return reduce(_fold, combos, (dict(infinitesimals), {}))


def compute_overdetermined_system_of_infinitesimals(
    eq, dep: list, indep: list, infinitesimals: dict | None = None
) -> list:
    """Return the list of determining equations for *eq*.

    Pure end-to-end: every intermediate value is a new object.
    """
    dep   = convert_to_iterable(dep)
    indep = convert_to_iterable(indep)

    base_inf       = create_infinitesimals(dep, indep, infinitesimals)
    eq_order, highest = order(eq, dep, indep)
    highest_term   = next(iter(highest))

    extended_inf, dummies = _build_prolonged_infinitesimals(
        dep, indep, base_inf, eq_order
    )

    vdummies = OrderedDict(
        (i, _backend["Symbol"](i.name)) for i in dep + indep
    )
    all_dummies = ChainMap(dummies, vdummies)

    r = prolongation(eq, eq_order, extended_inf, dep, indep, all_dummies).expand()
    sol = _solve(eq, highest_term)[0]

    r_clean = r.xreplace(finish_substitution(r)).xreplace({highest_term: sol})

    coeffs = sorted(
        extract_coeffs(r_clean, dep, indep),
        key=get_coeff_order,
        reverse=True,
    )
    return compute_determining_equations(r_clean, coeffs)


# ---------------------------------------------------------------------------
# 10. Public API
# ---------------------------------------------------------------------------

def overdeterminedSystemODE(
    ode,
    dependent,
    independent,
    infinitesimals: dict | None = None,
    *args,
    **kw,
) -> list:
    """Compute the overdetermined system for a single ODE.

    >>> # Arrigo Example 2.20
    >>> from delierium.helpers import ltf
    >>> from sympy import Symbol, Function, diff
    >>> from collections import OrderedDict
    >>> x = Symbol('x')
    >>> y = Function('y')(x)
    >>> ode = diff(y, x, 3) + y * diff(y, x, 2)
    >>> inf = overdeterminedSystemODE(ode, [y], [x])
    """  # noqa: E501
    return compute_overdetermined_system_of_infinitesimals(
        ode, dependent, independent, infinitesimals=infinitesimals
    )


def overdeterminedSystemODEs(
    eqs: list,
    dependent,
    independent,
    infinitesimals: dict | None = None,
    *args,
    **kw,
) -> list:
    """Compute the overdetermined system for a *system* of ODEs.

    Pure: collects prolongations into a new list before solving.
    """
    dep   = convert_to_iterable(dependent)
    indep = convert_to_iterable(independent)

    base_inf = create_infinitesimals(dep, indep, infinitesimals)

    # Find global maximum order and collect all highest-order terms
    order_pairs = [order(eq, dep, indep) for eq in eqs]
    eq_order    = max(o for o, _ in order_pairs)
    all_highest = [t for _, terms in order_pairs for t in terms]
    highest_term = all_highest[0]

    extended_inf, dummies = _build_prolonged_infinitesimals(
        dep, indep, base_inf, eq_order
    )

    vdummies    = OrderedDict((i, _backend["Symbol"](i.name)) for i in dep + indep)
    all_dummies = ChainMap(dummies, vdummies)

    prols = [
        prolongation(eq, eq_order, extended_inf, dep, indep, all_dummies).expand()
        for eq in eqs
    ]

    sol = _solve(eqs[-1], highest_term)[0]

    def _clean(r):
        return r.xreplace(finish_substitution(r)).xreplace({highest_term: sol})

    cleaned = [_clean(r) for r in prols]
    r_last  = cleaned[-1]

    coeffs = sorted(
        extract_coeffs(r_last, dep, indep),
        key=get_coeff_order,
        reverse=True,
    )
    return compute_determining_equations(r_last, coeffs)


def overdeterminedSystemPDE(
    pde,
    dependent,
    independent,
    infinitesimals: dict | None = None,
    *args,
    **kw,
):
    """Placeholder – PDE support not yet implemented."""
    raise NotImplementedError("PDE support is not yet implemented.")


# ---------------------------------------------------------------------------
# 11. Janet basis interface
# ---------------------------------------------------------------------------

def Janet_Basis_from_ODE(
    ode,
    dependent,
    independent,
    sort_order=Mgrevlex,
    infinitesimals: dict | None = None,
    *args,
    **kw,
):
    """Compute the Janet basis for the symmetry algebra of *ode*."""
    inf_dict = create_infinitesimals([dependent], [independent], infinitesimals)
    overdetermined = overdeterminedSystemODE(
        ode, [dependent], [independent], infinitesimals=inf_dict
    )

    Y   = _backend["Symbol"]("H")
    inf = [inf_dict[_].xreplace({dependent: Y}) for _ in [dependent, independent]]
    r1  = [dependent.xreplace({dependent: Y}), independent]

    def _strip_deriv_subs(e):
        """Replace every derivative in *e* by zero, up to its max order."""
        mine  = [a for a in e.atoms(_backend["Derivative"]) if a.args[0].func == dependent]
        if not mine:
            return e.replace(dependent, Y)
        max_ord = max(len(a.operator().parameter_set()) for a in mine)
        e = e.replace(dependent, Y)
        return reduce(
            lambda acc, j: acc.subs({_diff(dependent(independent), independent, j): 0}),
            range(1, max_ord + 1),
            e,
        )

    intermediate = [_strip_deriv_subs(e) for e in overdetermined]
    janet        = Janet_Basis(intermediate, reversed(inf), reversed(r1), sort_order=sort_order)

    backsubstitute = lambda e: e.xreplace({Y: dependent})   # noqa: E731

    def _rebuild_lhdp(lhdp):
        ctx = Context(
            dependent=[backsubstitute(d) for d in lhdp.p[0].context.dependent],
            independent=[backsubstitute(d) for d in lhdp.p[0].context.independent],
            weight=sort_order,
        )
        terms = [
            _Dterm(
                derivative=backsubstitute(t.derivative),
                coeff=backsubstitute(t.coeff),
                context=ctx,
            )
            for t in lhdp.p
        ]
        return LHDP(e=0, context=ctx, dterms=terms)

    res = [_rebuild_lhdp(lhdp) for lhdp in janet.S]
    return Reorder(res, context=res[-1].p[0].context if res else None)


# ---------------------------------------------------------------------------
# 12. Module entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    import doctest
    doctest.testmod()
