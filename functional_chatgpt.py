import sympy as sp
from itertools import combinations_with_replacement
from functools import reduce
from more_itertools import flatten
from typing import List, Tuple, Dict, Set, Any

sp.init_printing(use_latex=True)

# ---------------------------------------------------------------------
# Basic utilities
# ---------------------------------------------------------------------

def make_infinitesimal(v: sp.Symbol, *variables: sp.Symbol, name: str = "") -> sp.Function:
    return sp.Function(name or v.name.swapcase())(*variables)


def variable_combinations(variables: List[sp.Symbol], order: int) -> List[Tuple[sp.Symbol, ...]]:
    return [
        comb
        for i in range(1, order + 1)
        for comb in combinations_with_replacement(variables, i)
    ]


def func_diff(fun: sp.Function, var: sp.Symbol | sp.Function) -> sp.Expr:
    if var.is_Function or var.is_Derivative:
        d = sp.Symbol("d")
        return fun.xreplace({var: d}).diff(d).xreplace({d: var}).doit()
    return sp.Derivative(fun, var).doit()

# ---------------------------------------------------------------------
# Recursive prolongation helpers
# ---------------------------------------------------------------------

def _initial_level(dependents, infinitesimals):
    return dependents, [infinitesimals[f] for f in dependents]


def _next_level(funcs, etas, x, indeps, infinitesimals):
    def evolve(pair):
        func, eta = pair
        base = func_diff(eta, x)
        correction = reduce(
            lambda acc, v: acc - func_diff(func, v) * func_diff(infinitesimals[v], x),
            indeps,
            base,
        )
        return func_diff(func, x), correction

    return list(zip(*map(evolve, zip(funcs, etas))))


def compute_level(order_vars, dependents, indeps, infinitesimals):
    funcs, etas = _initial_level(dependents, infinitesimals)

    for x in order_vars:
        funcs, etas = _next_level(funcs, etas, x, indeps, infinitesimals)

    return funcs, etas

# ---------------------------------------------------------------------
# Substitution utilities
# ---------------------------------------------------------------------

def finish_substitution(expr: sp.Expr) -> Dict[sp.Subs, sp.Expr]:
    return {
        s: s.args[0].xreplace(dict(zip(s.bound_symbols, s.args[2])))
        for s in expr.atoms(sp.Subs)
    }

# ---------------------------------------------------------------------
# LTF (Lie Traditional Form)
# ---------------------------------------------------------------------

def _derivative_index(deriv):
    idx = []
    for sym, cnt in deriv.args[1:]:
        label = sym.name if sym.is_Function else str(sym)
        idx.extend([label] * cnt)
    return "{" + "".join(sorted(idx)) + "}"


def _replace_derivatives(expr):
    symbols = {}
    for d in expr.atoms(sp.Derivative):
        name = f"{d.args[0].name}_{_derivative_index(d)}"
        symbols.setdefault(name, sp.Symbol(name))
        expr = expr.xreplace({d: symbols[name]})
    return expr


def _replace_simple_derivatives(expr, deps, indeps):
    replacements = {}
    for d in expr.atoms(sp.Derivative):
        if d.args[0] in deps:
            if len(indeps) == 1:
                replacements[d] = sp.Symbol(
                    f"{d.args[0].name}{''.join("'" * d.args[-1][1])}"
                )
            else:
                s = "".join(
                    (a[0].name if a[0].is_Function else str(a[0])) * a[1]
                    for a in d.args[1:]
                )
                replacements[d] = sp.Symbol(f"{d.args[0].name}_{{{s}}}")
    return expr.xreplace(replacements)


def ltf(expr: sp.Expr, deps: List[sp.Function], indeps: List[sp.Symbol]) -> sp.Expr:
    expr = expr.xreplace(finish_substitution(expr))
    expr = _replace_derivatives(expr)
    expr = _replace_simple_derivatives(expr, deps, indeps).expand().simplify()
    try:
        display(expr)
    except Exception:
        print(expr)
    return expr

# ---------------------------------------------------------------------
# Equation analysis
# ---------------------------------------------------------------------

def order(expr, deps, _):
    max_order = 0
    max_deriv = set()

    for d in expr.expand().atoms(sp.Derivative):
        if d.args[0] in deps:
            ord_ = sum(cnt for _, cnt in d.args[1:])
            if ord_ > max_order:
                max_deriv, max_order = {d}, ord_
            elif ord_ == max_order:
                max_deriv.add(d)

    return max_order, max_deriv


def rewrite_diff_equation_with_infinitesimal(expr, infinitesimals):
    terms = expr.expand().args if expr.is_Add else [expr]

    def rewrite(term):
        factors = term.args if not term.is_Derivative else [term]
        return reduce(lambda a, f: a * infinitesimals.get(f, f), factors, 1)

    return sum(map(rewrite, terms))


def prolongation(expr, _, infinitesimals, *__):
    return rewrite_diff_equation_with_infinitesimal(expr, infinitesimals)

# ---------------------------------------------------------------------
# Coefficient extraction
# ---------------------------------------------------------------------

def analyze_power(factor, deps):
    base = factor.as_base_exp()[0]
    return factor if (base.is_Derivative or base.is_Function) and base.args[0] in deps else 1


def extract_coeffs(expr, deps, _):
    result = set()

    for term in expr.expand().args:
        f = reduce(
            lambda acc, x: acc * (
                analyze_power(x, deps) if x.is_Pow else x
                if (x.is_Derivative or x.is_Function) and x.args[0] in deps
                else 1
            ),
            term.args,
            1,
        )
        if f != 1:
            result.add(f)

    return list(result)


def get_coeff_order(expr):
    if expr.is_Pow:
        return expr.as_base_exp()[1]
    if expr.is_Mul:
        return sum(a.as_base_exp()[1] if a.is_Pow else 1 for a in expr.args)
    return 1


def compute_determining_equations(expr, coeffs):
    equations = []

    for c in coeffs:
        r = sum(t / c for t in expr.expand().args if t.has(c))
        equations.append(r)
        expr -= r * c

    equations.append(expr)
    return equations

# ---------------------------------------------------------------------
# Main solver
# ---------------------------------------------------------------------

def compute_overdetermined_system_of_infinitesimals(eq, dep, indep, infinitesimals):
    eq_order, highest = order(eq, dep, indep)
    combos = variable_combinations(indep, eq_order)

    for comb in combos:
        funcs, etas = compute_level(comb, dep, indep, infinitesimals)
        infinitesimals[funcs[0]] = etas[0]

    r = prolongation(eq, 2, infinitesimals, dep, indep)
    sol = sp.solve(eq, list(highest)[0])[0]
    r = r.xreplace(finish_substitution(r))
    r = r.xreplace({list(highest)[0]: sol})

    coeffs = sorted(
        extract_coeffs(r, dep, indep),
        key=get_coeff_order,
        reverse=True,
    )

    return compute_determining_equations(r, coeffs)

# ---------------------------------------------------------------------
# Examples (UNCHANGED)
# ---------------------------------------------------------------------

def main():
    t, x = sp.symbols("t x")
    u = sp.Function("u")(t, x)
    heq = sp.Derivative(u, t) - sp.Derivative(u, x, x)

    independents = [t, x]
    dependents = [u]

    infinitesimals = {
        x: make_infinitesimal(x, t, x, u, name="X"),
        t: make_infinitesimal(t, t, x, u, name="T"),
        u: make_infinitesimal(u, t, x, u, name="U"),
    }

    result = compute_overdetermined_system_of_infinitesimals(
        eq=heq,
        dep=dependents,
        indep=independents,
        infinitesimals=infinitesimals,
    )

    for eq in result:
        ltf(eq, [u], [x, t])

    return result


def main2():
    y, x = sp.symbols("y x")
    u = sp.Function("u")(x, y)
    laplace_eq = sp.Derivative(u, y, y) + sp.Derivative(u, x, x)

    independents = [y, x]
    dependents = [u]

    infinitesimals = {
        x: make_infinitesimal(x, x, y, u, name="X"),
        y: make_infinitesimal(y, x, y, u, name="Y"),
        u: make_infinitesimal(u, x, y, u, name="U"),
    }

    result = compute_overdetermined_system_of_infinitesimals(
        eq=laplace_eq,
        dep=dependents,
        indep=independents,
        infinitesimals=infinitesimals,
    )

    for eq in set(result):
        ltf(eq, dependents, independents)

    return result


if __name__ == "__main__":
    main()
    print("." * 80)
    main2()
