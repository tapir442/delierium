from collections import ChainMap
from functools import reduce
from itertools import combinations_with_replacement
from typing import Any

import sympy as sp

sp.init_printing(use_latex=True)

def finish_substitution(expr):
    subs = set(expr.atoms(sp.Subs))
    subs_dic = {}
    for s0 in subs:
        bound = s0.bound_symbols
        der = s0.args[0]
        var = s0.args[2]
        subs_dic[s0] = der.xreplace(dict(zip(bound, var)))
    return subs_dic

def ltf(expr, dep, indep):
    """Lie Traditional Form."""
    #set_trace()
    functions = expr.atoms(sp.Function)
    reps = {}
    for fun in [_ for _ in functions if _ not in dep]:
        # Consider the case that some functions won't have the name
        # attribute e.g. Abs of an elementary function
        try:
            reps[fun] = sp.Symbol(fun.name) # Otherwise functions with greek symbols aren't replaced
        except AttributeError:
            continue
    # first, resolve the dangling substitutions. Don't know why the
    # substitution is not done, but it seems that it has to do with
    # that a bound variable is within a function which is used as
    # a derivation argument
    subs_dic = finish_substitution(expr)
    output = expr
    output = output.xreplace(subs_dic)
    used_symbols = {}
    for deriv in output.atoms(sp.Derivative):
        # there is room to improve: collect indices and sort
        subindex = []
        for func_or_symbol, count in deriv.args[1:]:
            if func_or_symbol.is_Function:
                subindex.extend([func_or_symbol.name] * count)
            elif func_or_symbol.is_Symbol:
                subindex.extend([f"{func_or_symbol}"] * count)
            else:
                raise ValueError(f"{func_or_symbol=} has class {func_or_symbol.__class__=}")
        subindex = "{" + "".join(sorted(subindex)) + "}"

        fluffi = f"{deriv.args[0].name}_{subindex}"
        if fluffi in used_symbols:
            output = output.xreplace({deriv: used_symbols[fluffi]})
        else:
            s = sp.Symbol(fluffi)
            used_symbols[fluffi] = s
            output = output.xreplace({deriv: used_symbols[fluffi]})

    dreps2 = {}

    if len(indep) == 1:
        # the original dependent variables should be written with primes
        dreps2 = dict([(deriv, (sp.Symbol(deriv.output.subs(reps) +
                                ' '.join("'" * deriv.args[-1][1]))))  \
                 for deriv in output.atoms(sp.Derivative) if deriv.args[0] in dep])
    else:
        derivatives = [_ for _ in output.atoms(sp.Derivative) if _.args[0] in dep]
        for dev in derivatives:
            s = ""
            for arg in dev.args[1:]:
                match type(arg[0]):
                    case sp.Function:
                        n = arg[0].name
                    case sp.Symbol:
                        n = str(arg[0])
                    case _:
                        raise ValueError(f"{arg[0]} is type {type(arg[0])}")
                s += n*arg[1]
            dreps2[dev] = sp.Symbol(f"{dev.args[0].name}_"  + "{" +f"{s}" + "}")

    fundic = dict([(_, sp.Symbol(_.name)) for _ in dep])
    output = output.xreplace(dreps2).xreplace(fundic)
    display(output)

def variable_combinations(variables: list[sp.Symbol], order:int) -> list(tuple[sp.Symbol]):
    return reduce(
        lambda acc, i: acc + list(map(list, combinations_with_replacement(variables, i))),
        range(1, order + 1),
        [])

def make_infinitesimal(v, *variables, name=""):
    return sp.Function(f'{v.name.swapcase() if not name else name}')(*variables)

def order(expr, dep, indep):
    max_order = 0
    max_deriv = set()
    k = expr.expand().atoms(sp.Derivative)
    for atom in k:
        if atom.args[0].name in [_.name for _ in dep]:
            _order = sum(cnt[1] for cnt in atom.args[1:])
            if max_order == _order:
                max_deriv |= set([atom])
            elif max_order < _order:
                max_deriv = set([atom])
                max_order = _order
    # XXX: return coefficients, too. When some coefficients are -1, or 1, or numerical
    # return only those derivs
    return (max_order, max_deriv)

def func_diff(fun:sp.Function, var:sp.Symbol | sp.Function) -> sp.Derivative:
    if var.is_Function or var.is_Derivative:
        d = sp.Symbol('d')
        r = fun.xreplace({var: d}).diff(d).xreplace({d: var}).doit()
    else:
        r = sp.Derivative(fun, var).doit()
    return r


def compute_level(deriv_vars_order: list[Any], dep, indep, infinitesimals):
    """Compute all derivatives and infinitesimals for a given derivative order.
    Extended Gamma operator (Arrigo, eq 2.85, or Schwarz, eq. 5.10)
    """
    v = deriv_vars_order[-1]
    # Base case (first order)
    if len(deriv_vars_order) == 1:
        funcs = dep
        etas = [infinitesimals[f] for f in funcs]
    else:
        prev_order = deriv_vars_order[:-1]
        funcs, etas = compute_level(prev_order, dep, indep, infinitesimals)
    # Compute current derivatives and infinitesimals functionally
    results = [
                (
                    func_diff(func, v),
                    reduce(
                        lambda acc, var: acc - func_diff(func, var)
                        * func_diff(infinitesimals[var], v),
                        indep,
                        func_diff(eta, v)
                    )
                )
                for func, eta in zip(funcs, etas)
            ]
    # Split result into separate lists
    funcs_next, etas_next = zip(*results)
    return list(funcs_next), list(etas_next)

def prolongation(expr, n, infinitesimals, dep, indep, dummies):
    for inf in infinitesimals:
        d = finish_substitution(infinitesimals[inf])
        infinitesimals[inf] = infinitesimals[inf].xreplace(d)
    acc = 0
    reverse_dummies = {}
    for k, v in dummies.items():
        reverse_dummies[v] = k
    for _ in infinitesimals:
        acc += infinitesimals[_] * func_diff(expr.xreplace(dummies), _.xreplace(dummies)).xreplace(reverse_dummies)

    return acc

def extract_coeffs(expr, dep, indep):
    def analyze_power(factor):
        base = factor.as_base_exp()[0]
        if base.is_Derivative:
            if base.args[0] in dep:
                return factor
        #if base.is_Function:
        #    if base in dep:
        #        return factor
        return 1
    args = expr.expand().args
    all_i_need = set()
    for term in args:
        local_term = term.args
        f = 1
        for factor in local_term:
            if factor.is_Pow:
                f *= analyze_power(factor)
            elif factor.is_Derivative:
                if factor.args[0] in dep:
                    f *= factor
            elif factor.is_Function:
                #if factor in dep:
                #    f *= factor
                pass
            elif factor.is_number:
                pass
            else:
                # XXx: explore with heateq
                pass
        if f != 1:
            all_i_need.add(f)
    return list(all_i_need)

def get_coeff_order(expr):
    acc = 0
    if expr.is_Pow:
        acc += expr.as_base_exp()[1]
    elif expr.is_Mul:
        for a in expr.args:
            if a.is_Pow:
                acc += a.as_base_exp()[1]
            else:
                acc += 1
    else:
        acc += 1
    return acc

def compute_determining_equations(expr, coeffs):
    acc = []
    for coeff in coeffs:
        termsum = sum(term/coeff for term in expr.expand().args if term.has(coeff))
        acc.append(termsum)
        expr -= termsum * coeff
    acc.append(expr.expand())
    return acc

def compute_overdetermined_system_of_infinitesimals(eq, dep, indep, infinitesimals):
    
    eq_order, highest_term = order(eq, dep, indep)
    highest_term = list(highest_term)[0]
    combos = variable_combinations(indep, eq_order)

    dummies = {}

    for comb in combos:
        funcs, etas = compute_level(comb, dep, indep, infinitesimals)
        infinitesimals[funcs[0]] = etas[0]
        dummies[funcs[0]] = sp.Symbol(f"{dep[0].name}_{"".join([str(v) for v in comb])}")

    vdummies = {}
    for i in dep + indep:
        vdummies[i] = sp.Symbol(i.name)
    
    _dummies = ChainMap(dummies, vdummies)
    r = prolongation(eq, eq_order, infinitesimals, dep, indep, _dummies)
    
    sol = sp.solve(eq, highest_term)[0]
    r = r.xreplace(finish_substitution(r))
    r = r.xreplace({highest_term: sol})
    coeffs = sorted(
        extract_coeffs(r, dep, indep),
        key=get_coeff_order,
        reverse=True,
    )
    return compute_determining_equations(r, coeffs)


