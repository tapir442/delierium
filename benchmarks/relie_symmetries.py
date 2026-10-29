"""Francesco Oliveri's ReLie (REDUCE, with CRACK) on the symmetry catalogue.

Internal benchmark. ReLie (http://mat521.unime.it/oliveri, no licence
stated, so not committed) is expected in benchmarks/relie/relie.red. Same
two phases and comparison as reduce_symmetries.py (LIEPDE); only the input
differs: ReLie names derivatives u1_x1x2, solves the equations for the
leading derivatives itself, and must be told which derivatives occur
non-polynomially.

    uv run python benchmarks/relie_symmetries.py run [--only TEXT] [--jobs 2]
    uv run python benchmarks/relie_symmetries.py compare benchmarks/relie-raw.jsonl
"""

from pathlib import Path

from sympy import Derivative, Symbol
from sympy.core.function import AppliedUndef

import reduce_symmetries as rs
from delierium.helpers import finish_substitution
from delierium.infinitesimals import (
    _canonical_derivatives_of,
    _exact_numbers,
    _leading_derivative,
    order,
)

RELIE = Path(__file__).resolve().parent / "relie" / "relie.red"


def jet_name(d, indep, dep):
    """u1_x1x1x2 for Derivative(u(x, y), (x, 2), y), variables in xvar order."""
    counts = dict(d.variable_count)
    return Symbol(f"u{dep.index(d.expr) + 1}_"
                  + "".join(f"x{i}" * counts.get(v, 0) for i, v in enumerate(indep, 1)))


def to_relie(entry):
    """ReLie input for entry and the names to map back."""
    if not RELIE.exists():
        raise rs.Unsupported(f"{RELIE} missing")
    indep, dep = entry.variables()
    eqs = [
        finish_substitution(_exact_numbers(_canonical_derivatives_of(e, dep)))
        for e in entry.parsed_equations()
    ]
    if len(eqs) != len(dep):
        raise rs.Unsupported("not as many equations as functions")
    others = sorted({f.func for e in eqs for f in e.atoms(AppliedUndef)} - {d.func for d in dep},
                    key=str)
    parameters = sorted({s for e in eqs for s in e.free_symbols} - set(indep), key=str)
    names = {f"x{i}": v.name for i, v in enumerate(indep, 1)}
    names |= {f"u{i}": d.func.__name__ for i, d in enumerate(dep, 1)}
    names |= {f"p{i}": s.name for i, s in enumerate(parameters)}
    names |= {f"f{i}": f.__name__ for i, f in enumerate(others)}
    to = {v: Symbol(f"x{i}") for i, v in enumerate(indep, 1)}
    to |= {s: Symbol(f"p{i}") for i, s in enumerate(parameters)}

    def jet(e):
        ds = [d for d in e.atoms(Derivative) if d.expr in dep]
        e = e.xreplace({d: jet_name(d, indep, dep) for d in ds})
        return e.xreplace({d: Symbol(f"u{a}") for a, d in enumerate(dep, 1)})

    jetorder, leadders, nonpoly, diffeqs = 0, [], set(), []
    for e in eqs:
        _, highest = order(e, dep, indep)
        if not highest:
            raise rs.Unsupported("an equation without derivatives")
        jetorder = max([jetorder] + [d.derivative_count for d in e.atoms(Derivative)
                                     if d.expr in dep])
        lead = jet(_leading_derivative(e, highest, dep))
        if lead in leadders:
            raise rs.Unsupported("two equations with the same leading derivative")
        leadders.append(lead)
        j = jet(e)
        nonpoly |= {s for s in j.free_symbols if "_" in s.name and not j.is_polynomial(s)}
        diffeqs.append(rs.reduce_expr(j, indep, dep, others, to))
    variables = [f"x{i}" for i in range(1, len(indep) + 1)]
    functions = [f"u{i}" for i in range(1, len(dep) + 1)]
    lines = ["off nat $", "linelength 100000 $", f'in "{RELIE}"$']
    if others:
        lines.append(f"operator {', '.join(f'f{i}' for i in range(len(others)))} $")
    lines += [
        f"jetorder:={jetorder} $",
        f"xvar:={{{', '.join(variables)}}} $",
        f"uvar:={{{', '.join(functions)}}} $",
        f"diffeqs:={{{', '.join(diffeqs)}}} $",
        f"leadders:={{{', '.join(map(str, leadders))}}} $",
    ]
    if nonpoly:
        lines.append(f"nonpolyders:={{{', '.join(sorted(map(str, nonpoly)))}}} $")
    checks = ", ".join(f'" ", df(c, {v})' for v in variables + functions)
    lines += [
        "relie(4) $",
        'for each cs in symmetries do << write "CASE";',
        '  for each c in first cs do write "COND ", c;',
        '  for each s in second cs do write "SOL ", lhs s, " := ", rhs s;',
        f'  for each c in third cs do write "CONST ", c, {checks} >>;',
        "end;",
    ]
    return "\n".join(lines) + "\n", names


if __name__ == "__main__":
    rs.main(convert=to_relie, name="relie")
