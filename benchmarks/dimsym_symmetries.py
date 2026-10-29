"""Sherring, Prince and Jerie's DIMSYM (REDUCE) on the symmetry catalogue.

Internal benchmark. DIMSYM 2.3 (https://github.com/reduce-algebra/dimsym, not
to be redistributed in modified form, so not committed) is expected in
benchmarks/dimsym/src/dimsym23.red. Same two phases and comparison as
reduce_symmetries.py (LIEPDE); only the input differs: DIMSYM writes x(j),
u(i) and derivatives u(i, j1, ..., jn) (higher indices first), needs the
equations solved for their leading derivatives, and arbitrary functions of
the equations as free unknowns (operators) of variables, not of expressions.

    uv run python benchmarks/dimsym_symmetries.py run [--only TEXT] [--jobs 2]
    uv run python benchmarks/dimsym_symmetries.py compare benchmarks/dimsym-raw.jsonl
"""

import re
from pathlib import Path

from sympy import Derivative, Symbol, solve
from sympy.core.function import AppliedUndef

import reduce_symmetries as rs
from delierium.helpers import finish_substitution
from delierium.infinitesimals import (
    _canonical_derivatives_of,
    _exact_numbers,
    _leading_derivative,
    order,
)

DIMSYM = Path(__file__).resolve().parent / "dimsym" / "src" / "dimsym23.red"


def translate(entry, descending=True):
    """entry in the notation x(j), u(i), u(i, j1, ..., jn) (DIMSYM, SPDE):
    names to map back, the arbitrary functions {name: arguments}, and per
    equation (leading derivative, equation, solutions for the leading
    derivative)."""
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
    marks = {}

    def mark(text):
        m = Symbol(f"MARK{len(marks)}")
        marks[m.name] = text
        return m

    def coordinate(a):
        """DIMSYM's name of x, u or a derivative of u."""
        if a in indep:
            return f"x({indep.index(a) + 1})"
        if a in dep:
            return f"u({dep.index(a) + 1})"
        if isinstance(a, Derivative) and a.expr in dep:
            js = sorted((indep.index(v) + 1 for v, k in a.variable_count for _ in range(k)),
                        reverse=descending)
            return f"u({dep.index(a.expr) + 1},{','.join(map(str, js))})"
        raise rs.Unsupported(f"arbitrary function of {a}")

    depends = {}

    def text(e):
        # arbitrary functions and their derivatives: free unknowns
        for d in sorted(e.atoms(Derivative), key=str):
            if d.expr in dep:
                continue
            if not isinstance(d.expr, AppliedUndef):
                raise rs.Unsupported("derivative of an expression")
            name = f"f{others.index(d.expr.func)}"
            depends[name] = [coordinate(a) for a in d.expr.args]
            spec = [f"{coordinate(v)}, {k}" if k > 1 else coordinate(v)
                    for v, k in d.variable_count]
            call = f"{name}({', '.join(depends[name])})"
            e = e.xreplace({d: mark(f"df({call}, {', '.join(spec)})")})
        for f in sorted(e.atoms(AppliedUndef), key=str):
            if f.func in others:
                name = f"f{others.index(f.func)}"
                depends[name] = [coordinate(a) for a in f.args]
                e = e.xreplace({f: mark(f"{name}({', '.join(depends[name])})")})
        for d in sorted(e.atoms(Derivative), key=str):
            e = e.xreplace({d: mark(coordinate(d))})
        for d in dep:
            e = e.xreplace({d: mark(coordinate(d))})
        e = e.xreplace({v: mark(coordinate(v)) for v in indep})
        e = e.xreplace({s: Symbol(f"p{i}") for i, s in enumerate(parameters)})
        out = str(e)
        out = re.sub(r"\bE\b", "e", out)
        out = re.sub(r"\bAbs\(", "abs(", out)
        for m, value in sorted(marks.items(), key=lambda kv: -len(kv[0])):
            out = out.replace(m, value)
        return out

    equations, chosen = [], set()
    for e in eqs:
        _, highest = order(e, dep, indep)
        if not highest:
            raise rs.Unsupported("an equation without derivatives")
        lead = _leading_derivative(e, highest, dep)
        if lead in chosen:
            raise rs.Unsupported("two equations with the same leading derivative")
        chosen.add(lead)
        equations.append((text(lead), text(e), [text(x) for x in solve(e, lead)]))
    return names, depends, equations


def to_dimsym(entry):
    """DIMSYM input for entry and the names to map back."""
    if not DIMSYM.exists():
        raise rs.Unsupported(f"{DIMSYM} missing")
    names, depends, equations = translate(entry)
    loads = []
    for lead, _, sols in equations:
        if len(sols) != 1:
            raise rs.Unsupported(f"{len(sols)} solutions for the leading derivative")
        loads.append(f"loaddeq({lead} = {sols[0]})$")
    n, m = len(entry.independent), len(entry.dependent)
    lines = ["off nat $", "linelength 100000 $", f'in "{DIMSYM}"$']
    for name, args in depends.items():  # operator form: printed with arguments
        lines += [f"operator {name} $", f"freeunknown {name}({', '.join(args)}) $"]
    checks = ", ".join([f'" ", df(c(k), x({j}))' for j in range(1, n + 1)]
                       + [f'" ", df(c(k), u({i}))' for i in range(1, m + 1)])
    lines += loads + [
        "mkdets(point)$",
        "solvedets(std)$",
        "showdets()$",
        'write "CASE";',
        # deteqn(i) stays unevaluated when unset
        'for i:=1:1000 do if freeof(deteqn(i), deteqn) then write "COND ", deteqn(i);',
    ]
    lines += [f'write "SOL xi_x{j} := ", xi({j});' for j in range(1, n + 1)]
    lines += [f'write "SOL eta_u{i} := ", phi({i});' for i in range(1, m + 1)]
    lines += ["alldets := for i:=1:1000 join if freeof(deteqn(i), deteqn) then {deteqn(i)}"
              " else {} $",
              "for k:=1:1000 do if not freeof({symvec, alldets}, c(k)) then "
              f'write "CONST c_", k, {checks};']
    # an infinitesimal DIMSYM left undetermined is an unknown itself
    for j in range(1, n + 1):
        lines.append(f'if not freeof(xi({j}), xi) then write "CONST xi_{j}", '
                     + checks.replace("c(k)", f"xi({j})") + ";")
    for i in range(1, m + 1):
        lines.append(f'if not freeof(phi({i}), phi) then write "CONST phi_{i}", '
                     + checks.replace("c(k)", f"phi({i})") + ";")
    lines.append("end;")
    return "\n".join(lines) + "\n", names


if __name__ == "__main__":
    rs.main(convert=to_dimsym, name="dimsym")
