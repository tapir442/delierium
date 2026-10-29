"""Hereman's symmgrp2020 (Maxima) on the symmetry catalogue.

Internal benchmark. symmgrp2020 computes the determining equations of the Lie
point symmetries (and simplifies them a little: single-term equations are
used to drop terms). For each catalogue entry it runs in its own Maxima
process; its equations are read back, delierium computes their Janet basis,
and the dimension of the solution space is compared with the catalogue's.

    uv run python benchmarks/symmgrp_symmetries.py [--only TEXT] [--timeout 120]

https://github.com/willyhereman/LiePointSymmetries-Maxima, cloned into
benchmarks/symmgrp-maxima (not committed).
"""

import argparse
import json
import re
import signal
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from sympy import (
    Derivative,
    E,
    Function,
    I,
    Symbol,
    oo,
    pi,
    sympify,
)
from sympy.core.function import AppliedUndef
from sympy.parsing.sympy_parser import parse_expr

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from delierium.infinitesimals import (  # noqa: E402
    _canonical_derivatives_of,
    _exact_numbers,
    _leading_derivative,
    order,
)
from delierium.helpers import finish_substitution  # noqa: E402
from delierium.janet_basis import JanetBasis  # noqa: E402
from tests.symmetry_catalog import CATALOG, INFINITE  # noqa: E402

HERE = Path(__file__).resolve().parent
SYMMGRP = HERE / "symmgrp-maxima" / "symmgrp2020" / "symmgrp2020.max"


class Unsupported(Exception):
    pass


def to_symmgrp(entry):
    """The Maxima input for entry: (text, parameter names)."""
    indep, dep = entry.variables()
    p, q = len(indep), len(dep)
    eqs = [
        finish_substitution(_exact_numbers(_canonical_derivatives_of(e, dep)))
        for e in entry.parsed_equations()
    ]
    # arbitrary functions F(u), k(u), ... as undefined Maxima functions FUN0, ...
    # (renamed: phi is symmgrp's own)
    others = sorted({f.func for e in eqs for f in e.atoms(AppliedUndef)} - {d.func for d in dep},
                    key=str)
    names = {f"FUN{k}": f.__name__ for k, f in enumerate(others)}
    functions = {f: Function(f"FUN{k}") for k, f in enumerate(others)}
    eqs = [
        e.replace(lambda a: isinstance(a, AppliedUndef) and a.func in functions,
                  lambda a: functions[a.func](*a.args))
        for e in eqs
    ]
    parameters = sorted({s for e in eqs for s in e.free_symbols} - set(indep), key=str)
    rename = {}
    for s in parameters:
        rename[s] = Symbol(f"PAR{len(names)}")
        names[f"PAR{len(names)}"] = s.name
    lines = [
        f'batchload("{SYMMGRP}")$',
        "linel : 100000$",
        f"p : {p}$ q : {q}$ m : {len(eqs)}$",
        "warnings : false$",
        f"parameters : [{', '.join(str(rename[s]) for s in parameters)}]$",
        "sublisteqs : [all]$ subst_deriv_of_vi : true$",
        "highest_derivatives : all$ info_given : false$",
    ]
    chosen = set()
    for k, e in enumerate(eqs, 1):
        _, highest = order(e, dep, indep)
        if not highest:
            raise Unsupported("an equation without derivatives")
        lead = _leading_derivative(e, highest, dep)
        if lead in chosen:
            raise Unsupported("two equations with the same leading derivative")
        chosen.add(lead)
        lines.append(f"e{k} : {maxima_expr(e.xreplace(rename), indep, dep)}$")
        lines.append(f"v{k} : {maxima_expr(lead, indep, dep)}$")
    lines += [
        "symmetry(1, 0, 0)$",
        'print("LODE-BEGIN")$',
        "for e in lode do print(string(e))$",
        'print("LODE-END")$',
    ]
    return "\n".join(lines) + "\n", names


def maxima_expr(e, indep, dep):
    """e in Maxima syntax: x[i], u[l], u[l, [a_1, ..., a_p]]."""
    marks = {}
    for d in sorted(e.atoms(Derivative), key=str):
        if d.expr not in dep:
            # a derivative of an arbitrary function, e.g. k'(u)
            variables = ", ".join(
                f"{maxima_expr(v, indep, dep)}, {k}" for v, k in d.variable_count
            )
            mark = Symbol(f"DERIV{len(marks)}")
            marks[mark.name] = f"diff({maxima_expr(d.expr, indep, dep)}, {variables})"
            e = e.xreplace({d: mark})
            continue
        a = dep.index(d.expr) + 1
        counts = [0] * len(indep)
        for v, k in d.variable_count:
            counts[indep.index(v)] += k
        mark = Symbol(f"DERIV{len(marks)}")
        marks[mark.name] = f"u[{a},[{','.join(map(str, counts))}]]"
        e = e.xreplace({d: mark})
    for a, d in enumerate(dep, 1):
        mark = Symbol(f"DEP{a}")
        marks[mark.name] = f"u[{a}]"
        e = e.xreplace({d: mark})
    for i, v in enumerate(indep, 1):
        mark = Symbol(f"INDEP{i}")
        marks[mark.name] = f"x[{i}]"
        e = e.xreplace({v: mark})
    text = str(e).replace("**", "^")
    text = re.sub(r"\bpi\b", "%pi", text)
    text = re.sub(r"\bE\b", "%e", text)
    text = re.sub(r"\bI\b", "%i", text)
    text = re.sub(r"\bAbs\(", "abs(", text)
    for mark, value in sorted(marks.items(), key=lambda kv: -len(kv[0])):
        text = text.replace(mark, value)
    return text


def run_maxima(text, timeout):
    with tempfile.NamedTemporaryFile("w", suffix=".mac", delete=False) as f:
        f.write(text)
    t0 = time.time()
    out = subprocess.run(
        ["maxima", "--very-quiet", f"--batch={f.name}"], capture_output=True, text=True,
        timeout=timeout, check=False,
    ).stdout
    seconds = time.time() - t0
    Path(f.name).unlink()
    m = re.search(r"\nLODE-BEGIN \n.*?\n(.*?)\nprint\(\"LODE-END\"\)", out, re.S)
    if m is None:
        raise RuntimeError(out[-600:])
    return [line.strip() for line in m.group(1).splitlines() if line.strip()], seconds


def from_maxima(lines, p, q, names):
    xs = [Symbol(f"X{i}") for i in range(1, p + 1)]
    us = [Symbol(f"U{l}") for l in range(1, q + 1)]
    args = (*xs, *us)
    local = {f"X{i + 1}": x for i, x in enumerate(xs)} | {f"U{l + 1}": u for l, u in enumerate(us)}
    etas = [Function(f"eta{i}")(*args) for i in range(1, p + 1)]
    phis = [Function(f"phi{l}")(*args) for l in range(1, q + 1)]
    local |= {f"ETA{i + 1}": f for i, f in enumerate(etas)}
    local |= {f"PHI{l + 1}": f for l, f in enumerate(phis)}
    local |= {k: (Function(v) if k.startswith("FUN") else Symbol(v)) for k, v in names.items()}
    local |= {"D": lambda f, *a: Derivative(f, *zip(a[::2], a[1::2], strict=True)),
              "E": E, "pi": pi, "I": I}
    if any(re.search(r"u\[\d+,\[", line) for line in lines):
        # symmgrp splits only what is polynomial in the derivatives (sqrt(u_x),
        # exp(u_x), atan(u_x), ...): such equations are not determining
        # equations yet
        raise Unsupported("symmgrp left derivatives of u in its equations")
    equations = []
    for line in lines:
        s = line.replace("'diff(", "D(").replace("^", "**")
        s = re.sub(r"eta\[(\d+)\]", r"ETA\1", s)
        s = re.sub(r"phi\[(\d+)\]", r"PHI\1", s)
        s = re.sub(r"x\[(\d+)\]", r"X\1", s)
        s = re.sub(r"u\[(\d+)\]", r"U\1", s)
        s = s.replace("%pi", "pi").replace("%e", "E").replace("%i", "I")
        equations.append(sympify(parse_expr(s, local_dict=local)))
    return equations, etas + phis, list(args)


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout


def run_entry(job):
    i, timeout = job
    entry = CATALOG[i]
    row = {"index": i, "name": entry.name, "expected": entry.dimension}
    try:
        text, names = to_symmgrp(entry)
    except Unsupported as ex:
        return row | {"status": f"not converted: {ex}"}
    try:
        lines, seconds = run_maxima(text, timeout)
    except subprocess.TimeoutExpired:
        return row | {"status": "symmgrp timeout"}
    except RuntimeError as ex:
        return row | {"status": "symmgrp failed", "output": str(ex)[-300:]}
    row["symmgrp_time"] = round(seconds, 2)
    row["equations"] = len(lines)
    row["lines"] = lines
    row["names"] = names
    return row


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--only", default="")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--out", default=str(HERE / "symmgrp.jsonl"))
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, _alarm)
    idx = [i for i, e in enumerate(CATALOG) if args.only in e.name]
    t0 = time.time()
    with ThreadPoolExecutor(8) as pool:
        rows = list(pool.map(run_entry, [(i, args.timeout) for i in idx]))
    print(f"symmgrp: {sum('symmgrp_time' in r for r in rows)} of {len(rows)} "
          f"in {time.time() - t0:.0f} s", flush=True)
    counts = {}
    with open(args.out, "w") as out:
        for row in rows:
            if "lines" in row:
                entry = CATALOG[row["index"]]
                p, q = len(entry.independent), len(entry.dependent)
                try:
                    eqs, funcs, variables = from_maxima(row.pop("lines"), p, q, row["names"])
                    signal.alarm(args.timeout)
                    t = time.time()
                    rank = JanetBasis(eqs, funcs, variables).rank()
                    row["janet_time"] = round(time.time() - t, 2)
                    row["dimension"] = INFINITE if rank == oo else int(rank)
                    expected = row["expected"]
                    row["status"] = (
                        "no dimension in the catalogue" if expected is None
                        else "same dimension" if row["dimension"] == expected
                        else "different dimension"
                    )
                except Unsupported as ex:
                    row["status"] = str(ex)
                except Timeout:
                    row["status"] = "Janet basis timeout"
                except Exception as ex:  # noqa: BLE001
                    row["status"] = f"read back failed: {type(ex).__name__}: {str(ex)[:80]}"
                finally:
                    signal.alarm(0)
            row.pop("lines", None)
            counts[row["status"]] = counts.get(row["status"], 0) + 1
            out.write(json.dumps(row, default=str) + "\n")
            if row["status"] not in ("same dimension",):
                print(row["name"][:60], "|", row["status"], "|", row.get("dimension"),
                      row.get("expected"), flush=True)
    print(json.dumps(counts, indent=1))


if __name__ == "__main__":
    main()
