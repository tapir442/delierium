"""Thomas Wolf's LIEPDE (REDUCE, with CRACK) on the symmetry catalogue.

Internal benchmark. LIEPDE computes the determining equations of the point
symmetries and solves them with CRACK. Per catalogue entry (own redcsl
process): the general solution, one generator per free constant (infinite
if free functions remain), unsolved conditions. Compared: the dimension with
the catalogue; each generator against delierium's determining equations;
closure under commutators; the catalogue's generators in LIEPDE's span.

    uv run python benchmarks/reduce_symmetries.py [--only TEXT] [--timeout 120]
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

from sympy import Derivative, E, Function, I, Symbol, pi, solve
from sympy.core.function import AppliedUndef
from sympy.parsing.sympy_parser import parse_expr

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from delierium.helpers import finish_substitution  # noqa: E402
from delierium.infinitesimals import (  # noqa: E402
    _canonical_derivatives_of,
    _exact_numbers,
    _leading_derivative,
    order,
)
from delierium.lie_algebra import LieAlgebra, NotClosedError, VectorField  # noqa: E402
import mathlie_symmetries  # noqa: E402
from mathlie_symmetries import (  # noqa: E402
    checker,
    entry_of,
    independent,
    pool_map,
    projected_dimension,
)
from tests.symmetry_catalog import CATALOG  # noqa: E402

HERE = Path(__file__).resolve().parent


class Unsupported(Exception):
    pass


def to_reduce(entry):
    """REDUCE input for entry and the names to map back."""
    indep, dep = entry.variables()
    eqs = [
        finish_substitution(_exact_numbers(_canonical_derivatives_of(e, dep)))
        for e in entry.parsed_equations()
    ]
    if len(eqs) != len(dep):
        raise Unsupported("not as many equations as functions")
    others = sorted({f.func for e in eqs for f in e.atoms(AppliedUndef)} - {d.func for d in dep},
                    key=str)
    parameters = sorted({s for e in eqs for s in e.free_symbols} - set(indep), key=str)
    names = {f"x{i}": v.name for i, v in enumerate(indep, 1)}
    names |= {f"u{i}": d.func.__name__ for i, d in enumerate(dep, 1)}
    names |= {f"p{i}": s.name for i, s in enumerate(parameters)}
    names |= {f"f{i}": f.__name__ for i, f in enumerate(others)}
    to = {v: Symbol(f"x{i}") for i, v in enumerate(indep, 1)}
    to |= {s: Symbol(f"p{i}") for i, s in enumerate(parameters)}
    lines = ["off int;", "load_package crack;", "load_package liepde;", "off nat;",
             "linelength 100000;", "lisp(print_:=nil)$"]
    if others:
        lines.append(f"operator {', '.join(f'f{i}' for i in range(len(others)))};")
    for i in range(1, len(dep) + 1):
        lines.append(f"depend u{i}, {', '.join(f'x{j}' for j in range(1, len(indep) + 1))};")
    reduce_eqs = []
    chosen = set()
    for e in eqs:
        _, highest = order(e, dep, indep)
        if not highest:
            raise Unsupported("an equation without derivatives")
        lead = _leading_derivative(e, highest, dep)
        if lead in chosen:
            raise Unsupported("two equations with the same leading derivative")
        chosen.add(lead)
        sols = solve(e, lead)
        text = lambda x: reduce_expr(x, indep, dep, others, to)  # noqa: E731
        if len(sols) == 1:
            reduce_eqs.append(f"{text(lead)} = {text(sols[0])}")
        else:
            reduce_eqs.append(text(e))  # LIEPDE brings it into solved form
    variables = ", ".join(f"x{i}" for i in range(1, len(indep) + 1))
    functions = ", ".join(f"u{i}" for i in range(1, len(dep) + 1))
    lines.append(f"r := liepde({{{{{', '.join(reduce_eqs)}}}, {{{functions}}}, {{{variables}}}}},"
                 ' {"point"}, {}, {})$')
    checks = ", ".join(
        [f'" ", df(c, x{i})' for i in range(1, len(indep) + 1)]
        + [f'" ", df(c, u{i})' for i in range(1, len(dep) + 1)]
    )
    lines += [
        'for each cs in r do << write "CASE";',
        '  for each c in first cs do write "COND ", c;',
        '  for each s in second cs do write "SOL ", lhs s, " := ", rhs s;',
        f'  for each c in third cs do write "CONST ", c{", " + checks if checks else ""} >>;',
        "end;",
    ]
    return "\n".join(lines) + "\n", names


def reduce_expr(e, indep, dep, others, to):
    marks = {}
    for d in sorted(e.atoms(Derivative), key=str):
        if d.expr in dep:
            parts = [f"u{dep.index(d.expr) + 1}"]
        else:
            parts = [reduce_expr(d.expr, indep, dep, others, to)]
        for v, k in d.variable_count:
            if v in indep:
                name = f"x{indep.index(v) + 1}"
            elif v in dep:
                name = f"u{dep.index(v) + 1}"
            else:  # already renamed (ReLie's jet coordinates)
                name = str(v)
            parts.append(name if k == 1 else f"{name}, {k}")
        mark = Symbol(f"MARK{len(marks)}")
        marks[mark.name] = f"df({', '.join(parts)})"
        e = e.xreplace({d: mark})
    for a, d in enumerate(dep, 1):
        e = e.xreplace({d: Symbol(f"u{a}")})
    e = e.replace(lambda a: isinstance(a, AppliedUndef) and a.func in others,
                  lambda a: Function(f"f{others.index(a.func)}")(*a.args))
    e = e.xreplace(to)
    text = str(e)
    text = re.sub(r"\bE\b", "e", text)
    text = re.sub(r"\bAbs\(", "abs(", text)
    for mark, value in sorted(marks.items(), key=lambda kv: -len(kv[0])):
        text = text.replace(mark, value)
    return text


def _die_with_parent():
    """REDUCE gets SIGKILL when the Python process dies (Linux): a killed run
    must not leave REDUCE computing for hours."""
    import ctypes

    ctypes.CDLL("libc.so.6", use_errno=True).prctl(1, signal.SIGKILL)  # PR_SET_PDEATHSIG


def run_reduce(text, timeout):
    with tempfile.NamedTemporaryFile("w", suffix=".red", delete=False) as f:
        f.write(text)
    t0 = time.time()
    try:
        with open(f.name) as stdin:
            out = subprocess.run(["redcsl", "-w"], stdin=stdin, capture_output=True, text=True,
                                 timeout=timeout, check=False,
                                 preexec_fn=_die_with_parent).stdout  # noqa: PLW1509
    finally:
        Path(f.name).unlink()
    return out, time.time() - t0


def parse_output(out, entry, names):
    """[(conditions, solution {var: expr}, constants, functions)] per case."""
    indep, dep = entry.variables()
    back = {k: Symbol(v) for k, v in names.items() if k[0] in "xpu"}
    funcs = {k: Function(v) for k, v in names.items() if k[0] == "f"}

    def expr(s, free=()):
        """s as SymPy; free: [(name, args)] of LIEPDE's free functions."""
        s = s.strip().replace("df(", "D(")
        local = dict(back) | funcs | {"e": E, "pi": pi, "i": I,
                                      "D": lambda f, *a: Derivative(f, *a)}
        local |= {name: Function(name)(*args) for name, args in free}
        return parse_expr(s, local_dict=local)

    # REDUCE wraps very long lines despite linelength: one entry per line again
    joined, pending = [], ""
    for line in out.splitlines():
        if pending:
            pending += line.strip()
        elif line.startswith(("COND ", "SOL ", "CONST ")) and not line.rstrip().endswith("$"):
            pending = line.rstrip()
        else:
            joined.append(line)
            continue
        if pending.rstrip().endswith("$"):
            joined.append(pending)
            pending = ""
    out = "\n".join(joined + ([pending] if pending else []))
    # DIMSYM's c(k), x(j), u(i)
    out = re.sub(r"\bc\((\d+)\)", r"c_\1", out)
    out = re.sub(r"\b(xi|phi|eta)\((\d+)\)", r"\1_\2", out)
    out = re.sub(r"\b([xu])\((\d+)\)", r"\1\2", out)
    cases = []
    for block in out.split("CASE")[1:]:
        conditions, solution, constants, functions = [], {}, [], []
        for line in block.splitlines():
            line = line.strip().rstrip("$").strip()  # off nat ends each line with $
            if line.startswith("COND "):
                conditions.append(line[5:])
            elif line.startswith("SOL "):
                lhs, rhs = line[4:].split(":=", 1)
                solution[lhs.strip()] = rhs.strip()
            elif line.startswith("CONST "):
                parts = line[6:].split()
                if any(p != "0" for p in parts[1:]):
                    # a free function of the variables it depends on
                    names_ = [f"x{i}" for i in range(1, len(indep) + 1)]
                    names_ += [f"u{i}" for i in range(1, len(dep) + 1)]
                    args = [back[n] for n, p in zip(names_, parts[1:], strict=False) if p != "0"]
                    functions.append((parts[0], args))
                else:
                    constants.append(parts[0])
        cases.append((conditions, solution, constants, functions))
    # LIEPDE prints the true dependencies ("with c_8, c_6(u1)"); REDUCE's
    # global dependency list may still have the ones CRACK started with
    m = re.search(r"\bwith (c_\w+(?:\([^)]*\))?(?:, c_\w+(?:\([^)]*\))?)*)", out)
    if m and len(cases) == 1:
        declared = {}
        for name, args in re.findall(r"(c_\w+)(?:\(([^)]*)\))?", m.group(1)):
            declared[name] = [back[a.strip()] for a in args.split(",")] if args else []
        conditions, solution, constants, functions = cases[0]
        everything = constants + [n for n, _ in functions]
        constants = [n for n in everything if not declared.get(n)]
        functions = [(n, declared[n]) for n in everything if declared.get(n)]
        cases[0] = (conditions, solution, constants, functions)
    return cases, expr


def generators_of(case, entry, expr):
    """One generator per free constant (others and the functions 0)."""
    _, solution, constants, functions = case
    indep, dep = entry.variables()
    keys = [f"xi_x{i}" for i in range(1, len(indep) + 1)]
    keys += [f"eta_u{i}" for i in range(1, len(dep) + 1)]
    exprs = [solution.get(k, "0") for k in keys]
    for f, _ in functions:
        exprs = [re.sub(rf"\b{f}\b", "0", e) for e in exprs]
    gens = []
    for c in constants:
        g = []
        for e in exprs:
            for other in constants:
                e = re.sub(rf"\b{other}\b", "1" if other == c else "0", e)
            g.append(expr(e))
        gens.append(tuple(g))
    return gens


def solution_dimension(case, entry, expr):
    """The dimension of the generators' space when conditions remain.

    The constants and free functions solve the (linear, homogeneous)
    remaining conditions; delierium's Janet basis gives the dimension of
    the space of infinitesimals they span (projected_dimension)."""
    conditions, solution, constants, functions = case
    indep, dep = entry.variables()
    variables = [Symbol(v) for v in entry.independent + entry.dependent]
    unknowns = [(c, variables) for c in constants]
    unknowns += [(name, variables) for name, _ in functions]
    free = [Function(name)(*variables) for name, _ in unknowns]
    depends = dict(functions)
    system = [expr(c, unknowns) for c in conditions]
    for f, (name, _) in zip(free, unknowns, strict=True):
        args = depends.get(name, [])
        system += [f.diff(v) for v in variables if v not in args]
    keys = [f"xi_x{i}" for i in range(1, len(indep) + 1)]
    keys += [f"eta_u{i}" for i in range(1, len(dep) + 1)]
    # an infinitesimal without a solution (ReLie) is one of the unknowns itself
    names_ = {n for n, _ in unknowns}
    infinitesimals = [expr(solution.get(k, k if k in names_ else "0"), unknowns) for k in keys]
    return projected_dimension(system, free, infinitesimals, variables)


def convert_entry(i, convert, timeout=60):
    """(row, text, names) for catalogue entry i; in the main thread (SymPy is
    not thread-safe), with a time limit."""
    entry = CATALOG[i]
    row = {"index": i, "name": entry.name, "expected": entry.dimension}
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        text, names = convert(entry)
    except Timeout:
        return row | {"status": "not converted: timeout"}, None, None
    except Unsupported as ex:
        return row | {"status": f"not converted: {ex}"}, None, None
    except Exception as ex:  # noqa: BLE001
        return row | {"status": f"not converted: {type(ex).__name__}: {str(ex)[:60]}"}, None, None
    finally:
        signal.alarm(0)
    return row, text, names


def run_entry(job):
    (row, text, names), timeout = job
    if text is None:
        return row
    try:
        out, seconds = run_reduce(text, timeout)
    except subprocess.TimeoutExpired:
        return row | {"status": "timeout"}
    return row | {"time": round(seconds, 2), "output": out, "names": names}


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout


def compare(row):
    """Per entry, in a worker process (with its own time limit)."""
    entry = entry_of(row)
    cases, expr = parse_output(row["output"], entry, row["names"])
    if "Unable to find all substitutions" in row["output"]:
        return {"status": "LIEPDE needs a solved form"}
    if "one_of(" in row["output"]:
        return {"status": "several roots for the leading derivative (one_of), not solved"}
    if not cases:
        return {"status": "no result"}
    r = {"cases": len(cases)}
    conditions, _, constants, functions = cases[0]
    coords = [Symbol(v) for v in entry.independent + entry.dependent]
    gens = independent(generators_of(cases[0], entry, expr), coords)
    if conditions or functions:
        r["functions"] = len(functions)
        r["conditions"] = len(conditions)
        r["dimension"] = solution_dimension(cases[0], entry, expr)
    else:
        r["dimension"] = len(gens)
    expected = row["expected"]
    if expected is None:
        r["status"] = "no dimension in the catalogue"
    else:
        r["status"] = "same dimension" if r["dimension"] == expected else "different dimension"
    if conditions or functions:
        return r  # no explicit generators: they solve the conditions only together
    check = checker(entry)
    r["wrong_generators"] = [str(g) for g in gens if not check(g)]
    if gens:
        algebra = LieAlgebra(gens, coords)
        try:
            algebra.structure_constants
            r["closed"] = True
        except NotClosedError:
            r["closed"] = False
        if entry.generators:
            missing = []
            for g in entry.parsed_generators():
                try:
                    algebra._coordinates_of(VectorField(g, coords))
                except NotClosedError:
                    missing.append(str(g))
            r["catalogue_not_in_span"] = missing
    return r


def compare_worker(job):
    row, timeout = job
    base = {k: v for k, v in row.items() if k != "output"}
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        return base | compare(row)
    except Timeout:
        return base | {"status": "comparison timeout"}
    except MemoryError:
        return base | {"status": "comparison out of memory"}
    except Exception as ex:  # noqa: BLE001
        return base | {"status": f"read back failed: {type(ex).__name__}: {str(ex)[:80]}"}
    finally:
        signal.alarm(0)


def compare_failed(job, reason):
    row, _ = job
    return {k: v for k, v in row.items() if k != "output"} | {
        "status": f"comparison crashed: {reason}"}


def main(convert=to_reduce, name="reduce"):
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("run", help="LIEPDE on the catalogue; raw output to --raw")
    p.add_argument("--only", default="")
    p.add_argument("--timeout", type=int, default=120)
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--raw", default=str(HERE / f"{name}-raw.jsonl"))
    p = sub.add_parser("compare", help="evaluate the raw output")
    p.add_argument("raw")
    p.add_argument("--timeout", type=int, default=60)
    p.add_argument("--memory", type=int, default=6, help="GB per entry")
    p.add_argument("--retry", action="store_true",
                   help="recompute the entries that hit a limit (with more --timeout/--memory)")
    p.add_argument("--jobs", type=int, default=8)
    p.add_argument("--out", default=str(HERE / f"{name}.jsonl"))
    args = parser.parse_args()
    if args.command == "run":
        idx = [i for i, e in enumerate(CATALOG) if args.only in e.name]
        t0 = time.time()
        converted = [convert_entry(i, convert) for i in idx]
        print(f"converted {sum(c[1] is not None for c in converted)} of {len(idx)} "
              f"in {time.time() - t0:.0f} s", flush=True)
        with ThreadPoolExecutor(args.jobs) as pool:
            rows = list(pool.map(run_entry, [(c, args.timeout) for c in converted]))
        print(f"{name}: {sum('time' in r for r in rows)} of {len(rows)} "
              f"in {time.time() - t0:.0f} s", flush=True)
        with open(args.raw, "w") as out:
            for row in rows:
                out.write(json.dumps(row) + "\n")
        return
    rows = [json.loads(line) for line in open(args.raw)]
    todo = [r for r in rows if "output" in r]
    t0 = time.time()
    mathlie_symmetries.MEMORY = args.memory * 2**30  # read by the forked workers
    done = pool_map(compare_worker, [(r, args.timeout) for r in todo], args.jobs,
                    Path(args.out).with_suffix(".partial"), compare_failed, args.timeout,
                    args.retry)
    print(f"compared {len(done)} in {time.time() - t0:.0f} s", flush=True)
    counts = {}
    with open(args.out, "w") as out:
        for row in rows:
            row = dict(done.get(row["name"], row))
            row.pop("output", None)
            counts[row["status"]] = counts.get(row["status"], 0) + 1
            out.write(json.dumps(row, default=str) + "\n")
            bad = row.get("wrong_generators") or row.get("catalogue_not_in_span") \
                or row.get("closed") is False
            if row["status"] != "same dimension" or bad:
                print(row["name"][:60], "|", row["status"], "|", row.get("dimension"),
                      row.get("expected"), "| wrong:", row.get("wrong_generators"),
                      "| not in span:", row.get("catalogue_not_in_span"), flush=True)
    print(json.dumps(counts, indent=1))


if __name__ == "__main__":
    main()
