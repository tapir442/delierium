"""The catalogue's dimensions against Rosenfeld-Groebner in François Boulier's
DifferentialAlgebra (BLAD, https://codeberg.org/francois.boulier/DifferentialAlgebra).

Internal benchmark. delierium's determining equations (those of
determining_janet_basis) go to RosenfeldGroebner with an orderly ranking on
the infinitesimals; the parameters of the equation are constants ranked
below. The dimension of a regular differential chain is the number of
derivatives of the infinitesimals that are not derivatives of a leader. BLAD
splits on the parameters itself: the generic chains are those without an
equation in the parameters alone, the others are special cases.

    PYTHONPATH=. uv run --with DifferentialAlgebra python benchmarks/blad_crosscheck.py

One process per entry, memory-limited, at most --workers at a time; rows go
to <out>.partial as they come (a rerun skips those), the summary to
<out>.jsonl. Only rational coefficients: entries with exp, sin, symbolic
exponents or arbitrary functions are reported as unsupported.
"""

import argparse
import contextlib
import json
import multiprocessing
import resource
import signal
import time
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import product
from pathlib import Path

from sympy import Derivative, Function, Pow, Symbol, oo, pi
from sympy.core.function import AppliedUndef
from sympy.parsing.sympy_parser import parse_expr

from delierium.infinitesimals import _determining_system
from tests.symmetry_catalog import CATALOG, INFINITE

HERE = Path(__file__).resolve().parent
BY_NAME = {e.name: e for e in CATALOG}
MEMORY = 6 * 2**30  # per entry


def unsupported(system, functions):
    """Why BLAD cannot take system (coefficients not rational), or None."""
    for e in system:
        for a in e.atoms(Function):
            if not (isinstance(a, AppliedUndef) and a.func in functions):
                return f"function {a.func}"
        for p in e.atoms(Pow):
            if not p.exp.is_Integer:
                return f"power {p}"
    return None


def leaders(chain, variables, names):
    """(name, multi-index) of the leaders of chain that are infinitesimals."""
    result = []
    for d in chain.leading_derivative():
        if isinstance(d, Derivative):
            counts, f = dict(d.variable_count), d.expr
        elif isinstance(d, AppliedUndef):
            counts, f = {}, d
        else:
            continue  # a parameter
        if f.func.__name__ in names:
            result.append((f.func.__name__, tuple(counts.get(v, 0) for v in variables)))
    return result


def dimension(lead, names, n):
    """Number of parametric derivatives (INFINITE if not finite)."""
    total = 0
    for name in names:
        ms = [m for f, m in lead if f == name]
        bounds = []
        for i in range(n):  # finite iff a pure derivative in every direction
            pure = [m[i] for m in ms if all(m[j] == 0 for j in range(n) if j != i)]
            if not pure:
                return INFINITE
            bounds.append(min(pure))
        for a in product(*(range(b) for b in bounds)):
            if not any(all(a[j] >= m[j] for j in range(n)) for m in ms):
                total += 1
    return total


def compare_one(entry, timeout):
    import DifferentialAlgebra as D  # pylint: disable=import-outside-toplevel

    row = {"name": entry.name, "expected": entry.dimension}
    indep, dep = entry.variables()
    t0 = time.time()
    system, functions, variables = _determining_system(entry.parsed_equations(), dep, indep)
    row["deteq_time"] = round(time.time() - t0, 2)
    # BLAD wants the arguments in the order of the derivations
    canon = {f: f.func(*variables) for f in functions}
    system = [e for e in (s.xreplace(canon).doit() for s in system) if e != 0]
    system = [e.subs(pi, Symbol("pi_")) for e in system]  # a parameter for BLAD
    functions = list(canon.values())
    names = [f.func.__name__ for f in functions]
    why = unsupported(system, {f.func for f in functions})
    if why:
        return row | {"status": "unsupported", "check": why}
    params = sorted({s for e in system for s in e.free_symbols} - set(variables), key=str)
    ring = D.DifferentialRing(
        derivations=variables, blocks=[[f.func for f in functions], *params], parameters=params
    )
    t0 = time.time()
    chains = ring.RosenfeldGroebner(system, timeout=timeout)
    row["blad_time"] = round(time.time() - t0, 2)
    generic, special = [], []
    for chain in chains:
        dim = dimension(leaders(chain, variables, names), names, len(variables))
        conditions = [str(e) for e in chain.equations() if not e.atoms(AppliedUndef)]
        if conditions:
            special.append([dim, conditions])
        else:
            generic.append(dim)
    row |= {"status": "ok", "chains": len(chains), "generic": generic, "special": special}
    if not chains:
        row["check"] = "no solution"
    elif entry.dimension is None:
        row["check"] = "no expected dimension"
    else:
        same = generic and all(d == entry.dimension for d in generic)
        row["check"] = "agree" if same else "DIFFER"
    return row


def special_one(entry, timeout, case):
    """BLAD's special case case = [dimension, conditions] of entry against
    delierium: the Janet basis of the determining system with the conditions
    substituted (what BLAD computed: must agree), and the dimension of the
    equation with the conditions substituted (differs if it degenerates)."""
    from sympy import solve  # pylint: disable=import-outside-toplevel

    from delierium.infinitesimals import determining_janet_basis  # pylint: disable=C0415
    from delierium.janet_basis import JanetBasis  # pylint: disable=import-outside-toplevel

    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    blad, conditions = case
    row = {"name": f"{entry.name} | {', '.join(conditions)}", "entry": entry.name,
           "conditions": conditions, "blad": blad}
    if any("pi_" in c for c in conditions):
        return row | {"status": "skipped", "check": "pi = 0"}
    indep, dep = entry.variables()
    equations = entry.parsed_equations()
    params = {str(s): s for e in equations for s in e.free_symbols if s not in indep}
    conds = [parse_expr(c, local_dict=params) for c in conditions]
    solutions = solve(conds, list({s for c in conds for s in c.free_symbols}), dict=True)
    if not solutions:
        return row | {"status": "unsolved"}
    system, functions, variables = _determining_system(equations, dep, indep)
    cases = []
    for sol in solutions:
        sub = [e for e in (s.subs(sol) for s in system) if e != 0]
        a = JanetBasis(sub, functions, variables).rank() if sub else oo
        try:
            specialized = [e.subs(sol).doit() for e in equations]
            b = _dim(determining_janet_basis(specialized, dep, indep).rank())
        except ValueError as ex:  # the equation vanishes or loses its derivatives
            b = str(ex)
        cases.append({"solution": str(sol), "system": _dim(a), "equation": b})
    same = all(c["system"] == blad for c in cases)
    return row | {"status": "ok", "cases": cases, "check": "agree" if same else "DIFFER",
                  "degenerate": any(c["equation"] != c["system"] for c in cases)}


def _dim(rank):
    return INFINITE if rank == oo else int(rank)


def _alarm(*_):
    raise TimeoutError


def _child(func, args, conn):
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))
    try:
        conn.send(func(*args))
    except BaseException as ex:  # pylint: disable=broad-exception-caught
        conn.send({"crashed": f"{type(ex).__name__}: {str(ex)[:80]}"})


def isolated(func, entry, timeout, *rest):
    """func(entry, timeout, *rest) in a fresh forked process."""
    ctx = multiprocessing.get_context("fork")
    reader, writer = ctx.Pipe(duplex=False)
    proc = ctx.Process(target=_child, args=(func, (entry, timeout, *rest), writer))
    proc.start()
    writer.close()
    result, t0 = None, time.time()
    if reader.poll(timeout + 60):
        with contextlib.suppress(EOFError):
            result = reader.recv()
    if proc.is_alive():
        proc.kill()
    proc.join()
    seconds = round(time.time() - t0, 2)
    if result is None:
        status = "timeout" if seconds >= timeout + 60 else f"crashed: exit code {proc.exitcode}"
        result = {"crashed": status}
    if "crashed" in result:
        name = entry.name if not rest else f"{entry.name} | {', '.join(rest[0][1])}"
        result = {"name": name, "expected": entry.dimension, "status": result["crashed"]}
    return result | {"time": seconds}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--workers", type=int, default=3)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--out", default=str(HERE / f"blad-{time.strftime('%Y-%m-%d')}"))
    parser.add_argument("--special", help="check the special cases of this result file")
    parser.add_argument("names", nargs="*")
    args = parser.parse_args()
    entries = [BY_NAME[n] for n in args.names] if args.names else list(CATALOG)
    if args.special:
        special(args, entries)
        return
    partial = Path(args.out + ".partial")
    done = {}
    if partial.exists():
        done = {r["name"]: r for r in map(json.loads, partial.read_text().splitlines())}
    todo = [e for e in entries if e.name not in done]
    print(f"{len(done)} done before, {len(todo)} to do", flush=True)
    with ThreadPoolExecutor(args.workers) as pool, partial.open("a") as out:
        futures = [pool.submit(isolated, compare_one, e, args.timeout) for e in todo]
        for f in as_completed(futures):
            row = f.result()
            done[row["name"]] = row
            out.write(json.dumps(row, default=str) + "\n")
            out.flush()
    rows = sorted(done.values(), key=lambda r: r["name"])
    Path(args.out + ".jsonl").write_text("".join(json.dumps(r, default=str) + "\n" for r in rows))
    print(Counter(r["check"] if r["status"] == "ok" else r["status"] for r in rows))
    for r in rows:
        if r.get("check") == "DIFFER":
            print("DIFFER", r["name"], r["expected"], r["generic"], r["special"])


def special(args, entries):
    names = {e.name for e in entries}
    rows = [r for r in map(json.loads, Path(args.special).read_text().splitlines())
            if r["name"] in names and r.get("special")]
    jobs = [(BY_NAME[r["name"]], case) for r in rows for case in r["special"]]
    out = args.out + "-special"
    partial = Path(out + ".partial")
    done = {}
    if partial.exists():
        done = {r["name"]: r for r in map(json.loads, partial.read_text().splitlines())}
    todo = [(e, c) for e, c in jobs if f"{e.name} | {', '.join(c[1])}" not in done]
    print(f"{len(done)} done before, {len(todo)} to do", flush=True)
    with ThreadPoolExecutor(args.workers) as pool, partial.open("a") as f:
        futures = [pool.submit(isolated, special_one, e, args.timeout, c) for e, c in todo]
        for fut in as_completed(futures):
            row = fut.result()
            done[row["name"]] = row
            f.write(json.dumps(row, default=str) + "\n")
            f.flush()
    rows = sorted(done.values(), key=lambda r: r["name"])
    Path(out + ".jsonl").write_text("".join(json.dumps(r, default=str) + "\n" for r in rows))
    print(Counter(r.get("check", r["status"]) for r in rows))
    print("degenerate:", sum(bool(r.get("degenerate")) for r in rows))
    for r in rows:
        if r.get("check") == "DIFFER":
            print("DIFFER", r["name"], r["blad"], r["cases"])


if __name__ == "__main__":
    main()
