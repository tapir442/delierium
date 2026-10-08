"""Benchmark: delierium against SymPy's and sympy-extras' Lie symmetry code.

SymPy's only Lie symmetry facility for differential equations is
``sympy.solvers.ode.infinitesimals`` (with ``checkinfsol``): heuristic
searches (abaco1_simple, bivariate, chi, linear, ...) for *some* particular
infinitesimals of a *first order* ODE. It raises NotImplementedError for any
other order and does not treat systems or PDEs.

delierium computes the determining equations of ODEs, ODE systems and PDEs of
any order, and their Janet basis, which gives the dimension of the symmetry
algebra. It does not solve for the infinitesimals.

sympy-extras (PyPI; 0.x, its API may change with any release, hence the
pinned version below) computes point symmetries
of ODEs, systems and PDEs of any order with a polynomial ansatz: explicit
generators, but only those whose coefficients are polynomials of total degree
at most 2 here, so their number is a lower bound of the dimension.

So the tools overlap only partly, and the benchmark measures:

A. First order ODEs (Kamke chapters 1 and 2, from the SymPy kamke test
   suite), each tool in its own fresh process:
   - sympy_default: infinitesimals(hint="default"), what dsolve's lie_group uses
   - sympy_all:     infinitesimals(hint="all"), every heuristic
   - deli_det:      delierium's determining equations
   - deli_janet:    delierium's Janet basis and rank (oo for first order)
   and, for every generator SymPy found, a cross check:
   - cross_sympy:   SymPy's own checkinfsol
   - cross_deli:    substituted into delierium's determining equations
   - extras:        sympy-extras' generators (degree 2), and for each of them
   - cross_extras:  substituted into delierium's determining equations

B. The delierium catalogue (tests/symmetry_catalog.py, equations with known
   symmetries from the literature, any order, systems, PDEs):
   - sympy_all:     what SymPy says (mostly: not implemented)
   - deli_janet:    delierium's dimension of the symmetry algebra, compared
                    with the literature
   - extras:        how many generators sympy-extras finds, compared with the
                    dimension
   - deli_gens / sympy_gens / extras_gens: verify the published generators
                    (SymPy only for first order ODEs, via checkinfsol;
                    sympy-extras via check_symmetry)

Usage:

    uv run --with sympy-extras==0.0.2 python benchmarks/sympy_symmetries.py run --out results.jsonl
    uv run --with sympy-extras==0.0.2 python benchmarks/sympy_symmetries.py report results.jsonl [more.jsonl]

--tools runs only the given tools (e.g. --tools extras,extras_gens,cross_extras
to add sympy-extras to an earlier run); the report merges several result files,
a later file's result replacing an earlier one's. --cross-from takes the
generators to cross check from earlier runs as well, so that delierium's
tools can be rerun without rerunning SymPy:

    uv run --with sympy-extras==0.0.2 python benchmarks/sympy_symmetries.py run \
        --suites kamke --tools deli_det,deli_janet,cross_deli,cross_extras \
        --cross-from old.jsonl --out new.jsonl

--budget limits the wall-clock time of a run: no task starts that could not
finish in it. The equations run in random order, all tools of an equation
together, so a run cut short by the budget covers a random sample of the
equations, each with every tool; the report states the coverage.

Every task runs in a forked process with a cleared SymPy cache, a soft
timeout (SIGALRM) and a memory limit, so one tool's cache never helps the
other and a runaway computation does not stall the run.
"""

import argparse
import dataclasses
import json
import math
import multiprocessing as mp
import random
import resource
import signal
import statistics
import sys
import time
from collections import Counter, defaultdict
from pathlib import Path

from sympy import Function, Symbol, oo, srepr, sympify
from sympy.core.cache import clear_cache
from sympy.solvers.deutils import ode_order
from sympy.solvers.ode import checkinfsol, infinitesimals
from sympy.solvers.ode.lie_group import lie_heuristics

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
from tests.symmetry_catalog import CATALOG, INFINITE  # noqa: E402

DEFAULT_KAMKE = ROOT.parent / "kamke-test-suite"
MEMORY_LIMIT = 4 * 2**30
# as in tests/test_symmetry_catalog.py: the symbolic Janet basis does not
# finish in reasonable time, so random values are substituted for parameters
RANDOM_PARAMETERS = {"Kamke 6.171", "Kamke 6.219"}


def delierium():
    """delierium's modules, imported only in the processes that run delierium,
    so that SymPy's tasks run on pure SymPy (the parent never imports it)."""
    import delierium.infinitesimals as infinitesimals_module
    import delierium.janet_basis as janet_basis_module

    return infinitesimals_module, janet_basis_module


def sympy_extras():
    """sympy-extras' Lie module, imported only in the processes that run it."""
    import sympy_extras.solvers.lie as lie

    return lie


def extras_symmetries(eqs, dep):
    """sympy-extras' generators (xi..., eta...) as strings, in plain symbols."""
    lie = sympy_extras()
    found = lie.symmetries(eqs if len(eqs) > 1 else eqs[0], dep if len(dep) > 1 else dep[0], 2)
    gens = [[srepr(c) for c in (*X.xi, *X.eta)] for X in found]
    return {"n": len(found), "generators": gens}


def extras_verify(eqs, dep, indep, generators):
    lie = sympy_extras()
    jets = lie.JetSpace(list(dep))
    k = len(indep)
    return [
        bool(lie.check_symmetry(eqs, list(dep), lie.Symmetry(jets, list(g[:k]), list(g[k:]))))
        for g in generators
    ]


class Timeout(BaseException):
    """BaseException, so that `except Exception` inside SymPy cannot eat it."""


def _alarm(signum, frame):
    raise Timeout


# ---------------------------------------------------------------- equations


def kamke_first_order(path):
    sys.path.insert(0, str(path))
    from test_kamke import Kamke

    x = Symbol("x")
    y = Function("y")(x)
    out = {}
    for chapter in (1, 2):
        for name, eq in getattr(Kamke, f"chapter_{chapter}").items():
            if hasattr(eq, "lhs"):
                eq = eq.lhs - eq.rhs
            out[name.removeprefix("kamke_")] = (eq, y, x)
    return out


def catalog_entry(name):
    entry = next(e for e in CATALOG if e.name == name)
    if name in RANDOM_PARAMETERS:
        indep, _ = entry.variables()
        eqs = entry.parsed_equations()
        parameters = sorted(set().union(*(e.free_symbols for e in eqs)) - set(indep), key=str)
        rng = random.Random(entry.name)
        values = {p: rng.randint(2, 100) for p in parameters}
        # the same values in the published generators, which contain the parameters too
        generators = tuple(tuple(str(c.subs(values)) for c in g) for g in entry.parsed_generators())
        entry = dataclasses.replace(
            entry, equations=tuple(str(e.subs(values)) for e in eqs), generators=generators
        )
    return entry


def order_of(entry):
    from sympy import Derivative

    return max(
        (
            sum(c for _, c in d.variable_count)
            for e in entry.parsed_equations()
            for d in e.atoms(Derivative)
        ),
        default=0,
    )


# ---------------------------------------------------------------- the tools


def generators_from_sympy(result, func):
    """SymPy's [{xi(x, f): .., eta(x, f): ..}] as (xi, eta) in plain symbols."""
    x = func.args[0]
    y = Symbol(func.func.__name__)
    xi, eta = Function("xi")(x, func), Function("eta")(x, func)
    return [(g[xi].xreplace({func: y}), g[eta].xreplace({func: y})) for g in result]


def sympy_best(eq, func):
    """Every heuristic on its own, the results merged: SymPy at its best.
    (hint="all" gives up on the first heuristic that raises.)"""
    found, worked, failed = [], [], {}
    for heuristic in lie_heuristics:
        try:
            result = infinitesimals(eq, func, hint=heuristic)
        except (NotImplementedError, ValueError):
            continue
        except Exception as e:
            failed[heuristic] = type(e).__name__
            continue
        worked.append(heuristic)
        found.extend(g for g in generators_from_sympy(result, func) if g not in found)
    if not found:
        raise NotImplementedError(f"no heuristic found infinitesimals; crashed: {failed}")
    return {
        "n": len(found),
        "generators": [[srepr(c) for c in g] for g in found],
        "heuristics": worked,
        "crashed": failed,
    }


def deli_verify(eqs, dep, indep, generators):
    """delierium's verify_symmetries: generators are tuples in plain symbols,
    independent variables first; True where every residue vanishes."""
    d, _ = delierium()
    return [bool(r) for r in d.verify_symmetries(eqs, dep, indep, generators)]


def sympy_verify(eq, func, generators):
    x = func.args[0]
    y = Symbol(func.func.__name__)
    xi, eta = Function("xi")(x, func), Function("eta")(x, func)
    sols = [{xi: g[0].subs(y, func), eta: g[1].subs(y, func)} for g in generators]
    return [bool(ok) for ok, _ in checkinfsol(eq, sols, func=func)]


def janet_rank(system, functions, variables):
    _, jb = delierium()
    rank = jb.JanetBasis(system, functions, variables).rank()
    return "oo" if rank == oo else int(rank)


def run_kamke(tool, eq, y, x, payload):
    if tool == "sympy_default":
        return {"n": len(infinitesimals(eq, y, hint="default"))}
    if tool == "sympy_all":
        return {"n": len(infinitesimals(eq, y, hint="all"))}
    if tool == "sympy_best":
        return sympy_best(eq, y)
    if tool == "deli_det":
        return {"n": len(delierium()[0].overdetermined_system_ode(eq, [y], [x]))}
    if tool == "deli_janet":
        system, functions, variables, _ = delierium()[0]._linear_system_ode(eq, y, x)
        return {"rank": janet_rank(system, functions, variables)}
    if tool == "extras":
        return extras_symmetries([eq], [y])
    gens = [tuple(sympify(c) for c in g) for g in payload]
    if tool == "cross_sympy":
        return {"ok": sympy_verify(eq, y, gens)}
    if tool in ("cross_deli", "cross_extras"):
        return {"ok": deli_verify([eq], [y], [x], gens)}
    raise ValueError(tool)


def run_catalog(tool, entry):
    indep, dep = entry.variables()
    eqs = entry.parsed_equations()
    if tool == "sympy_all":
        return {"n": len(infinitesimals(eqs[0], dep[0], hint="all"))}
    if tool == "deli_janet":
        d, _ = delierium()
        if entry.kind == "ode":
            system, functions, variables, _ = d._linear_system_ode(eqs[0], dep[0], indep[0])
        elif entry.kind == "odes":
            system, functions, variables, _ = d._linear_system_odes(eqs, dep, indep)
        else:
            infs = d.create_infinitesimals(dep, indep)
            plain = {f: Symbol(f.func.__name__) for f in dep}
            det = d.overdetermined_system_pde(eqs[0], dep, indep, infinitesimals=infs)
            system = [e.xreplace(plain) for e in det]
            functions = [infs[v].xreplace(plain) for v in indep + dep]
            variables = indep + [plain[f] for f in dep]
        return {"rank": janet_rank(system, functions, variables)}
    if tool == "deli_gens":
        return {"ok": deli_verify(eqs, dep, indep, entry.parsed_generators())}
    if tool == "sympy_gens":
        return {"ok": sympy_verify(eqs[0], dep[0], entry.parsed_generators())}
    if tool == "extras":
        return {"n": extras_symmetries(eqs, dep)["n"]}
    if tool == "extras_gens":
        return {"ok": extras_verify(eqs, dep, indep, entry.parsed_generators())}
    raise ValueError(tool)


def worker(task, timeout, conn, kamke_path):
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
    clear_cache()
    signal.signal(signal.SIGALRM, _alarm)
    result = dict(task)
    result.pop("payload", None)
    try:
        if task["suite"] == "kamke":
            eq, y, x = kamke_first_order(kamke_path)[task["name"]]
        else:
            entry = catalog_entry(task["name"])
        if task["tool"].startswith(("sympy", "cross_sympy", "extras")) and (
            "delierium" in sys.modules
        ):
            raise RuntimeError("delierium is loaded in a SymPy or sympy-extras task")
        signal.setitimer(signal.ITIMER_REAL, timeout)
        start = time.perf_counter()
        try:
            if task["suite"] == "kamke":
                out = run_kamke(task["tool"], eq, y, x, task.get("payload"))
            else:
                out = run_catalog(task["tool"], entry)
        finally:
            elapsed = time.perf_counter() - start
            signal.setitimer(signal.ITIMER_REAL, 0)
        result.update(status="ok", time=elapsed, **out)
    except Timeout:
        result.update(status="timeout", time=timeout)
    except MemoryError:
        result.update(status="memory", time=time.perf_counter() - start)
    except NotImplementedError as e:
        result.update(status="notimpl", time=time.perf_counter() - start, error=str(e)[:500])
    except Exception as e:
        result.update(
            status="error", time=time.perf_counter() - start, error=f"{type(e).__name__}: {e}"[:300]
        )
    conn.send(result)
    conn.close()


# ---------------------------------------------------------------- scheduler


def run_tasks(tasks, jobs, timeout, out, kamke_path, deadline=None):
    """Run tasks in forked processes, at most `jobs` at a time; append every
    result to `out` (JSON lines) and return them. No task starts after
    deadline - timeout (time.monotonic()), so that all end by the deadline."""
    ctx = mp.get_context("fork")
    pending = list(tasks)
    running = {}
    results = []
    done = 0
    with open(out, "a") as fh:
        while pending or running:
            if deadline is not None and time.monotonic() > deadline - timeout - 30:
                if pending:
                    print(f"  budget used up: {len(pending)} tasks not run", file=sys.stderr)
                pending = []
            while pending and len(running) < jobs:
                task = pending.pop(0)
                parent, child = ctx.Pipe(duplex=False)
                p = ctx.Process(target=worker, args=(task, timeout, child, kamke_path))
                p.start()
                child.close()
                running[p] = (task, parent, time.monotonic())
            for p, (task, conn, started) in list(running.items()):
                result = None
                if conn.poll():
                    try:
                        result = conn.recv()
                    except EOFError:
                        result = None
                    if result is None:
                        result = {**task, "status": "crash", "time": time.monotonic() - started}
                elif not p.is_alive():
                    result = {**task, "status": "crash", "time": time.monotonic() - started}
                elif time.monotonic() - started > timeout + 30:  # stuck in C code
                    p.kill()
                    result = {**task, "status": "timeout", "time": timeout}
                if result is not None:
                    result.pop("payload", None)
                    p.join()
                    del running[p]
                    results.append(result)
                    fh.write(json.dumps(result) + "\n")
                    fh.flush()
                    done += 1
                    if done % 100 == 0:
                        print(f"  {done} done, {len(pending)} pending", file=sys.stderr)
            time.sleep(0.01)
    return results


def cmd_run(args):
    start = time.monotonic()
    budget = args.budget or None
    out = Path(args.out)
    out.write_text("")
    kamke = kamke_first_order(args.kamke)
    names = list(kamke)[: args.limit] if args.limit else list(kamke)
    if args.sample:
        names = random.Random(1).sample(names, args.sample)
    orders = {n: ode_order(kamke[n][0], kamke[n][1]) for n in names}
    selected = set(args.tools.split(",")) if args.tools else None

    def wanted(tools):
        return [t for t in tools if selected is None or t in selected]

    # one group of tasks per equation: all its tools run together
    kamke_tools = ("sympy_default", "sympy_all", "sympy_best", "deli_det", "deli_janet", "extras")
    suites = set(args.suites.split(","))
    groups = [
        [{"suite": "kamke", "name": n, "tool": t, "order": orders[n]} for t in wanted(kamke_tools)]
        for n in names
        if "kamke" in suites
    ]
    catalog = CATALOG[: args.limit] if args.limit else CATALOG
    if "catalog" not in suites:
        catalog = []
    if args.sample:
        catalog = random.Random(1).sample(catalog, args.sample)
    for e in catalog:
        tools = ["sympy_all", "deli_janet", "extras"]
        if e.generators:
            tools += ["deli_gens", "extras_gens"]
            if e.kind == "ode" and order_of(e) == 1:
                tools.append("sympy_gens")
        groups.append([{"suite": "catalog", "name": e.name, "tool": t} for t in wanted(tools)])
    groups = [g for g in groups if g]
    # equations in random order: a run cut short by the budget is a sample
    random.Random(0).shuffle(groups)
    tasks = [t for g in groups for t in g]
    planned = Counter(g[0]["suite"] for g in groups)
    with open(out, "a") as fh:
        meta = {"suite": "meta", "planned": dict(planned), "timeout": args.timeout}
        fh.write(json.dumps(meta | {"budget": budget, "jobs": args.jobs}) + "\n")
    print(f"phase 1: {len(tasks)} tasks", file=sys.stderr)
    # phase 2 (the cross checks) gets the last 15 % of the budget
    deadline1 = start + 0.85 * budget if budget else None
    results = run_tasks(tasks, args.jobs, args.timeout, out, args.kamke, deadline1)

    checks = {"sympy_best": ("cross_sympy", "cross_deli"), "extras": ("cross_extras",)}
    # generators of this run, and of earlier runs (--cross-from) for the tools not run now
    earlier = []
    for path in args.cross_from:
        with open(path) as fh:
            earlier += [json.loads(line) for line in fh]
    fresh = {(r["name"], r["tool"]) for r in results}
    sources = results + [r for r in earlier if (r.get("name"), r.get("tool")) not in fresh]
    cross = [
        {"suite": "kamke", "name": r["name"], "tool": t, "order": 1, "payload": r["generators"]}
        for r in sources
        if r["suite"] == "kamke" and r["tool"] in checks and r["status"] == "ok"
        if r.get("generators") and r["name"] in names
        for t in wanted(checks[r["tool"]])
    ]
    print(f"phase 2: {len(cross)} cross checks", file=sys.stderr)
    deadline2 = start + budget if budget else None
    run_tasks(cross, args.jobs, args.timeout, out, args.kamke, deadline2)
    print(f"done in {(time.monotonic() - start) / 60:.1f} min", file=sys.stderr)


# ---------------------------------------------------------------- report


def stats(times):
    times = sorted(times)
    if not times:
        return "- | - | - | - | -"
    n = len(times)
    median = statistics.median(times)
    q90 = times[min(n - 1, math.ceil(0.9 * n) - 1)]  # nearest rank
    return f"{n} | {sum(times):.1f} | {median:.3f} | {q90:.3f} | {times[-1]:.2f}"


def eval_crashed(r):
    """crashed heuristics of a sympy_best run that found nothing (in its error)."""
    if r.get("status") != "notimpl" or "crashed: " not in r.get("error", ""):
        return []
    return list(eval(r["error"].split("crashed: ", 1)[1]))


def coverage(path, rows):
    """One line: how many of the planned equations a run covered."""
    meta = next((r for r in rows if r["suite"] == "meta"), None)
    if meta is None:
        return None
    ran = Counter(suite for suite, _ in {(r["suite"], r["name"]) for r in rows if "name" in r})
    tools = sorted({r["tool"] for r in rows if r["suite"] != "meta"})
    budget = meta.get("budget")
    return (
        f"- {Path(path).name}: "
        + ", ".join(f"{s} {ran[s]} of {n} equations" for s, n in meta["planned"].items())
        + (f", time budget {budget / 60:.0f} min" if budget else "")
        + f", {meta['jobs']} processes; tools {', '.join(tools)}"
    )


def cmd_report(args):
    by = defaultdict(dict)
    timeout = args.timeout
    p = print
    p("Runs (the equations of a run cut short by its time budget are a random sample):\n")
    for path in args.results:
        with open(path) as fh:
            rows = [json.loads(line) for line in fh]
        line = coverage(path, rows)
        if line:
            p(line)
        for r in rows:
            if r["suite"] == "meta":
                timeout = r.get("timeout", timeout)
            else:
                by[(r["suite"], r["name"])][r["tool"]] = r
    p()

    kamke = {k[1]: v for k, v in by.items() if k[0] == "kamke"}
    orders = Counter(next(iter(v.values())).get("order") for v in kamke.values())
    kamke = {n: v for n, v in kamke.items() if next(iter(v.values())).get("order") == 1}
    p(f"## A. First order ODEs: Kamke chapters 1 and 2 ({len(kamke)} equations)\n")
    p(
        f"Orders of all equations in the two chapters: {dict(sorted(orders.items()))}; "
        "only the first order ones are counted below.\n"
    )
    p(f"Timeout {timeout} s per task, one fresh process per task.\n")
    p("| tool | ok | timeout | not implemented | error | memory/crash |")
    p("|---|---|---|---|---|---|")
    tools = ["sympy_default", "sympy_all", "sympy_best", "deli_det", "deli_janet", "extras"]
    tools = [t for t in tools if any(t in v for v in kamke.values())]
    for t in tools:
        c = Counter(v[t]["status"] for v in kamke.values() if t in v)
        p(
            f"| {t} | {c['ok']} | {c['timeout']} | {c['notimpl']} | {c['error']} | "
            f"{c['memory'] + c['crash']} |"
        )
    p("\nRun times of the successful runs (seconds):\n")
    p("| tool | n | total | median | 90% | max |")
    p("|---|---|---|---|---|---|")
    for t in tools:
        p(
            f"| {t} | "
            + stats([v[t]["time"] for v in kamke.values() if v.get(t, {}).get("status") == "ok"])
            + " |"
        )
    both = [v for v in kamke.values() if all(v.get(t, {}).get("status") == "ok" for t in tools)]
    p(f"\nOn the {len(both)} equations where all {len(tools)} succeed:\n")
    p("| tool | n | total | median | 90% | max |")
    p("|---|---|---|---|---|---|")
    for t in tools:
        p(f"| {t} | " + stats([v[t]["time"] for v in both]) + " |")
    ranks = Counter(
        str(v["deli_janet"].get("rank"))
        for v in kamke.values()
        if v.get("deli_janet", {}).get("status") == "ok"
    )
    p(f"\ndelierium ranks (expected oo for every first order ODE): {dict(ranks)}")
    best = [
        v["sympy_best"] for v in kamke.values() if v.get("sympy_best", {}).get("status") == "ok"
    ]
    ngens = Counter(r["n"] for r in best)
    p(f"\nSymPy generators found per equation (sympy_best): {dict(sorted(ngens.items()))}")
    worked = Counter(h for r in best for h in r["heuristics"])
    crashed = Counter(h for v in kamke.values() for h in v.get("sympy_best", {}).get("crashed", {}))
    crashed.update(h for v in kamke.values() for h in eval_crashed(v.get("sympy_best", {})))
    errors = Counter(
        (t, v[t].get("error", "")[:90])
        for v in kamke.values()
        for t in ("sympy_default", "sympy_all")
        if v.get(t, {}).get("status") == "error"
    )
    if errors:
        p("\nSymPy's exceptions (hint default/all stop at the first heuristic that raises):\n")
        for (t, msg), n in errors.most_common():
            p(f"- {n} × {t}: {msg}")
    p("\n| heuristic | found generators on | raised an exception on |")
    p("|---|---|---|")
    for h in lie_heuristics:
        p(f"| {h} | {worked[h]} | {crashed[h]} |")

    p("\n### Cross check of SymPy's generators\n")
    total = Counter()
    disagree = []
    for name, v in kamke.items():
        if "cross_sympy" not in v and "cross_deli" not in v:
            continue
        s, d = v.get("cross_sympy", {}), v.get("cross_deli", {})
        total["equations"] += 1
        if s.get("status") == "ok" and d.get("status") == "ok":
            for a, b in zip(s["ok"], d["ok"], strict=True):
                total["generators"] += 1
                total[f"sympy {'ok' if a else 'FAIL'} / delierium {'ok' if b else 'FAIL'}"] += 1
                if a != b:
                    disagree.append(name)
        else:
            total[
                f"check did not finish: sympy {s.get('status')}, delierium {d.get('status')}"
            ] += 1
    for k, n in total.items():
        p(f"- {k}: {n}")
    if disagree:
        p(f"- disagreeing equations: {', '.join(sorted(set(disagree)))}")
    p("\n| check | n | total | median | 90% | max |")
    p("|---|---|---|---|---|---|")
    for t in ("cross_sympy", "cross_deli"):
        p(
            f"| {t} | "
            + stats([v[t]["time"] for v in kamke.values() if v.get(t, {}).get("status") == "ok"])
            + " |"
        )

    report_extras_kamke(kamke, p)

    entries = {e.name: e for e in CATALOG}
    # entries of earlier runs that the catalogue no longer has (renamed, removed)
    catalog = {k[1]: v for k, v in by.items() if k[0] == "catalog" and k[1] in entries}
    p(f"\n## B. delierium catalogue ({len(catalog)} entries)\n")
    groups = defaultdict(list)
    for name in catalog:
        e = entries[name]
        kind = e.kind if e.kind != "ode" else f"ode, order {order_of(e)}"
        groups[kind].append(name)
    p(
        "| kind | entries | SymPy finds generators | delierium dimension right | wrong | no reference | "
        "delierium failed | delierium median s | max s |"
    )
    p("|---|---|---|---|---|---|---|---|---|")
    wrong = []
    for kind in sorted(groups):
        names = groups[kind]
        c = Counter()
        times = []
        for n in names:
            v, e = catalog[n], entries[n]
            if v.get("sympy_all", {}).get("status") == "ok":
                c["sympy"] += 1
            j = v.get("deli_janet")
            if j is None:  # not run (a merged run without delierium)
                continue
            if j["status"] != "ok":
                c["fail"] += 1
                continue
            times.append(j["time"])
            got = INFINITE if j["rank"] == "oo" else j["rank"]
            if e.dimension is None:
                c["noref"] += 1
            elif got == e.dimension:
                c["right"] += 1
            else:
                c["wrong"] += 1
                wrong.append((n, got, e.dimension))
        times.sort()
        med = f"{times[len(times) // 2]:.2f}" if times else "-"
        mx = f"{times[-1]:.1f}" if times else "-"
        p(
            f"| {kind} | {len(names)} | {c['sympy']} | {c['right']} | {c['wrong']} | {c['noref']} | "
            f"{c['fail']} | {med} | {mx} |"
        )
    for n, got, want in wrong:
        p(f"- wrong dimension: {n}: delierium {got}, literature {want}")
    fails = [
        (n, v["deli_janet"]["status"])
        for n, v in catalog.items()
        if v.get("deli_janet", {}).get("status", "ok") != "ok"
    ]
    for n, s in fails:
        p(f"- delierium {s}: {n}")
    report_extras_catalog(catalog, entries, groups, p)
    sympy_msgs = Counter(
        (v["sympy_all"]["status"], v["sympy_all"].get("error", "")[:90])
        for v in catalog.values()
        if v.get("sympy_all", {}).get("status", "ok") != "ok"
    )
    p("\nSymPy's answers where it found nothing:\n")
    for (s, msg), n in sympy_msgs.most_common():
        p(f"- {n} × {s}: {msg}")

    p("\n### Published generators\n")
    for t in ("deli_gens", "sympy_gens", "extras_gens"):
        c = Counter()
        times = []
        for v in catalog.values():
            r = v.get(t)
            if not r:
                continue
            if r["status"] == "ok":
                c["confirmed"] += sum(r["ok"])
                c["rejected"] += len(r["ok"]) - sum(r["ok"])
                times.append(r["time"])
            else:
                c[r["status"]] += 1
        p(
            f"- {t}: {dict(c)}; "
            + (f"median {sorted(times)[len(times) // 2]:.3f} s" if times else "")
        )


def report_extras_kamke(kamke, p):
    found = [v["extras"] for v in kamke.values() if v.get("extras", {}).get("status") == "ok"]
    if not found:
        return
    ngens = Counter(r["n"] for r in found)
    p(
        "\n### sympy-extras on the first order ODEs\n\n"
        f"Generators found per equation (polynomial ansatz of degree 2; a first order ODE has "
        f"infinitely many): {dict(sorted(ngens.items()))}\n"
    )
    total = Counter()
    for v in kamke.values():
        r = v.get("cross_extras")
        if not r:
            continue
        if r["status"] == "ok":
            total["generators confirmed by delierium"] += sum(r["ok"])
            total["generators rejected by delierium"] += len(r["ok"]) - sum(r["ok"])
        else:
            total[f"check did not finish ({r['status']})"] += 1
    for k, n in total.items():
        p(f"- {k}: {n}")
    rejected = sorted(
        n
        for n, v in kamke.items()
        if v.get("cross_extras", {}).get("ok") and not all(v["cross_extras"]["ok"])
    )
    if rejected:
        p(f"- equations with rejected generators: {', '.join(rejected)}")


def report_extras_catalog(catalog, entries, groups, p):
    if not any("extras" in v for v in catalog.values()):
        return
    p("\n### sympy-extras: generators found compared with the dimension\n")
    p(
        "| kind | entries | = dimension | fewer | more | infinite dimension | no reference "
        "| failed | median s |"
    )
    p("|---|---|---|---|---|---|---|---|---|")
    more = []
    for kind in sorted(groups):
        c = Counter()
        times = []
        for n in groups[kind]:
            r, e = catalog[n].get("extras"), entries[n]
            if r is None:
                continue
            if r["status"] != "ok":
                c["failed"] += 1
                continue
            times.append(r["time"])
            if e.dimension is None:
                c["noref"] += 1
            elif e.dimension == INFINITE:
                c["infinite"] += 1
            elif r["n"] == e.dimension:
                c["equal"] += 1
            elif r["n"] < e.dimension:
                c["fewer"] += 1
            else:
                c["more"] += 1
                more.append((n, r["n"], e.dimension))
        entries_run = sum(c.values())
        med = f"{statistics.median(times):.2f}" if times else "-"
        p(
            f"| {kind} | {entries_run} | {c['equal']} | {c['fewer']} | {c['more']} "
            f"| {c['infinite']} | {c['noref']} | {c['failed']} | {med} |"
        )
    for n, got, want in more:
        p(f"- more generators than the dimension: {n}: sympy-extras {got}, literature {want}")
    errs = Counter(
        (v["extras"]["status"], v["extras"].get("error", "")[:90])
        for v in catalog.values()
        if v.get("extras", {}).get("status") not in (None, "ok")
    )
    for (s, msg), n in errs.most_common():
        p(f"- {n} × sympy-extras {s}: {msg}")


def main():
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    sub = parser.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--out", default="sympy_symmetries.jsonl")
    r.add_argument("--jobs", type=int, default=3, help="parallel tasks (default 3: low load)")
    r.add_argument("--timeout", type=float, default=60)
    r.add_argument("--sample", type=int, default=0, help="N random equations of each suite")
    r.add_argument("--limit", type=int, default=0, help="only the first N equations of each suite")
    r.add_argument("--kamke", type=Path, default=DEFAULT_KAMKE)
    r.add_argument("--budget", type=float, default=0, help="wall-clock limit in seconds")
    r.add_argument("--tools", default="", help="comma separated: run only these tools")
    r.add_argument("--suites", default="kamke,catalog", help="comma separated: kamke, catalog")
    r.add_argument(
        "--cross-from",
        nargs="*",
        default=[],
        help="earlier result files: cross check their SymPy / sympy-extras generators too",
    )
    s = sub.add_parser("report")
    s.add_argument("results", nargs="+")
    s.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()
    cmd_run(args) if args.cmd == "run" else cmd_report(args)


if __name__ == "__main__":
    main()
