"""Run Baumann's MathLie (Mathematica) on the symmetry catalogue and compare.

Internal benchmark (#6), not part of the package: MathLie is licensed to one
machine, so neither it nor its output is committed.

    uv run python benchmarks/mathlie_symmetries.py run [--only SUBSTRING] [--timeout 60]
    uv run python benchmarks/mathlie_symmetries.py compare RESULTS.jsonl

run: writes the catalogue in Mathematica syntax, calls Infinitesimals[] for
each entry in one kernel (TimeConstrained), and stores per entry the
infinitesimals split into one generator per integration constant k_i, whether
free functions remain, and the unsolved determining equations.

compare: MathLie's dimension against the catalogue's; MathLie's generators
against delierium's determining equations; their closure under commutators
(LieAlgebra); the catalogue's generators in MathLie's span.
"""

import argparse
import json
import os
import re
import resource
import signal
import subprocess
import sys
import time
from pathlib import Path

from sympy import (
    Derivative,
    Ei,
    Function,
    Lambda,
    LambertW,
    Matrix,
    Symbol,
    airyai,
    airyaiprime,
    airybi,
    airybiprime,
    besseli,
    besselj,
    besselk,
    bessely,
    erf,
    erfc,
    erfi,
    gamma,
    oo,
)
from sympy.core.function import AppliedUndef
from sympy.parsing.mathematica import parse_mathematica
from sympy.printing.mathematica import mathematica_code

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from delierium.infinitesimals import create_infinitesimals  # noqa: E402
from delierium.janet_basis import JanetBasis  # noqa: E402
from delierium.matrix_order import Mgrevlex  # noqa: E402
from delierium.lie_algebra import LieAlgebra, NotClosedError, VectorField  # noqa: E402
from tests.symmetry_catalog import CATALOG, INFINITE  # noqa: E402
from catalog_helpers import determining_equations, vanishes  # noqa: E402

HERE = Path(__file__).resolve().parent
# entries by name: the results stay valid when the catalogue gets new entries
BY_NAME = {e.name: e for e in CATALOG}


def entry_of(row):
    """The catalogue entry of a result row (by its name, not its position)."""
    return BY_NAME[row["name"]]

MATHLIE = Path(os.environ.get("MATHLIE", "/home/tapir/research-disk/LieSymmetriesForDEs/mathlie"))
# MathLie loads its parts by context names (LieSymmetry`, ...) whose case
# differs from the file names: links with the right case
LINKS = {
    "MathLie": "mathlie",
    "LieSymmetry": "liesymmetry",
    "PDESOLVE": "pdesolve",
    "nonclass": "nonclass",
    "LieBaecklundSymmetry": "liebaecklundsymmetry",
    "DynamicalSystems": "dynamicalsystems",
    "PotentialSYmmetry": "potentialsymmetry",
    "LieIntegrate": "lieintegrate",
}


def safe(name):
    """A Mathematica symbol for a catalogue name: prefixed, so that it clashes
    neither with System` (E, I, N, D, C ...) nor with MathLie's symbols (u, k1,
    xi, phi, free)."""
    return "q" + re.sub(r"[^A-Za-z0-9]", "Z", name)


def to_mathematica(entry):
    indep, dep = entry.variables()
    names = {s.name for e in entry.parsed_equations() for s in e.free_symbols}
    names |= {f.func.__name__ for e in entry.parsed_equations() for f in e.atoms(Function)
              if hasattr(f.func, "__name__") and f.func.__class__.__name__ == "UndefinedFunction"}
    names |= set(entry.independent) | set(entry.dependent)
    rename = {n: safe(n) for n in names}
    eqs = []
    for e in entry.parsed_equations():
        e = e.xreplace({s: Symbol(rename[s.name]) for s in e.free_symbols})
        e = e.replace(
            lambda a: hasattr(a, "func") and a.func.__class__.__name__ == "UndefinedFunction",
            lambda a: Function(rename[a.func.__name__])(*a.args),
        )
        eqs.append(f"(({mathematica_code(e)}) //. Hold[h_] :> h) == 0")
    return {
        "index": CATALOG.index(entry),
        "name": entry.name,
        "eqs": eqs,
        "dep": [rename[d] for d in entry.dependent],
        "indep": [rename[v] for v in entry.independent],
    }


WL = r"""
$MathLiePath = "LINKDIR/"; PrependTo[$Path, "LINKDIR"];
Quiet[Get["MathLie`"]];
str[e_] := ToString[e, InputForm, CharacterEncoding -> "ASCII"];
load[] := If[! MemberQ[$Packages, "LieSymmetry`"],
  $MathLiePath = "LINKDIR/"; PrependTo[$Path, "LINKDIR"]; Quiet[Get["MathLie`"]]];
solve[en_] := Module[{name = en["index"], eqs, dep, indep, res, t0, rules, vec, ks, gens, r},
  load[];
  eqs = ToExpression[en["eqs"]];
  dep = Symbol /@ en["dep"]; indep = Symbol /@ en["indep"];
  t0 = AbsoluteTime[];
  (* Quiet only: Check would call every result with a (harmless) message
     an error; the shape of the result tells *)
  res = Quiet@MemoryConstrained[
      TimeConstrained[
        Block[{Print = Null &}, Infinitesimals[eqs, dep, indep, {}]],
        TIMEOUT, "timeout"],
      MEMORY 2^30, "out of memory"];
  ClearSystemCache[];
  r = <|"index" -> en["index"], "name" -> en["name"], "ms" -> Round[1000 (AbsoluteTime[] - t0)]|>;
  If[res === "error" && r["ms"] >= 1000 TIMEOUT - 1000, res = "timeout"];
  If[MatchQ[res, {__Rule}], res = {res, {}}];
  Which[
    MatchQ[res, {{__Rule}, _List}],
    rules = res[[1]];
    vec = Join[
      Table[(xi[i] /. rules) @@ Join[indep, dep], {i, Length[indep]}],
      Table[(phi[i] /. rules) @@ Join[indep, dep], {i, Length[dep]}]];
    ks = Union@Cases[vec, s_Symbol /; StringMatchQ[SymbolName[s], "k" ~~ DigitCharacter ..], {0, Infinity}];
    gens = Table[Simplify[D[vec, k] /. Thread[ks -> 0] /. free[_][___] -> 0], {k, ks}];
    r["status"] = "ok";
    r["free"] = ! FreeQ[vec, free];
    r["generators"] = Map[str, gens, {2}];
    r["infinitesimals"] = str /@ vec;
    r["remaining"] = str /@ res[[2]],
    StringQ[res], r["status"] = res,
    SymbolName[Head[res]] === "InfinitesimalsOfFirstOrderODE", r["status"] = "first order ODE: not supported",
    True, r["status"] = "unexpected"; r["result"] = StringTake[str[res], UpTo[500]]];
  WriteString[OpenAppend["OUTPUT." <> ToString[$KernelID]],
    ExportString[r, "RawJSON", "Compact" -> True], "\n"];
  Close["OUTPUT." <> ToString[$KernelID]];
  name];
entries = Import["INPUT", "RawJSON"];
If[JOBS == 0, Scan[solve, entries]; Exit[]];
LaunchKernels[JOBS];
DistributeDefinitions[solve, str, load];
ParallelEvaluate[Pause[2 $KernelID]; load[]];
ParallelMap[solve, entries, Method -> "FinestGrained"];
"""


def link_mathlie(directory):
    directory.mkdir(parents=True, exist_ok=True)
    for context, file in LINKS.items():
        link = directory / f"{context}.m"
        if link.is_symlink() and not link.exists():  # the package moved
            link.unlink()
        if not link.exists():
            link.symlink_to(MATHLIE / f"{file}.m")


def run_isolated(args, work, data, output):
    """One wolframscript per entry, at most 2 at a time (the licence allows 2
    kernels), each in a systemd scope with a hard memory limit: MathLie can
    take 10 GB and more, and MemoryConstrained does not stop it."""
    from concurrent.futures import ThreadPoolExecutor

    def one(entry):
        tag = f"{output.name}.{entry['index']}"
        (work / f"{tag}.json").write_text(json.dumps([entry]))
        script = (
            WL.replace("LINKDIR", str(work / "mathlie"))
            .replace("INPUT", str(work / f"{tag}.json"))
            .replace("OUTPUT", str(work / tag))
            .replace("TIMEOUT", str(args.timeout))
            .replace("JOBS", "0")
            .replace("MEMORY", str(args.memory))
        )
        (work / f"{tag}.wls").write_text(script)
        t0 = time.time()
        proc = subprocess.run(
            ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={args.memory}G",
             "-p", "MemorySwapMax=0", "timeout", "-s", "KILL", str(args.timeout + 60),
             "wolframscript", "-file", str(work / f"{tag}.wls")],
            check=False, capture_output=True,
        )
        results = list(work.glob(tag + ".*[0-9]"))
        if not results:  # killed: out of memory or over time
            status = "timeout" if time.time() - t0 >= args.timeout + 55 else "out of memory"
            row = {"index": entry["index"], "name": entry["name"], "ms": round(1000 * (time.time() - t0)),
                   "status": status, "returncode": proc.returncode}
            (work / f"{tag}.0").write_text(json.dumps(row) + "\n")
        print(entry["index"], round(time.time() - t0), flush=True)

    with ThreadPoolExecutor(2) as pool:
        list(pool.map(one, data))


def run(args):
    work = HERE / "mathlie-work"
    link_mathlie(work / "mathlie")
    entries = [e for e in CATALOG if not args.only or args.only in e.name]
    if args.retry:  # entries with this status in a previous output
        previous, status = args.retry.split(":")
        again = {json.loads(line)["name"] for line in Path(previous).read_text().splitlines()
                 if json.loads(line)["status"] == status}
        entries = [e for e in entries if e.name in again]
    data = []
    for e in entries:
        try:
            data.append(to_mathematica(e))
        except Exception as ex:  # noqa: BLE001
            print("cannot convert", e.name, ex)
    (work / "input.json").write_text(json.dumps(data))
    output = Path(args.output)
    script = (
        WL.replace("LINKDIR", str(work / "mathlie"))
        .replace("INPUT", str(work / "input.json"))
        .replace("OUTPUT", str(work / output.name))
        .replace("TIMEOUT", str(args.timeout))
        .replace("JOBS", str(args.jobs))
        .replace("MEMORY", str(args.memory))
    )
    (work / "run.wls").write_text(script)
    for old in work.glob(output.name + ".*"):
        old.unlink()
    t0 = time.time()
    if args.isolated:
        run_isolated(args, work, data, output)
    else:
        subprocess.run(["wolframscript", "-file", str(work / "run.wls")], check=False)
    with output.open("w") as out:
        for part in sorted(work.glob(output.name + ".*")):
            if part.suffix in (".json", ".wls"):
                continue
            out.write(part.read_text())
    print(f"{len(data)} entries in {time.time() - t0:.0f} s -> {output}")


UNKNOWN = re.compile(r"^(k\d+|free\d+|xi\d+|phi\d+)$")


def parse(s, rename, coords=None):
    """MathLie's InputForm as SymPy. free[i], xi[i], phi[i] become functions
    free1, xi1, phi1 and Derivative[n..][f][args] their derivatives; with
    coords, these unknowns (and the constants k_i) are functions of all
    coordinates, for the Janet basis."""
    s = re.sub(r"\b(free|xi|phi)\[(\d+)\]", r"\1\2", s)
    s = re.sub(r"Derivative\[([\d, ]+)\]\[(\w+)\]",
               lambda m: f"DERIV{m.group(2)}o{'o'.join(m.group(1).replace(' ', '').split(','))}",
               s)
    e = parse_mathematica(s)
    back = {Symbol(v): Symbol(k) for k, v in rename.items()}
    e = e.xreplace(back)
    # arbitrary functions of the equation (qpsi[qx] for psi(x)) by their names
    functions = {v: k for k, v in rename.items()}
    special = {"Erf": erf, "Erfc": erfc, "Erfi": erfi, "AiryAi": airyai, "AiryBi": airybi,
               "AiryAiPrime": airyaiprime, "AiryBiPrime": airybiprime, "BesselJ": besselj,
               "BesselY": bessely, "BesselI": besseli, "BesselK": besselk, "Gamma": gamma,
               "ExpIntegralEi": Ei, "LambertW": LambertW, "ProductLog": LambertW}

    def rebuild(a):
        name = functions.get(a.func.__name__, a.func.__name__)
        args = a.args
        if name.startswith("DERIV"):
            base, *orders = name[5:].split("o")
            base = functions.get(base, base)
            f = (Function(base)(*coords) if coords and UNKNOWN.match(base)
                 else Function(base)(*args))
            spec = [(v, int(k)) for v, k in zip(args, orders, strict=True) if int(k)]
            return Derivative(f, *spec)
        if name in special:  # parse_mathematica leaves Erf[...] an unknown function
            return special[name](*args)
        if coords and UNKNOWN.match(name):
            return Function(name)(*coords)
        return Function(name)(*args) if name != a.func.__name__ else a

    e = e.replace(lambda a: isinstance(a, AppliedUndef), rebuild)
    if coords:
        e = e.xreplace({s: Function(s.name)(*coords) for s in e.free_symbols
                        if UNKNOWN.match(s.name)})
    return e


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout


CACHE = HERE / "cache"


def _source_hash():
    """delierium's source: a change invalidates the cached equations."""
    import hashlib

    h = hashlib.sha256()
    for f in sorted((HERE.parent / "src" / "delierium").rglob("*.py")):
        h.update(f.read_bytes())
    return h.hexdigest()[:16]


def cached_determining_equations(entry):
    """(infinitesimals, delierium's determining equations) of entry, the
    equations cached in benchmarks/cache (srepr), keyed by the entry and
    delierium's source."""
    import hashlib
    import os

    from sympy import sympify, srepr

    indep, dep = entry.variables()
    infinitesimals = create_infinitesimals(dep, indep)
    key = hashlib.sha256(repr((entry.equations, entry.independent, entry.dependent,
                               _source_hash())).encode()).hexdigest()[:24]
    path = CACHE / f"deteq-{key}.txt"
    if path.exists():
        return infinitesimals, [sympify(line) for line in path.read_text().splitlines()]
    system = determining_equations(entry, infinitesimals)
    CACHE.mkdir(exist_ok=True)
    tmp = path.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text("\n".join(srepr(e) for e in system) + "\n")
    os.replace(tmp, path)  # atomic: several workers may write the same entry
    return infinitesimals, system


def checker(entry):
    """A function generator -> it solves delierium's determining equations
    (computed once per entry, cached across tools)."""
    indep, dep = entry.variables()
    infinitesimals, system = cached_determining_equations(entry)
    plain = {d: Symbol(d.func.__name__) for d in dep}

    def check(generator):
        values = dict(zip(entry.independent + entry.dependent, generator, strict=True))
        solution = {
            f.func: Lambda(tuple(a.xreplace(plain) for a in f.args),
                           values[str(v.xreplace(plain))])
            for v, f in infinitesimals.items()
        }
        return all(vanishes(e.xreplace(plain).subs(solution).doit()) for e in system)

    return check


def check_generator(entry, generator):
    return checker(entry)(generator)


def independent(generators, coordinates):
    """A maximal subset of the generators independent over the constants
    (MathLie's integration constants can be redundant, e.g. k1 + k4)."""
    basis = []
    for g in generators:
        if all(c == 0 for c in g):
            continue
        if basis:
            try:
                LieAlgebra(basis, coordinates)._coordinates_of(VectorField(g, coordinates))
                continue
            except NotClosedError:
                pass
        basis.append(g)
    return basis


def solution_dimension(r, rename, coords):
    """The dimension of the generators' space when conditions or free
    functions remain: the remaining conditions are linear and homogeneous in
    the constants k_i and the functions free[i], xi[i], phi[i]; delierium's
    Janet basis gives the dimension of their solution space and of its
    kernel (all infinitesimals 0). The difference is the dimension (None if
    both are infinite)."""
    infinitesimals = [parse(c, rename, coords) for c in r["infinitesimals"]]
    system = [parse(c, rename, coords) for c in r["remaining"]]
    # which coordinates each unknown really depends on, as MathLie wrote it
    depends = {}
    for text in r["infinitesimals"] + r["remaining"]:
        for e in [parse(text, rename)]:
            for a in e.atoms(AppliedUndef):
                name = a.func.__name__
                if name.startswith("DERIV"):
                    name = name[5:].split("o")[0]
                if UNKNOWN.match(name):
                    depends.setdefault(name, set()).update(a.args)
            for s in e.free_symbols:
                if UNKNOWN.match(s.name):
                    depends.setdefault(s.name, set())
    free = [Function(name)(*coords) for name in sorted(depends)]
    for f in free:
        system += [f.diff(v) for v in coords if v not in depends[f.func.__name__]]
    return projected_dimension(system, free, infinitesimals, coords)


def projected_dimension(system, unknowns, infinitesimals, coords):
    """The dimension of the space of the infinitesimals, where system (linear,
    homogeneous in unknowns) constrains the unknowns the infinitesimals are
    built from. New functions X_j = infinitesimals[j]; a Janet basis in an
    elimination ranking (every derivative of the unknowns above every
    derivative of the X_j) contains a Janet basis of the conditions on the
    X_j alone; its rank is the dimension. Redundant unknowns (two free
    functions where one would do) do not count."""
    xs = [Function(f"X{j}")(*coords) for j in range(len(infinitesimals))]
    system = list(system) + [x - e for x, e in zip(xs, infinitesimals, strict=True)]
    funcs = list(unknowns) + xs
    n = len(unknowns)

    def eliminate(funcs_, variables):
        m = Mgrevlex(funcs_, variables)
        block = [0] * len(variables) + [1] * n + [0] * (len(funcs_) - n)
        return m.row_insert(0, Matrix(1, len(block), block))

    basis = JanetBasis(system, funcs, coords, sort_order=eliminate)
    rest = [e.expression() if hasattr(e, "expression") else e for e in basis.S]
    rest = [e for e in rest if not any(e.has(u.func) for u in unknowns)]
    rank = JanetBasis(rest, xs, coords).rank() if rest else oo
    return INFINITE if rank == oo else int(rank)


MEMORY = 6 * 2**30  # per entry; SymPy can grow beyond 20 GB on one


def _limit_memory():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))


def _child(func, job, conn):
    _limit_memory()
    try:
        conn.send(func(job))
    except BaseException as ex:  # noqa: BLE001
        conn.send({"crashed": f"{type(ex).__name__}: {str(ex)[:80]}"})


def _isolated(func, job, failed, timeout):
    """func(job) in a fresh forked process (SymPy's caches grow from entry to
    entry; a crash loses only this entry); the row gets compare_time."""
    import multiprocessing
    import warnings

    ctx = multiprocessing.get_context("fork")
    reader, writer = ctx.Pipe(duplex=False)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", DeprecationWarning)  # fork with threads
        proc = ctx.Process(target=_child, args=(func, job, writer))
        proc.start()
    writer.close()
    result = None
    t0 = time.time()
    if reader.poll(timeout):
        try:
            result = reader.recv()
        except EOFError:
            pass
    if proc.is_alive():
        proc.kill()
    proc.join()
    if result is None:
        result = {"crashed": f"exit code {proc.exitcode}"}
    seconds = round(time.time() - t0, 2)
    if "crashed" in result:
        return failed(job, result["crashed"]) | {"compare_time": seconds}
    return result | {"compare_time": seconds}


RETRY = ("crashed", "timeout", "out of memory")  # what --retry recomputes


def pool_map(func, jobs, workers, partial, failed, timeout, retry=False):
    """func over jobs, at most workers at a time, each in its own process
    limited to MEMORY. failed(job, reason) gives the row of a crashed job.
    Every row (a dict with "name") is appended to the file partial as it
    comes; on a rerun, the jobs already there are skipped, with retry except
    those that hit a limit (RETRY in their status or check). Returns
    {index: row}."""
    from concurrent.futures import ThreadPoolExecutor, as_completed

    partial = Path(partial)
    done = {}
    if partial.exists():
        for line in partial.read_text().splitlines():
            row = json.loads(line)
            limit = str(row.get("status", "")) + str(row.get("check", ""))
            if retry and any(r in limit for r in RETRY) and "LIEPDE" not in limit:
                continue  # the tool's own timeout is not retried
            done[row["name"]] = row
    todo = [j for j in jobs if j[0]["name"] not in done]
    print(f"{len(done)} done before, {len(todo)} to do", flush=True)
    with ThreadPoolExecutor(workers) as pool, partial.open("a") as out:
        futures = [pool.submit(_isolated, func, j, failed, timeout + 60) for j in todo]
        for f in as_completed(futures):
            row = f.result()
            done[row["name"]] = row
            out.write(json.dumps(row, default=str) + "\n")
            out.flush()
    return done


def compare_failed(job, reason):
    r, _ = job
    e = entry_of(r)
    return {"index": r["index"], "name": e.name, "expected": e.dimension, "status": r["status"],
            "time": r["ms"] / 1000, "check": f"crashed: {reason}"}


def compare_one(job):
    r, timeout = job
    e = entry_of(r)
    row = {"index": r["index"], "name": e.name, "expected": e.dimension, "status": r["status"],
           "time": r["ms"] / 1000}
    if r["status"] != "ok":
        return row
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(timeout)
    try:
        # the equation's parameters too (lambda_ -> lambdaZ in Mathematica)
        names_ = set(e.independent + e.dependent)
        names_ |= {str(s) for q in e.parsed_equations() for s in q.free_symbols}
        rename = {n: safe(n) for n in names_}
        texts = [c for g in r["generators"] for c in g] + r["infinitesimals"] + r["remaining"]
        names = set(rename) | {s for c in texts for s in re.findall(r"q\w+", c)}
        # MathLie's own names (qk1 for k1 ...), not those of the catalogue
        known = set(rename.values())
        rename |= {n[1:]: n for n in names if n.startswith("q") and n not in known}
        coords = [Symbol(v) for v in e.independent + e.dependent]
        conditions = r["free"] or r["remaining"]
        if conditions:
            row["unsolved"] = len(r["remaining"])
            row["dimension"] = solution_dimension(r, rename, coords)
            return row  # no explicit generators: they solve the conditions only together
        gens = independent(
            [tuple(parse(c, rename) for c in g) for g in r["generators"]], coords
        )
        row["dimension"] = len(gens)
        check = checker(e)
        row["wrong_generators"] = [i for i, g in enumerate(gens) if not check(g)]
        if gens:
            algebra = LieAlgebra(gens, coords)
            try:
                algebra.structure_constants
                row["closed"] = True
            except NotClosedError:
                row["closed"] = False
            if e.generators:
                missing = []
                for g in e.parsed_generators():
                    try:
                        algebra._coordinates_of(VectorField(g, coords))
                    except NotClosedError:
                        missing.append(g)
                row["catalogue_not_in_span"] = [str(g) for g in missing]
    except Timeout:
        row["check"] = "timeout"
    except MemoryError:
        row["check"] = "out of memory"
    except Exception as ex:  # noqa: BLE001
        row["check"] = f"{type(ex).__name__}: {str(ex)[:100]}"
    finally:
        signal.alarm(0)
    return row


def compare(args):
    results = [json.loads(line) for line in Path(args.results).read_text().splitlines()]
    results = [r for r in results if args.only in r["name"]]
    out = Path(args.out or HERE / "mathlie-compare.jsonl")
    global MEMORY  # noqa: PLW0603  (read by the forked workers)
    MEMORY = args.memory * 2**30
    done = pool_map(compare_one, [(r, args.timeout) for r in results], args.jobs,
                    out.with_suffix(".partial"), compare_failed, args.timeout, args.retry)
    rows = [done[r["name"]] for r in results]
    with out.open("w") as f:
        for row in rows:
            print(json.dumps(row, default=str), flush=True)
            f.write(json.dumps(row, default=str) + "\n")
    summary(rows)


def summary(rows):
    def agree(r):
        return r.get("dimension") == r["expected"]

    ok = [r for r in rows if r["status"] == "ok"]
    print(f"\n{len(rows)} entries, MathLie answered {len(ok)}")
    for s in sorted({r["status"] for r in rows} - {"ok"}):
        print(f"  {s}: {sum(r['status'] == s for r in rows)}")
    print(f"dimension as catalogue: {sum(agree(r) for r in ok)}")
    print(f"dimension differs: {sum(not agree(r) for r in ok)}")
    print(f"with remaining conditions (dimension from their Janet basis): "
          f"{sum('unsolved' in r for r in ok)}")
    print(f"comparison failed or timed out: {sum('check' in r for r in ok)}")
    print(f"with generators failing delierium's determining equations: "
          f"{sum(bool(r.get('wrong_generators')) for r in ok)}")
    print(f"not closed: {sum(r.get('closed') is False for r in ok)}")
    print(f"catalogue generators outside MathLie's span: "
          f"{sum(bool(r.get('catalogue_not_in_span')) for r in ok)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("run")
    p.add_argument("--only", default="")
    p.add_argument("--timeout", type=int, default=60)
    p.add_argument("--jobs", type=int, default=4)
    p.add_argument("--memory", type=int, default=4, help="GB per entry")
    p.add_argument("--isolated", action="store_true",
                   help="a process per entry with a hard memory limit, 2 at a time")
    p.add_argument("--retry", default="", help="PREVIOUS.jsonl:STATUS")
    p.add_argument("--output", default=str(HERE / "mathlie.jsonl"))
    p = sub.add_parser("compare")
    p.add_argument("results")
    p.add_argument("--timeout", type=int, default=60)
    p.add_argument("--memory", type=int, default=6, help="GB per entry")
    p.add_argument("--retry", action="store_true",
                   help="recompute the entries that hit a limit (with more --timeout/--memory)")
    p.add_argument("--jobs", type=int, default=1)
    p.add_argument("--only", default="")
    p.add_argument("--out", default="")
    args = parser.parse_args()
    {"run": run, "compare": compare}[args.command](args)
