"""Benchmark: generators of the symmetry algebra by the ansatz of
delierium.solve (#9) on the catalogue entries with a finite algebra.

For every entry, in its own process (memory limit, timeout): the dimension
(Janet basis rank), the generators found by LieSymmetries.generators(),
whether they are as many as the dimension (complete) and whether every one
satisfies the determining equations (verified).

Usage:

    uv run python benchmarks/ansatz_generators.py run --out results.jsonl [--jobs 3] [--timeout 180]
        [--only-incomplete earlier.jsonl]
    uv run python benchmarks/ansatz_generators.py report results.jsonl
"""

import argparse
import json
import os
import resource
import subprocess
import sys
import time
from collections import Counter

MEMORY_LIMIT = 4 * 2**30


def worker(name: str) -> None:
    """Run one catalogue entry, print one JSON line."""
    sys.path.insert(0, os.getcwd())
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY_LIMIT, MEMORY_LIMIT))
    from delierium import lie_symmetries  # pylint: disable=import-outside-toplevel
    from tests.symmetry_catalog import CATALOG  # pylint: disable=import-outside-toplevel

    entry = next(e for e in CATALOG if e.name == name)
    indep, dep = entry.variables()
    equations = entry.parsed_equations()
    start = time.time()
    s = lie_symmetries(equations if len(equations) > 1 else equations[0], dep, indep)
    generators = s.generators()
    verified = all(s.verify(generators))
    print(
        json.dumps(
            {
                "name": name,
                "kind": entry.kind,
                "dimension": str(s.dimension),
                "found": len(generators),
                "complete": s.complete(generators),
                "verified": verified,
                "seconds": round(time.time() - start, 1),
            }
        )
    )


def finite_entries() -> list[str]:
    sys.path.insert(0, os.getcwd())
    from tests.symmetry_catalog import CATALOG  # pylint: disable=import-outside-toplevel

    return [e.name for e in CATALOG if isinstance(e.dimension, int)]


def incomplete_entries(path: str) -> list[str]:
    """The entries of an earlier result file that are not complete."""
    with open(path, encoding="utf-8") as f:
        records = [json.loads(line) for line in f]
    return [r["name"] for r in records if r["status"] != "ok" or not r["complete"]]


def run(out: str, jobs: int, timeout: int, only_incomplete: str | None = None) -> None:
    names = incomplete_entries(only_incomplete) if only_incomplete else finite_entries()
    pending = list(names)
    running: dict[str, tuple[subprocess.Popen, float]] = {}
    with open(out, "a", encoding="utf-8") as f:
        while pending or running:
            while pending and len(running) < jobs:
                name = pending.pop(0)
                p = subprocess.Popen(  # pylint: disable=consider-using-with
                    ["nice", "-n", "19", sys.executable, __file__, "worker", name],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )
                running[name] = (p, time.time())
            for name, (p, started) in list(running.items()):
                if p.poll() is None and time.time() - started < timeout:
                    continue
                if p.poll() is None:
                    p.kill()
                    p.wait()
                    record = {"name": name, "status": "timeout"}
                else:
                    output, error = p.communicate()
                    lines = [line for line in output.splitlines() if line.startswith("{")]
                    if lines:
                        record = json.loads(lines[-1]) | {"status": "ok"}
                    else:
                        record = {"name": name, "status": "error", "error": error.strip()[-300:]}
                f.write(json.dumps(record) + "\n")
                f.flush()
                del running[name]
            time.sleep(0.5)


def report(files: list[str]) -> None:
    records = {}
    for path in files:
        with open(path, encoding="utf-8") as f:
            for line in f:
                r = json.loads(line)
                records[r["name"]] = r
    status = Counter(r["status"] for r in records.values())
    ok = [r for r in records.values() if r["status"] == "ok"]
    print(f"{len(records)} entries: {dict(status)}")
    print(f"complete: {sum(r['complete'] for r in ok)}, verified: {sum(r['verified'] for r in ok)}")
    by_kind = Counter((r["kind"], r["complete"]) for r in ok)
    for (kind, complete), n in sorted(by_kind.items()):
        print(f"  {kind:5s} complete={complete}: {n}")
    print("not verified:", [r["name"] for r in ok if not r["verified"]])


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    w = sub.add_parser("worker")
    w.add_argument("name")
    r = sub.add_parser("run")
    r.add_argument("--out", required=True)
    r.add_argument("--jobs", type=int, default=3)
    r.add_argument("--timeout", type=int, default=180)
    r.add_argument("--only-incomplete", help="only the entries not complete in this result file")
    p = sub.add_parser("report")
    p.add_argument("files", nargs="+")
    args = parser.parse_args()
    if args.command == "worker":
        worker(args.name)
    elif args.command == "run":
        run(args.out, args.jobs, args.timeout, args.only_incomplete)
    else:
        report(args.files)


if __name__ == "__main__":
    main()
