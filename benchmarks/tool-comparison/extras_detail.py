"""sympy-extras' generators for the catalogue entries where it differs (count != dimension,
or a published generator rejected by its check_symmetry), each checked with delierium.
One fork per entry, 60 s, 4 GB, 1 at a time.

    nice -n 19 uv run --with sympy-extras==0.0.2 python benchmarks/tool-comparison/extras_detail.py
"""
import json, multiprocessing as mp, resource, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path[:0] = [str(HERE.parents[1]), str(HERE.parent)]
import sympy_symmetries as ss  # noqa: E402
from sympy import sympify  # noqa: E402
from tests.symmetry_catalog import CATALOG  # noqa: E402

def child(entry, conn):
    resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
    eqs, (indep, dep) = entry.parsed_equations(), entry.variables()
    row = {"name": entry.name}
    try:
        found = ss.extras_symmetries(eqs, dep)
        gens = [tuple(sympify(c) for c in g) for g in found["generators"]]
        plain = {f: __import__("sympy").Symbol(f.func.__name__) for f in dep}
        gens = [tuple(c.xreplace(plain) for c in g) for g in gens]
        ok = ss.deli_verify(eqs, dep, indep, gens) if gens else []
        row |= {"n": len(gens), "wrong": [str(g) for g, b in zip(gens, ok) if not b],
                "generators": [str(g) for g in gens]}
    except BaseException as ex:  # noqa: BLE001
        row |= {"error": repr(ex)[:200]}
    conn.send(row)

def main():
    rows = [json.loads(l) for l in open(HERE / "sympy-catalog.jsonl")]
    by = {}
    for r in rows:
        if r.get("tool"):
            by.setdefault(r["tool"], {})[r["name"]] = r
    todo = []
    for e in CATALOG:
        x, g = by["extras"].get(e.name, {}), by["extras_gens"].get(e.name, {})
        differs = x.get("status") == "ok" and isinstance(e.dimension, int) and int(x["n"]) != e.dimension
        rejected = g.get("status") == "ok" and "False" in g.get("ok", "")
        if differs or rejected:
            todo.append(e)
    print(len(todo), "entries", flush=True)
    ctx = mp.get_context("fork")
    with open(HERE / "extras-detail.jsonl", "w") as out:
        for e in todo:
            a, b = ctx.Pipe(duplex=False)
            p = ctx.Process(target=child, args=(e, b)); p.start(); b.close()
            row = a.recv() if a.poll(60) else {"name": e.name, "error": "timeout"}
            p.kill(); p.join()
            out.write(json.dumps(row) + "\n"); out.flush()

if __name__ == "__main__":
    main()
