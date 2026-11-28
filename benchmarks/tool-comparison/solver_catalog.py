"""lie_symmetries(...).generators() per finite catalogue entry, with the solver's final
state: one process each, 3 at a time, RLIMIT_AS 6 GB, 300 s.  python solver_catalog.py OUT"""
import json, multiprocessing as mp, resource, sys, time
REPO = "/home/tapir/research-disk/delierium"; OUT, TIMEOUT = sys.argv[1], 300
sys.path[:0] = [REPO + "/src", REPO]

def run(i, q):
    resource.setrlimit(resource.RLIMIT_AS, (6 << 30, 6 << 30))
    import delierium.solve as S
    from delierium import lie_symmetries, verify_symmetries
    from sympy import Derivative
    from tests.symmetry_catalog import CATALOG
    final = {}
    orig = S.run_steps
    def run_steps(state, steps, max_iterations=1000):
        orig(state, steps, max_iterations)
        final["state"] = state
    S.run_steps = run_steps
    e = CATALOG[i]
    try:
        indep, dep = e.variables(); eqs = e.parsed_equations()
        a = (eqs if len(eqs) > 1 else eqs[0], dep if len(dep) > 1 else dep[0], indep if len(indep) > 1 else indep[0])
        t = time.perf_counter(); s = lie_symmetries(*a); g = s.generators(); t = time.perf_counter() - t
        ok = all(bool(r) for r in verify_symmetries(*a, g)) if g else True
        r = {"i": i, "name": e.name, "kind": e.kind, "t": round(t, 2), "dim": str(s.dimension), "expected": e.dimension, "n": len(g), "verified": ok}
        st = final.get("state")
        if st is not None and len(g) < e.dimension:
            def order(eq):
                ds = eq.atoms(Derivative)
                return max((sum(c for _, c in d.variable_count) for d in ds), default=0)
            r |= {"system": [str(x)[:300] for x in st.system[:6]], "neq": len(st.system),
                  "orders": sorted(order(x) for x in st.system),
                  "functions": [str(f) for f in st.functions], "constants": len(st.constants),
                  "history": [h[:160] for h in st.history[-8:]]}
        q.put(r)
    except BaseException as ex:
        q.put({"i": i, "name": e.name, "error": repr(ex)[:200]})

if __name__ == "__main__":
    from tests.symmetry_catalog import CATALOG
    todo = [i for i, e in enumerate(CATALOG) if isinstance(e.dimension, int)]
    ctx = mp.get_context("fork"); running = {}
    with open(OUT, "w") as out:
        while todo or running:
            while todo and len(running) < 3:
                i = todo.pop(0); q = ctx.Queue(); p = ctx.Process(target=run, args=(i, q)); p.start(); running[i] = (p, q, time.time())
            time.sleep(0.05)
            for i, (p, q, t0) in list(running.items()):
                r = None
                if not q.empty(): r = q.get()
                elif not p.is_alive(): r = {"i": i, "name": CATALOG[i].name, "error": f"exit {p.exitcode}"}
                elif time.time() - t0 > TIMEOUT: p.kill(); r = {"i": i, "name": CATALOG[i].name, "error": "timeout"}
                if r is not None:
                    p.join(); del running[i]; out.write(json.dumps(r, default=str) + "\n"); out.flush()
