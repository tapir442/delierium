import json, sys, time, resource
resource.setrlimit(resource.RLIMIT_AS, (4 << 30, 4 << 30))
sys.path.insert(0, "/home/tapir/research-disk/delierium/tests")
from symmetry_catalog import CATALOG
from sympy import ode_order
from delierium import integrate_ode
i = int(sys.argv[1])
e = [e for e in CATALOG if e.kind == "ode" and e.generators][i]
(x,), (y,) = e.variables()
ode = e.parsed_equations()[0]
r = {"i": i, "name": e.name, "eq": e.equations[0], "order": ode_order(ode, y), "ngen": len(e.generators), "dim": str(e.dimension)}
t = time.time()
try:
    s = integrate_ode(ode, y, x, e.parsed_generators())
    r.update(status="ok", result=str(s)[:300])
except NotImplementedError as ex:
    r.update(status="unsolved", msg=str(ex)[:300])
except Exception as ex:
    r.update(status="error", msg=f"{type(ex).__name__}: {ex}"[:300])
r["time"] = round(time.time() - t, 1)
print(json.dumps(r), flush=True)
