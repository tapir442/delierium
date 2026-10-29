"""Check a tool's general solution (raw REDUCE output) against delierium:
dimension from the tool's own conditions, and with delierium's determining
equations added; also each function restricted to fewer variables."""
import json, sys
sys.path.insert(0, "benchmarks")
import reduce_symmetries as rs
from mathlie_symmetries import projected_dimension
from sympy import Function, Symbol, Lambda, together, numer, expand
from delierium.infinitesimals import create_infinitesimals
from mathlie_symmetries import BY_NAME
from catalog_helpers import determining_equations

raw, name = sys.argv[1], sys.argv[2]
row = next(r for r in map(json.loads, open(raw)) if r["name"] == name)
entry = BY_NAME[name]
print(name, "|", entry.equations)
cases, expr = rs.parse_output(row["output"], entry, row["names"])
conditions, solution, constants, functions = cases[0]
print("constants", constants, "| functions", functions, "|", len(conditions), "conditions")
coords = [Symbol(v) for v in entry.independent + entry.dependent]
unknowns = [(c, coords) for c in constants] + [(n, coords) for n, _ in functions]
names_ = {n for n, _ in unknowns}
free = [Function(n)(*coords) for n, _ in unknowns]
indep, dep = entry.variables()
keys = [f"xi_x{i}" for i in range(1, len(indep) + 1)] + [f"eta_u{i}" for i in range(1, len(dep) + 1)]
infs_ = [expr(solution.get(k, k if k in names_ else "0"), unknowns) for k in keys]
conds = [expr(c, unknowns) for c in conditions]
deps = dict(functions)
extra = [f.diff(v) for f, (n, _) in zip(free, unknowns) for v in coords if v not in deps.get(n, [])]
infs = create_infinitesimals(dep, indep)
system = determining_equations(entry, infs)
plain = {d: Symbol(d.func.__name__) for d in dep}
values = dict(zip(entry.independent + entry.dependent, infs_))
sub = {f.func: Lambda(tuple(a.xreplace(plain) for a in f.args), values[str(v.xreplace(plain))])
       for v, f in infs.items()}
deli = [expand(numer(together(e.xreplace(plain).subs(sub).doit()))) for e in system]
deli = [e for e in deli if e != 0]
print(len(system), "determining equations,", len(deli), "not 0 after substitution")
print("tool's conditions:              ", projected_dimension(conds + extra, free, infs_, coords))
print("plus delierium's equations:     ", projected_dimension(conds + extra + deli, free, infs_, coords))
for f, (n, _) in zip(free, unknowns):
    for v in deps.get(n, []):
        d = projected_dimension(conds + extra + [f.diff(v)], free, infs_, coords)
        print(f"tool's conditions, {n} free of {v}:", d)
print("catalogue:", entry.dimension)
