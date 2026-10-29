"""delierium's Janet bases against CoCoA 5's JanetBasis (Mario Albert's JBMill)
and Singular's rJanet (rstandard.lib).

Internal benchmark. A linear PDE system with constant coefficients,
sum_a c_a d^a f = 0, is the polynomial ideal of the sum_a c_a x^a (d/dx -> x);
for the same term order (degrevlex, x > y > z > ...) both programs must give
the same Janet basis, element by element.

    uv run python benchmarks/cocoa_janet.py [--n 200] [--seed 0] [--timeout 60]

Per system: the Janet basis of both (monic, as sets), times, and if they
differ whether they generate the same ideal (SymPy's reduced Groebner basis).
"""

import argparse
import json
import random
import re
import signal
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

from sympy import Derivative, Function, Poly, Rational, groebner, symbols, sympify

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from delierium.janet_basis import JanetBasis

HERE = Path(__file__).resolve().parent
COCOA = Path("/home/tapir/research-disk/cocoa-5.4")
NAMES = "xyzw"


# Systems from the literature, as polynomials (variables x > y > z > w)
EXAMPLES = [
    ("CoCoA manual", 3, ["x - y", "x**2 - z + 1", "x**3 - y**2"]),
    ("Janet's example (Seiler 3.1)", 3, ["z**2 - y**2", "x*z - y*z"]),
    ("monomial x*y, y*z", 3, ["x*y", "y*z"]),
    ("monomial x**2, x*y**2, y**3 (staircase)", 2, ["x**2", "x*y**2", "y**3"]),
    ("Gerdt-Blinkov cyclic 3 (as operators)", 3, ["x + y + z", "x*y + y*z + z*x", "x*y*z - 1"]),
    ("heat-type x**2 - y, z", 3, ["x**2 - y", "z"]),
    ("Pommaret: x**2 - y*z, x*y - z**2", 3, ["x**2 - y*z", "x*y - z**2"]),
]


def random_system(rng, n):
    gens = symbols(list(NAMES[:n]))
    system = []
    for _ in range(rng.randint(2, 4)):
        poly = 0
        for _ in range(rng.randint(1, 4)):
            exps = [rng.randint(0, 2) for _ in range(n)]
            while sum(exps) > 3:
                exps[rng.randrange(n)] = 0
            coeff = Rational(rng.choice([-3, -2, -1, 1, 2, 3]), rng.choice([1, 1, 1, 2]))
            monomial = 1
            for g, e in zip(gens, exps, strict=True):
                monomial *= g**e
            poly += coeff * monomial
        if poly != 0 and not poly.is_number:
            system.append(sympify(poly))
    return system


def to_operator(poly, gens, f):
    """sum c_a x^a -> sum c_a d^a f."""
    result = 0
    for monom, coeff in Poly(poly, *gens).terms():
        spec = [(g, e) for g, e in zip(gens, monom, strict=True) if e]
        result += coeff * (Derivative(f, *spec) if spec else f)
    return result


def to_polynomial(expr, gens, f):
    expr = expr.replace(
        lambda a: isinstance(a, Derivative),
        lambda a: _monomial(a.variable_count),
    )
    return expr.xreplace({f: 1})


def _monomial(variable_count):
    m = 1
    for v, k in variable_count:
        m *= v**k
    return m


def monic(polys, gens):
    out = set()
    for p in polys:
        P = Poly(p, *gens)
        if P.is_zero:
            continue
        out.add((P / P.LC(order="grevlex")).as_expr().expand())
    return out


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout


def delierium_basis(system, gens, timeout):
    f = Function("f")(*gens)
    signal.alarm(timeout)
    t0 = time.time()
    try:
        J = JanetBasis([to_operator(p, gens, f) for p in system], (f,), gens)
        basis = [to_polynomial(e.expression(), gens, f) for e in J.S]
        return basis, time.time() - t0, "ok"
    except Timeout:
        return None, timeout, "timeout"
    except Exception as ex:
        return None, time.time() - t0, f"{type(ex).__name__}: {str(ex)[:100]}"
    finally:
        signal.alarm(0)


def cocoa_bases(systems):
    """[(basis, seconds)] for each (system, gens), in one CoCoA session."""
    lines = []
    for i, (system, gens) in enumerate(systems):
        ring = ",".join(str(g) for g in gens)
        ideal = ", ".join(str(p).replace("**", "^") for p in system)
        lines += [
            f"use R{i} ::= QQ[{ring}], DegRevLex;",
            "t0 := CpuTime();",
            f"JB := JanetBasis(ideal({ideal}));",
            "t := CpuTime() - t0;",
            f'println "BEGIN {i} ", t;',
            "foreach g in JB do println g; endforeach;",
            f'println "END {i}";',
        ]
    out = subprocess.run(
        [str(COCOA / "cocoa5")], input="\n".join(lines) + "\n", capture_output=True,
        text=True, cwd=COCOA, check=False,
    ).stdout
    results = {}
    for m in re.finditer(r"BEGIN (\d+) ([\d/]+)\n(.*?)\nEND \1\n", out, re.S):
        i = int(m.group(1))
        gens = systems[i][1]
        names = {str(g): g for g in gens}
        basis = [sympify(line.replace("^", "**"), locals=names)
                 for line in m.group(3).splitlines()
                 if line.strip() and not line.startswith("#")]
        results[i] = (basis, float(Fraction(m.group(2))))
    return results, out


def singular_polynomial(p, gens):
    """p in Singular's syntax: y^2/2 would be y^(2/2) there, so every term is
    (coefficient)*monomial."""
    terms = []
    for monom, coeff in Poly(p, *gens).terms():
        factors = [f"{g}^{e}" for g, e in zip(gens, monom, strict=True) if e]
        terms.append("*".join([f"({coeff})", *factors]))
    return " + ".join(terms)


def singular_bases(systems):
    """[(basis, seconds)] for each (system, gens) from Singular's rJanet
    (rstandard.lib, Kanwal and Pfister), in one session."""
    lines = ['LIB "rstandard.lib";', 'system("--ticks-per-sec", 1000);']
    for i, (system, gens) in enumerate(systems):
        ring = ",".join(str(g) for g in gens)
        ideal = ", ".join(singular_polynomial(p, gens) for p in system)
        lines += [
            f"ring R{i} = 0, ({ring}), dp;",
            "short = 0;",
            f"ideal I = {ideal};",
            "int t0 = rtimer;",
            "ideal J = rJanet(I);",
            "int t = rtimer - t0;",
            f'print("BEGIN {i} " + string(t));',
            'for (int k = 1; k <= ncols(J); k++) { print("P " + string(J[k])); }',
            f'print("END {i}");',
            "kill t0, t, k;",
        ]
    lines.append("quit;")
    out = subprocess.run(
        ["Singular", "-q"], input="\n".join(lines) + "\n", capture_output=True, text=True,
        check=False,
    ).stdout
    errors = [line for line in out.splitlines() if line.lstrip().startswith("? ")]
    if errors:  # e.g. a syntax error: rJanet then runs on the previous ideal
        raise RuntimeError("Singular: " + "; ".join(errors[:5]))
    results = {}
    for m in re.finditer(r"BEGIN (\d+) (\d+)\n(.*?)\nEND \1\n", out, re.S):
        i = int(m.group(1))
        names = {str(g): g for g in systems[i][1]}
        basis = [sympify(line[2:].replace("^", "**"), locals=names)
                 for line in m.group(3).splitlines() if line.startswith("P ")]
        results[i] = (basis, int(m.group(2)) / 1000)
    return results, out


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=200, help="random systems")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--out", default=str(HERE / "cocoa-janet.jsonl"))
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, _alarm)

    rng = random.Random(args.seed)
    cases = []
    for name, n, polys in EXAMPLES:
        gens = symbols(list(NAMES[:n]))
        cases.append((name, [sympify(p, locals={str(g): g for g in gens}) for p in polys], gens))
    for k in range(args.n):
        n = rng.choice([2, 2, 3, 3, 4])
        cases.append((f"random {k}", random_system(rng, n), symbols(list(NAMES[:n]))))
    cases = [c for c in cases if c[1]]

    t0 = time.time()
    cocoa, raw = cocoa_bases([(system, gens) for _, system, gens in cases])
    print(f"CoCoA: {len(cocoa)} of {len(cases)} in {time.time() - t0:.0f} s", flush=True)
    if not cocoa:
        print(raw[-2000:])
    t0 = time.time()
    singular, raw = singular_bases([(system, gens) for _, system, gens in cases])
    print(f"Singular: {len(singular)} of {len(cases)} in {time.time() - t0:.0f} s", flush=True)
    if not singular:
        print(raw[-2000:])

    counts = {}
    with open(args.out, "w") as out:
        for i, (name, system, gens) in enumerate(cases):
            row = {"name": name, "system": [str(p) for p in system], "vars": len(gens)}
            basis, seconds, status = delierium_basis(system, gens, args.timeout)
            row["delierium"] = {"status": status, "time": round(seconds, 3)}
            if i in cocoa:
                row["cocoa"] = {"time": cocoa[i][1], "size": len(cocoa[i][0])}
            if i in singular:
                row["singular"] = {"time": singular[i][1], "size": len(singular[i][0])}
                if i in cocoa:
                    row["singular"]["= cocoa"] = monic(singular[i][0], gens) == monic(
                        cocoa[i][0], gens
                    )
            if basis is not None and i in cocoa:
                mine, theirs = monic(basis, gens), monic(cocoa[i][0], gens)
                row["delierium"]["size"] = len(mine)
                if mine == theirs:
                    verdict = "same Janet basis"
                else:
                    same_ideal = (
                        groebner(list(mine), *gens, order="grevlex").exprs
                        == groebner(list(theirs), *gens, order="grevlex").exprs
                    )
                    verdict = "different basis, same ideal" if same_ideal else "different ideal"
                    row["only delierium"] = [str(p) for p in mine - theirs]
                    row["only cocoa"] = [str(p) for p in theirs - mine]
            elif i not in cocoa:
                verdict = "CoCoA failed"
            else:
                verdict = f"delierium {status}"
            row["verdict"] = verdict
            counts[verdict] = counts.get(verdict, 0) + 1
            out.write(json.dumps(row) + "\n")
            if verdict != "same Janet basis":
                print(name, "|", verdict, "|", row.get("only delierium"), row.get("only cocoa"),
                      flush=True)
    print(json.dumps(counts, indent=1))
    rows = [json.loads(line) for line in open(args.out)]
    same = sum(r.get("singular", {}).get("= cocoa", False) for r in rows)
    print(f"Singular's rJanet = CoCoA's JanetBasis: {same} of {len(rows)}")


if __name__ == "__main__":
    main()
