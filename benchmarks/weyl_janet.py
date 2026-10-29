"""delierium's Janet bases with polynomial coefficients against Singular's Plural.

Internal benchmark. A linear PDE system for f(x, y, ...) with polynomial
coefficients is a left ideal of the Weyl algebra K[x][D]; Plural computes its
Groebner basis for a block order: the derivatives first (grevlex, as
delierium's Mgrevlex), then the coefficients. That is also a Groebner basis
over K(x)[D], where delierium computes. Checked per system:

1. every element of delierium's Janet basis reduces to zero by Plural's basis,
2. every element of Plural's basis reduces to zero by delierium's,
3. delierium's leading derivatives are the minimal Janet completion of the
   minimal leading derivatives of Plural's basis.

The reductions are delierium's reduce_by_system (Leibniz rule).

    uv run python benchmarks/weyl_janet.py [--n 100] [--seed 0] [--timeout 60]
"""

import argparse
import json
import random
import re
import signal
import subprocess
import sys
import time
from pathlib import Path

from sympy import Derivative, Function, Integer, Poly, Rational, symbols, sympify

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from delierium.janet_basis import LHDP, JanetBasis, reduce_by_system  # noqa: E402
from delierium.multipliers import janet_completion  # noqa: E402

HERE = Path(__file__).resolve().parent
NAMES = "xyz"

EXAMPLES = [
    ("Leibniz example: f_y = 0, f_x - y f = 0 (only f = 0)", 2, ["Dy", "Dx - y"]),
    ("Euler operator and translation", 2, ["x*Dx + y*Dy - 2", "Dx^2"]),
    ("x f_xx - f_y, f_xy", 2, ["x*Dx^2 - Dy", "Dx*Dy"]),
    ("Weyl: x Dx - y Dy, Dx Dy - 1", 2, ["x*Dx - y*Dy", "Dx*Dy - 1"]),
    ("heat-type with x: f_t - x f_xx, f_x", 2, ["Dy - x*Dx^2", "y*Dx + 1"]),
]


def random_operator(rng, n):
    """sum of 1-3 terms c(x) D^a with c a polynomial of degree <= 1."""
    xs = symbols(list(NAMES[:n]))
    ds = symbols([f"D{v}" for v in NAMES[:n]])
    op = Integer(0)
    for _ in range(rng.randint(1, 3)):
        a = [rng.randint(0, 2) for _ in range(n)]
        while sum(a) > 2:
            a[rng.randrange(n)] = 0
        coeff = Rational(rng.choice([-3, -2, -1, 1, 2, 3]), rng.choice([1, 1, 2]))
        if rng.random() < 0.6:
            coeff = coeff * rng.choice(xs) + rng.choice([0, 0, 1, -1, 2])
        mono = Integer(1)
        for d, e in zip(ds, a, strict=True):
            mono *= d**e
        op += coeff * mono
    return op


def to_lhdp(op, xs, ds, f, context):
    """Operator sum c(x) D^a (coefficients left) as an LHDP: sum c(x) d^a f."""
    expr = Integer(0)
    for monom, coeff in Poly(op, *ds).terms():
        spec = [(x, k) for x, k in zip(xs, monom, strict=True) if k]
        expr += coeff * (Derivative(f, *spec) if spec else f)
    return LHDP(expr, context) if expr != 0 else None


def singular_polynomial(op, gens):
    terms = []
    for monom, coeff in Poly(op, *gens).terms():
        factors = [f"{g}^{e}" for g, e in zip(gens, monom, strict=True) if e]
        terms.append("*".join([f"({coeff})", *factors]))
    return " + ".join(terms) if terms else "0"


def _limit_memory():
    import resource

    resource.setrlimit(resource.RLIMIT_AS, (3 * 2**30, 3 * 2**30))


def plural_one(args):
    """(index, basis, seconds) or (index, None, reason): one system in its own
    Singular process, with a time and memory limit (a Groebner basis in the
    Weyl algebra can blow up)."""
    i, system, n, timeout = args
    try:
        res = plural_bases([system], n, timeout)
    except subprocess.TimeoutExpired:
        return i, None, "Plural timeout"
    except RuntimeError as ex:
        return i, None, f"Plural error: {str(ex)[:80]}"
    if 0 not in res:
        return i, None, "Plural failed (memory?)"
    return i, res[0][0], res[0][1]


def plural_bases(systems, n, timeout=None):
    """Left Groebner bases in the Weyl algebra, block order D (grevlex) > x."""
    xs = list(NAMES[:n])
    ds = [f"D{v}" for v in xs]
    # matrix order on (x..., D...): D-degree, grevlex on D (reverse: the last
    # D smallest), then x-degree, grevlex on x
    rows = [[0] * n + [1] * n]
    for k in range(n - 1, 0, -1):
        rows.append([0] * n + [-1 if j == k else 0 for j in range(n)])
    rows.append([1] * n + [0] * n)
    for k in range(n - 1, 0, -1):
        rows.append([-1 if j == k else 0 for j in range(n)] + [0] * n)
    matrix = ",".join(str(v) for row in rows for v in row)
    lines = [
        'LIB "nctools.lib";',
        f"ring r = 0, ({','.join(xs + ds)}), M({matrix});",
        "def W = Weyl(); setring W; short = 0;",
        'system("--ticks-per-sec", 1000);',
    ]
    gens = symbols(xs + ds)
    for i, system in enumerate(systems):
        ideal = ", ".join(singular_polynomial(p, gens) for p in system)
        lines += [
            f"ideal I = {ideal};",
            "int t0 = rtimer;",
            "ideal G = std(I);",
            "int t = rtimer - t0;",
            f'print("BEGIN {i} " + string(t));',
            'for (int k = 1; k <= ncols(G); k++) { print("P " + string(G[k])); }',
            f'print("END {i}");',
            "kill I, G, t0, t, k;",
        ]
    lines.append("quit;")
    out = subprocess.run(
        ["Singular", "-q"], input="\n".join(lines) + "\n", capture_output=True, text=True,
        check=False, timeout=timeout, preexec_fn=_limit_memory,
    )
    errors = [line for line in out.stdout.splitlines() + out.stderr.splitlines()
              if line.lstrip().startswith("? ")]
    if errors:
        raise RuntimeError("Singular: " + "; ".join(errors[:5]))
    names = {str(g): g for g in gens}
    results = {}
    for m in re.finditer(r"BEGIN (\d+) (\d+)\n(.*?)\nEND \1\n", out.stdout, re.S):
        basis = [sympify(line[2:].replace("^", "**"), locals=names)
                 for line in m.group(3).splitlines() if line.startswith("P ")]
        results[int(m.group(1))] = ([b for b in basis if b != 0], int(m.group(2)) / 1000)
    return results


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout


def compare(system, plural, n, timeout):
    xs = symbols(list(NAMES[:n]))
    ds = symbols([f"D{v}" for v in NAMES[:n]])
    f = Function("f")(*xs)
    signal.alarm(timeout)
    try:
        t0 = time.time()
        J = JanetBasis([_expr(op, xs, ds, f) for op in system], (f,), xs)
        seconds = time.time() - t0
        ctx = J.context
        mine = J.S
        theirs = [e for e in (to_lhdp(g, xs, ds, f, ctx) for g in plural) if e is not None]
        r = {"delierium_time": round(seconds, 3), "size": len(mine), "plural_size": len(theirs)}
        r["mine_in_theirs"] = all(reduce_by_system(e, theirs, ctx) is None for e in mine)
        r["theirs_in_mine"] = all(reduce_by_system(e, mine, ctx) is None for e in theirs)
        leading = {tuple(e.order) for e in theirs}
        minimal = [m for m in leading
                   if not any(o != m and all(a >= b for a, b in zip(m, o, strict=True))
                              for o in leading)]
        expected = janet_completion(minimal, n)
        r["same_leading"] = {tuple(e.order) for e in mine} == expected
        r["status"] = "agree" if (r["mine_in_theirs"] and r["theirs_in_mine"]
                                  and r["same_leading"]) else "differ"
        return r
    except Timeout:
        return {"status": "delierium timeout"}
    finally:
        signal.alarm(0)


def _expr(op, xs, ds, f):
    expr = Integer(0)
    for monom, coeff in Poly(op, *ds).terms():
        spec = [(x, k) for x, k in zip(xs, monom, strict=True) if k]
        expr += coeff * (Derivative(f, *spec) if spec else f)
    return expr


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--out", default=str(HERE / "weyl-janet.jsonl"))
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, _alarm)
    rng = random.Random(args.seed)
    cases = []
    for name, n, ops in EXAMPLES:
        gens = symbols(list(NAMES[:n]) + [f"D{v}" for v in NAMES[:n]])
        loc = {str(g): g for g in gens}
        cases.append((name, n, [sympify(o.replace("^", "**"), locals=loc) for o in ops]))
    for k in range(args.n):
        n = rng.choice([2, 2, 3])
        system = [op for op in (random_operator(rng, n) for _ in range(rng.randint(2, 3))) if op != 0]
        cases.append((f"random {k}", n, system))
    from concurrent.futures import ThreadPoolExecutor

    plural, failed = {}, {}
    t0 = time.time()
    with ThreadPoolExecutor(8) as pool:
        jobs = [(i, c[2], c[1], args.timeout) for i, c in enumerate(cases)]
        for i, basis, info in pool.map(plural_one, jobs):
            if basis is None:
                failed[i] = info
            else:
                plural[i] = (basis, info)
    print(f"Plural: {len(plural)} of {len(cases)} in {time.time() - t0:.0f} s", flush=True)
    counts = {}
    with open(args.out, "w") as out:
        for i, (name, n, system) in enumerate(cases):
            row = {"name": name, "system": [str(s) for s in system], "vars": n}
            if i not in plural:
                row["status"] = failed.get(i, "Plural failed")
            else:
                row["plural_time"] = plural[i][1]
                row |= compare(system, plural[i][0], n, args.timeout)
            counts[row["status"]] = counts.get(row["status"], 0) + 1
            out.write(json.dumps(row) + "\n")
            if row["status"] != "agree":
                print(name, "|", row, flush=True)
    print(json.dumps(counts, indent=1))


if __name__ == "__main__":
    main()
