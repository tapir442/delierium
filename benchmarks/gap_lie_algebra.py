"""delierium's LieAlgebra (#11) against GAP on the symmetry catalogue.

Internal benchmark. For every complete list of generators of a finite
algebra in the catalogue, delierium computes the structure constants; GAP
builds LieAlgebraByStructureConstants from them and computes the derived and
lower central series, solvability, nilpotency, the center and the Killing
form, which delierium computes too. Constants depending on parameters get
random rational values (seeded by the entry's name), the same for both.
GAP also gives the Levi decomposition and the type of the semisimple part.

    uv run python benchmarks/gap_lie_algebra.py [--out gap-lie.jsonl]
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

from sympy import Matrix, Rational, Symbol, nsimplify

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from delierium.lie_algebra import LieAlgebra  # noqa: E402
from tests.symmetry_catalog import CATALOG, INFINITE  # noqa: E402

HERE = Path(__file__).resolve().parent


class Timeout(Exception):
    pass


def _alarm(*_):
    raise Timeout


def structure_constants(entry, timeout):
    """(algebra, constants as rationals, parameter values) or a reason."""
    coordinates = [Symbol(v) for v in entry.independent + entry.dependent]
    algebra = LieAlgebra(entry.parsed_generators(), coordinates)
    signal.alarm(timeout)
    try:
        c = algebra.structure_constants
    finally:
        signal.alarm(0)
    r = algebra.dimension
    parameters = sorted({s for row in c for col in row for e in col for s in e.free_symbols}, key=str)
    rng = random.Random(entry.name)
    values = {p: Rational(rng.randint(2, 30), rng.randint(1, 7)) for p in parameters}
    numeric = [[[nsimplify(e.subs(values)) for e in col] for col in row] for row in c]
    if not all(e.is_Rational for row in numeric for col in row for e in col):
        return None, "constants not rational at the parameter values"
    # delierium's own results, from the same numeric constants
    algebra.__dict__["structure_constants"] = numeric
    return (algebra, numeric, {str(k): str(v) for k, v in values.items()}, r), None


def delierium_properties(algebra):
    killing = algebra.killing_form()
    return {
        "derived": algebra.derived_series(),
        "lower_central": algebra.lower_central_series(),
        "solvable": algebra.is_solvable(),
        "nilpotent": algebra.is_nilpotent(),
        "abelian": algebra.is_abelian(),
        "center": algebra.center().rows,
        "killing_rank": killing.rank() if killing.rows else 0,
        "semisimple": bool(algebra.is_semisimple()),
    }


GAP_PROPERTIES = r"""
props := function(i, L)
  local K, levi, s, rk;
  if Dimension(L) = 0 then
    Print("R ", i, " [ 0 ] [ 0 ] true true true 0 0 0 0 \"\"\n");
    return;
  fi;
  K := KillingMatrix(Basis(L));
  levi := LeviMalcevDecomposition(L);
  if Dimension(levi[1]) > 0 then s := SemiSimpleType(levi[1]); else s := ""; fi;
  Print("R ", i, " ",
        List(LieDerivedSeries(L), Dimension), " ",
        List(LieLowerCentralSeries(L), Dimension), " ",
        IsLieSolvable(L), " ", IsLieNilpotent(L), " ", IsLieAbelian(L), " ",
        Dimension(LieCentre(L)), " ", RankMat(K), " ", Dimension(levi[1]), " ",
        Dimension(LieSolvableRadical(L)), " \"", s, "\"\n");
end;
"""


def gap_script(cases):
    # an error goes back to the top level instead of a break loop, so the
    # following algebras are still computed
    lines = ["BreakOnError := false;;", GAP_PROPERTIES]
    for i, (_, numeric, _, r) in cases.items():
        lines.append(f'Print("S {i}\\n");;')
        lines.append(f'T := EmptySCTable({r}, 0, "antisymmetric");;')
        for a in range(r):
            for b in range(a + 1, r):
                entries = []
                for k in range(r):
                    if numeric[a][b][k] != 0:
                        entries += [str(numeric[a][b][k]), str(k + 1)]
                if entries:
                    lines.append(f"SetEntrySCTable(T, {a + 1}, {b + 1}, [{', '.join(entries)}]);;")
        lines.append("L := LieAlgebraByStructureConstants(Rationals, T);;")
        lines.append(f"props({i}, L);;")
    lines.append("QUIT;")
    return "\n".join(lines) + "\n"


def parse_gap(out):
    results = {}
    pattern = re.compile(
        r"^R (\d+) (\[[^\]]*\]) (\[[^\]]*\]) (true|false) (true|false) (true|false) "
        r'(\d+) (\d+) (\d+) (\d+) "([^"]*)"',
        re.M,
    )
    for m in pattern.finditer(out):
        i = int(m.group(1))
        results[i] = {
            "derived": json.loads(m.group(2)),
            "lower_central": json.loads(m.group(3)),
            "solvable": m.group(4) == "true",
            "nilpotent": m.group(5) == "true",
            "abelian": m.group(6) == "true",
            "center": int(m.group(7)),
            "killing_rank": int(m.group(8)),
            "levi_dimension": int(m.group(9)),
            "radical_dimension": int(m.group(10)),
            "semisimple_type": m.group(11),
        }
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default=str(HERE / "gap-lie.jsonl"))
    parser.add_argument("--timeout", type=int, default=60)
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, _alarm)

    complete = [
        (i, e) for i, e in enumerate(CATALOG)
        if e.dimension not in (INFINITE, None) and len(e.generators) == e.dimension
    ]
    cases, rows = {}, {}
    t0 = time.time()
    for i, e in complete:
        row = {"name": e.name, "dimension": e.dimension}
        try:
            result, reason = structure_constants(e, args.timeout)
        except Timeout:
            result, reason = None, "timeout"
        if result is None:
            row["status"] = reason
        else:
            algebra, numeric, values, r = result
            cases[i] = result
            row["parameters"] = values
            t = time.time()
            row["delierium"] = delierium_properties(algebra)
            row["delierium_time"] = round(time.time() - t, 3)
        rows[i] = row
    print(f"delierium: {len(cases)} of {len(complete)} in {time.time() - t0:.0f} s", flush=True)

    t0 = time.time()
    out = subprocess.run(
        ["gap", "-q", "-o", "4g"], input=gap_script(cases), capture_output=True, text=True,
        check=False,
    )
    gap = parse_gap(out.stdout)
    print(f"GAP: {len(gap)} of {len(cases)} in {time.time() - t0:.0f} s", flush=True)
    if len(gap) < len(cases):
        failed = sorted(set(cases) - set(gap))
        print("GAP failed on", [CATALOG[i].name[:40] for i in failed[:5]])
        first = out.stdout.find(f"S {failed[0]}\n")
        print(out.stdout[first:first + 1500])

    keys = ["derived", "lower_central", "solvable", "nilpotent", "abelian", "center",
            "killing_rank"]
    counts = {}
    with open(args.out, "w") as f:
        for i, row in rows.items():
            if i in gap:
                row["gap"] = gap[i]
                d = row["delierium"]
                differ = [k for k in keys if d[k] != gap[i][k]]
                # semisimple: Killing form nondegenerate <=> radical 0
                if d["semisimple"] != (gap[i]["radical_dimension"] == 0 and row["dimension"] > 0):
                    differ.append("semisimple")
                row["status"] = "agree" if not differ else "differ: " + ", ".join(differ)
            elif "status" not in row:
                row["status"] = "GAP failed"
            counts[row["status"]] = counts.get(row["status"], 0) + 1
            f.write(json.dumps(row, default=str) + "\n")
            if row["status"].startswith("differ"):
                print(row["name"], "|", row["status"], "|", row["delierium"], "|", row["gap"])
    print(json.dumps(counts, indent=1))
    types = {}
    for row in rows.values():
        if "gap" in row:
            g = row["gap"]
            key = (g["semisimple_type"] or "-", g["radical_dimension"])
            types[key] = types.get(key, 0) + 1
    print("Levi type, radical dimension: count")
    for (s, rad), n in sorted(types.items(), key=lambda kv: -kv[1]):
        print(f"  {s:12} {rad:3}  {n}")


if __name__ == "__main__":
    main()
