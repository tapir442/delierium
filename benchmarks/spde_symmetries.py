"""Fritz Schwarz's SPDE (REDUCE package, 1980s) on the symmetry catalogue.

Internal benchmark. SPDE comes with REDUCE (load_package spde). Same two
phases and comparison as reduce_symmetries.py (LIEPDE); the input notation
is DIMSYM's (dimsym_symmetries.translate, derivative indices ascending), the
equations are given as they are with the derivative to solve for (sder).
simpsys() keeps its result internally; spdeinf, spdecond read it out.

    uv run python benchmarks/spde_symmetries.py run [--only TEXT] [--jobs 2]
    uv run python benchmarks/spde_symmetries.py compare benchmarks/spde-raw.jsonl
"""

import reduce_symmetries as rs
from dimsym_symmetries import translate

HELPERS = [
    "symbolic procedure spdeinf k; prepsq nth(cadr uhf, k) $",
    "symbolic operator spdeinf $",
    "symbolic procedure spdencond(); length car uhf $",
    "symbolic operator spdencond $",
    "symbolic procedure spdecond k; prepf nth(car uhf, k) $",
    "symbolic operator spdecond $",
    "symbolic procedure spdeall(); 'list . append("
    "for each y in cadr uhf collect prepsq y, for each y in car uhf collect prepf y) $",
    "symbolic operator spdeall $",
]


def to_spde(entry):
    """SPDE input for entry and the names to map back."""
    names, depends, equations = translate(entry, descending=False)
    n, m = len(entry.independent), len(entry.dependent)
    lines = ["off nat $", "linelength 100000 $", "load_package spde $", *HELPERS]
    for name in depends:
        lines.append(f"operator {name} $")
    for k, (lead, e, _) in enumerate(equations, 1):
        lines += [f"deq {k} := {e} $", f"sder {k} := {lead} $"]
    lines += [
        f"cresys({', '.join(f'deq {k}' for k in range(1, len(equations) + 1))}) $",
        "simpsys() $",
        'write "CASE";',
        'for i:=1:spdencond() do write "COND ", spdecond(i);',
    ]
    keys = [f"xi_x{j}" for j in range(1, n + 1)] + [f"eta_u{i}" for i in range(1, m + 1)]
    lines += [f'write "SOL {key} := ", spdeinf({k});' for k, key in enumerate(keys, 1)]
    total = "spdeall()"  # infinitesimals and remaining conditions

    def checks(f):
        return ", ".join([f'" ", df({f}, x({j}))' for j in range(1, n + 1)]
                         + [f'" ", df({f}, u({i}))' for i in range(1, m + 1)])

    lines.append(f"for k:=1:1000 do if not freeof({total}, c(k)) then "
                 f'write "CONST c_", k, {checks("c(k)")};')
    # an infinitesimal SPDE left undetermined is an unknown itself
    for j in range(1, n + 1):
        lines.append(f'if not freeof({total}, xi({j})) then write "CONST xi_{j}", '
                     f"{checks(f'xi({j})')};")
    for i in range(1, m + 1):
        lines.append(f'if not freeof({total}, eta({i})) then write "CONST eta_{i}", '
                     f"{checks(f'eta({i})')};")
    lines.append("end;")
    return "\n".join(lines) + "\n", names


if __name__ == "__main__":
    rs.main(convert=to_spde, name="spde")
