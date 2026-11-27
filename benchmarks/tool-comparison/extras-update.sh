#!/bin/bash
# sympy-extras master @ fbca643a (fixes of #71, #72), 2026-11-27; <= 3 processes, nice 19.
cd /home/tapir/research-disk/delierium
D=benchmarks/tool-comparison
export LC_ALL=C
G="sympy-extras @ git+https://github.com/Upabjojr/sympy-extras@fbca643a"
N="nice -n 19"
stage() { echo "STAGE $1 $(date +%H:%M:%S)" >> $D/stages3.log; }
stage extras-catalog; $N uv run --quiet --with "$G" python benchmarks/sympy_symmetries.py run --out $D/extras-catalog.jsonl --jobs 3 --timeout 60 --suites catalog --tools extras,extras_gens > $D/extras-catalog.log 2>&1
stage merge; python3 - <<'PY'
import json
D = "benchmarks/tool-comparison/"
old = [json.loads(l) for l in open(D + "sympy-catalog.jsonl")]
new = [json.loads(l) for l in open(D + "extras-catalog.jsonl") if json.loads(l).get("tool")]
keep = [r for r in old if r.get("tool") not in ("extras", "extras_gens")]
with open(D + "sympy-catalog.jsonl", "w") as fh:
    fh.writelines(json.dumps(r) + "\n" for r in keep + new)
PY
stage extras-kamke; $N uv run --quiet --with "$G" python benchmarks/sympy_symmetries.py run --out $D/extras-kamke.jsonl --jobs 3 --timeout 60 --suites kamke --tools extras,cross_extras > $D/extras-kamke.log 2>&1
stage extras-detail; $N uv run --quiet --with "$G" python $D/extras_detail.py > $D/extras-detail.log 2>&1
stage done
