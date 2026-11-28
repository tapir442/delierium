#!/bin/bash
# Full refresh of BENCHMARK.md on the 971-entry catalogue, delierium main 6b2eaf8 (2.7.2 + #121),
# restarted 2026-11-28; <= 3 processes, nice 19.
cd /home/tapir/research-disk/delierium
D=benchmarks/tool-comparison
export WOLFRAMSCRIPT_KERNELPATH=/opt/Wolfram/WolframKernel LC_ALL=C
stage() { echo "STAGE $1 $(date +%H:%M:%S)" >> $D/stages-refresh.log; }
N="nice -n 19"
sed "s/stages.log/stages-refresh.log/" $D/pipeline.sh | grep -v "^stage done" > $D/.pipeline-refresh.sh
bash $D/.pipeline-refresh.sh
sed "s/stages3.log/stages-refresh.log/" $D/extras-update.sh | grep -v "^stage done" > $D/.extras-refresh.sh
bash $D/.extras-refresh.sh
rm -f $D/.pipeline-refresh.sh $D/.extras-refresh.sh
stage solver; $N uv run --quiet python $D/solver_catalog.py $D/solver.jsonl > $D/solver.log 2>&1
stage integrate
n=$(uv run --quiet python -c "import sys; sys.path.insert(0, 'tests'); from symmetry_catalog import CATALOG; print(sum(e.kind == 'ode' and bool(e.generators) for e in CATALOG))")
seq 0 $((n - 1)) | xargs -P 3 -I{} sh -c "$N timeout 300 uv run --quiet python benchmarks/integrate_catalog.py {} || echo '{\"i\": {}, \"status\": \"timeout\"}'" > $D/integrate.jsonl 2> $D/integrate.log
stage done
