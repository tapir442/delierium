#!/bin/bash
# after the fix of unevaluated derivatives of f(expression) (2026-10-28): the stages that use delierium on foreign equations
cd /home/tapir/research-disk/delierium
D=benchmarks/tool-comparison
export WOLFRAMSCRIPT_KERNELPATH=/opt/Wolfram/WolframKernel LC_ALL=C
stage() { echo "STAGE $1 $(date +%H:%M:%S)" >> $D/stages2.log; }
N="nice -n 19"
stage symmgrp; $N uv run --quiet python benchmarks/symmgrp_symmetries.py --timeout 120 --out $D/symmgrp.jsonl > $D/symmgrp.log 2>&1
for t in reduce relie dimsym; do
  stage $t-compare; $N uv run --quiet python benchmarks/reduce_symmetries.py compare $D/$t-raw.jsonl --jobs 3 --timeout 120 --memory 6 --out $D/$t.jsonl > $D/$t-compare.log 2>&1
done
stage spde-run; $N uv run --quiet python benchmarks/spde_symmetries.py run --jobs 2 --timeout 120 --raw $D/spde-raw.jsonl > $D/spde-run.log 2>&1
stage spde-compare; $N uv run --quiet python benchmarks/reduce_symmetries.py compare $D/spde-raw.jsonl --jobs 3 --timeout 120 --memory 6 --out $D/spde.jsonl > $D/spde-compare.log 2>&1
stage mathlie-compare; $N uv run --quiet python benchmarks/mathlie_symmetries.py compare $D/mathlie.jsonl --jobs 3 --timeout 120 --out $D/mathlie-compare.jsonl > $D/mathlie-compare.log 2>&1
stage done
