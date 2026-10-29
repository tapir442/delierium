#!/bin/bash
# Rerun of all tool comparisons against delierium 2.7.0, 2026-10-28; <= 3 processes, nice 19.
cd /home/tapir/research-disk/delierium
D=benchmarks/tool-comparison
export WOLFRAMSCRIPT_KERNELPATH=/opt/Wolfram/WolframKernel LC_ALL=C
stage() { echo "STAGE $1 $(date +%H:%M:%S)" >> $D/stages.log; }
N="nice -n 19"
stage sympy-catalog; $N uv run --quiet --with sympy-extras==0.0.2 python benchmarks/sympy_symmetries.py run --out $D/sympy-catalog.jsonl --jobs 3 --timeout 60 --suites catalog > $D/sympy-catalog.log 2>&1
stage deli-kamke; $N uv run --quiet --with sympy-extras==0.0.2 python benchmarks/sympy_symmetries.py run --out $D/deli-kamke.jsonl --jobs 3 --timeout 60 --suites kamke --tools deli_det,deli_janet,cross_deli,cross_extras > $D/deli-kamke.log 2>&1
stage blad; $N env PYTHONPATH=. uv run --quiet --with DifferentialAlgebra python benchmarks/blad_crosscheck.py --workers 3 --timeout 300 --out $D/blad > $D/blad.log 2>&1
stage symmgrp; $N uv run --quiet python benchmarks/symmgrp_symmetries.py --timeout 120 --out $D/symmgrp.jsonl > $D/symmgrp.log 2>&1
for t in reduce relie dimsym spde; do
  stage $t-run; $N uv run --quiet python benchmarks/${t}_symmetries.py run --jobs 2 --timeout 120 --raw $D/$t-raw.jsonl > $D/$t-run.log 2>&1
  stage $t-compare; $N uv run --quiet python benchmarks/reduce_symmetries.py compare $D/$t-raw.jsonl --jobs 3 --timeout 120 --memory 6 --out $D/$t.jsonl > $D/$t-compare.log 2>&1
done
stage mathlie-run; $N uv run --quiet python benchmarks/mathlie_symmetries.py run --isolated --jobs 2 --timeout 120 --memory 8 --output $D/mathlie.jsonl > $D/mathlie-run.log 2>&1
stage mathlie-compare; $N uv run --quiet python benchmarks/mathlie_symmetries.py compare $D/mathlie.jsonl --jobs 3 --timeout 120 --out $D/mathlie-compare.jsonl > $D/mathlie-compare.log 2>&1
stage gap; $N uv run --quiet python benchmarks/gap_lie_algebra.py --out $D/gap.jsonl > $D/gap.log 2>&1
stage cocoa; $N uv run --quiet python benchmarks/cocoa_janet.py --out $D/cocoa.jsonl > $D/cocoa.log 2>&1
stage weyl; $N uv run --quiet python benchmarks/weyl_janet.py --n 200 --out $D/weyl.jsonl > $D/weyl.log 2>&1
stage done
