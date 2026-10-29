#!/bin/bash
# after rerun.sh: SymPy's and sympy-extras' Kamke generators checked by delierium 2.7.0
cd /home/tapir/research-disk/delierium
D=benchmarks/tool-comparison
until grep -q "STAGE done" $D/stages2.log; do sleep 30; done
echo "STAGE cross-kamke $(date +%H:%M:%S)" >> $D/stages2.log
nice -n 19 uv run --quiet --with sympy-extras==0.0.2 python benchmarks/sympy_symmetries.py run --out $D/cross-kamke.jsonl --jobs 3 --timeout 60 --suites kamke --tools cross_sympy,cross_extras > $D/cross-kamke.log 2>&1
echo "STAGE cross-done $(date +%H:%M:%S)" >> $D/stages2.log
