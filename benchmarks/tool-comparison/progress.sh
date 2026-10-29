#!/bin/bash
# progress bar of pipeline.sh: one line per stage, and per 100 entries in a compare stage
D=/home/tapir/research-disk/delierium/benchmarks/tool-comparison
ALL=(sympy-catalog deli-kamke blad symmgrp reduce-run reduce-compare relie-run relie-compare
     dimsym-run dimsym-compare spde-run spde-compare mathlie-run mathlie-compare gap cocoa weyl)
T=${#ALL[@]}; last=""
while :; do
  cur=$(tail -1 $D/stages.log | awk '{print $2}')
  k=$T
  for i in "${!ALL[@]}"; do [ "${ALL[$i]}" = "$cur" ] && k=$i; done
  sub=""; m=0
  case $cur in
    *-compare) t=${cur%-compare}; f=$D/$t.partial; [ "$t" = mathlie ] && f=$D/mathlie-compare.partial
               if [ -f "$f" ]; then m=$(wc -l < "$f"); sub=" ($m/786 entries)"; fi;;
  esac
  n=$((k * 30 / T))
  bar=$(printf '%*s' $n '' | tr ' ' '#')$(printf '%*s' $((30 - n)) '' | tr ' ' '.')
  key="$cur-$((m / 100))"
  if [ "$key" != "$last" ]; then echo "[$bar] $k/$T stages done, now: $cur$sub"; last=$key; fi
  [ "$cur" = done ] && break
  sleep 30
done
