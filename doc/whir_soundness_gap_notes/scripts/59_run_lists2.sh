#!/bin/sh
# 59_run_lists2.sh: 40 more seeds of mix and rand at k = 8, T = 13, then plain RS [16,8] at T = 11 (four parts).
cd "$(dirname "$0")"
BIN=${TMPDIR:-/tmp}/59_lists_bin
cc -O2 -o "$BIN" 59_lists.c
OUT=59_lists2_output.txt
: > $OUT
for t in mix rand; do
  s=101
  while [ $s -le 140 ]; do
    for j in 0 1 2 3; do "$BIN" $t 8 $((s + j)) 13 | grep "T=13" > .59_t_$j.tmp & done
    wait
    cat .59_t_?.tmp >> $OUT; rm -f .59_t_?.tmp
    s=$((s + 4))
  done
done
for p in 0 1 2 3; do "$BIN" rs 8 0 11 $p 4 > .59_rs_$p.tmp & done
wait
cat .59_rs_?.tmp >> $OUT; rm -f .59_rs_?.tmp
