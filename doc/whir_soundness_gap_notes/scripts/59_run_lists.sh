#!/bin/sh
# 59_run_lists.sh: builds 59_lists.c and writes 59_lists_output.txt (about three minutes on four cores).
cd "$(dirname "$0")"
BIN=${TMPDIR:-/tmp}/59_lists_bin
cc -O2 -o "$BIN" 59_lists.c
OUT=59_lists_output.txt
python3 59_predict.py 16 > $OUT
for k in 6 8; do
  if [ $k = 6 ]; then T=11; else T=12; fi
  for s in 1 2 3 4 5 6 7 8; do
    "$BIN" mix $k $s $T > .59_mix_${k}_$s.tmp &
    "$BIN" rand $k $s $T > .59_rand_${k}_$s.tmp &
    if [ $((s % 2)) = 0 ]; then wait; fi
  done
  wait
  for s in 1 2 3 4 5 6 7 8; do cat .59_mix_${k}_$s.tmp >> $OUT; done
  for s in 1 2 3 4 5 6 7 8; do cat .59_rand_${k}_$s.tmp >> $OUT; done
  rm -f .59_mix_${k}_*.tmp .59_rand_${k}_*.tmp
done
"$BIN" rs 6 0 10 >> $OUT
"$BIN" rs 6 0 11 >> $OUT
"$BIN" rs 8 0 12 >> $OUT
