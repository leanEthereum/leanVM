#!/bin/sh
# Researcher 18. Phantom-degree profiles at n = 16: for each "k T" runs 18_exhaust restricted to words that are
# polynomials of degree <= T + r modulo codewords, r = 0, 1, ..., and stops at the first run over the time limit
# (r = 16 - T - 1 is all words). Files <out dir>/d16/p_<dom>_<k>_<T>_r<r>.txt, read by 18_table16.py.
# usage: 18_profile16.sh <bin dir> <out dir> <dom> <seed> <seconds per run> "k T" ["k T" ...]
BIN=$1; OUT=$2; DOM=$3; SEED=$4; LIM=$5; shift 5
mkdir -p "$OUT/d16"
for kt in "$@"; do
  set -- $kt; k=$1; T=$2; r=0
  while [ $r -le $((16 - T - 1)) ]; do
    f="$OUT/d16/p_${DOM}_${k}_${T}_r$r.txt"
    if ! grep -q RESULT "$f" 2>/dev/null; then
      "$BIN/ex" $k $T $DOM $SEED 4 1 $r > "$f" 2>/dev/null &
      pid=$!
      ( sleep $LIM; kill $pid 2>/dev/null ) &
      wd=$!
      wait $pid 2>/dev/null
      kill $wd 2>/dev/null
    fi
    if grep -q RESULT "$f"; then echo "r=$r: $(grep RESULT "$f")"; else echo "k=$k T=$T r=$r: not finished in ${LIM}s"; break; fi
    r=$((r + 1))
  done
done
