#!/bin/sh
# Researcher 18. Sweep of the exact all-words maxima at n = 16.
# usage: 18_run16.sh <bin dir> <out dir> <dom> <seed> <seconds per case> [threads]
# Runs 18_exhaust for every (k, T), 2 <= k <= 13, k < T < 16, kills a case after the time limit (then it is reported
# as "not exhausted"), and writes one file per case plus a summary on stdout.
BIN=$1; OUT=$2; DOM=$3; SEED=$4; LIM=$5; TH=${6:-4}
mkdir -p "$OUT"
for k in 2 3 4 5 6 7 8 9 10 11 12 13; do
  T=$((k + 1))
  while [ $T -le 15 ]; do
    f="$OUT/e_${DOM}_${SEED}_${k}_${T}.txt"
    if ! grep -q RESULT "$f" 2>/dev/null; then
      "$BIN/ex" $k $T $DOM $SEED $TH > "$f" 2>/dev/null &
      pid=$!
      ( sleep $LIM; kill $pid 2>/dev/null ) &
      wd=$!
      wait $pid 2>/dev/null
      kill $wd 2>/dev/null
    fi
    if grep -q RESULT "$f"; then grep RESULT "$f"; else echo "RESULT k=$k T=$T dom=$DOM not exhausted in ${LIM}s"; fi
    T=$((T + 1))
  done
done
