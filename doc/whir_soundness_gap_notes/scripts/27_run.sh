#!/bin/sh
# Researcher 27. All four-member lists at n = 16 for the five parameter points of note 27, section 3.
# usage: 27_run.sh <bin dir> <out dir> [seed] [threads]
# (8, 10) is run in four parts over the rooted pairs so that no single run exceeds three minutes on four threads;
# the four histograms are concatenated into out_8_10.txt, which 27_summary.py reads like the others.
BIN=$1; OUT=$2; SEED=${3:-1}; TH=${4:-4}
mkdir -p "$OUT"
for kt in 12:13 9:11 6:9 3:7; do
  k=${kt%%:*}; T=${kt##*:}
  "$BIN/27_lists" $k $T $SEED $TH > "$OUT/out_${k}_${T}.txt"
done
: > "$OUT/out_8_10.txt"
for c in 0 1 2 3; do
  lo=$((c * 90)); hi=$((lo + 90))
  "$BIN/27_lists" 8 10 $SEED $TH 0 $lo $hi >> "$OUT/out_8_10.txt"
done
for f in 12_13 9_11 8_10 6_9 3_7; do
  echo "== $f"; python3 "$(dirname "$0")/27_summary.py" "$OUT/out_$f.txt" | tail -7
done
