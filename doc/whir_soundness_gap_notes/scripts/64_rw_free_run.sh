#!/bin/sh
# Note 64, random windows (b): the greedy free-configuration search of 64_item4_free.c with d random partners.
# Usage: sh 64_rw_free_run.sh BUILD_DIR N    (GF(2^16), k = n/2 and n/4, t = 3, 4, 5, d = 2, 4, 6, 8, two graphs)
set -e
here=$(dirname "$0"); bin="$1/64_item4_free"; N=$2; n=$((1 << N))
cc -O2 -o "$bin" "$here/64_item4_free.c"
for k in $((n / 2)) $((n / 4)); do for d in 2 4 6 8; do for t in 3 4 5; do for g in 1 2; do
  r=600; [ "$t" = 4 ] && r=300; [ "$t" = 5 ] && r=150
  "$bin" 16 $N $k $t $r 7 $d $g | grep '^q=' | sed "s/^q=2^16 /graph $g /"
done; done; done; done
