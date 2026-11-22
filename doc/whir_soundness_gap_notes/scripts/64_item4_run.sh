#!/bin/sh
# Note 64, item 4: build and run the greedy free-configuration search over all toy configurations.
# Usage: sh 64_item4_run.sh BUILD_DIR   (the binary goes to BUILD_DIR, the summary to stdout)
set -e
here=$(dirname "$0"); bin="$1/64_item4_free"
cc -O2 -o "$bin" "$here/64_item4_free.c"
for m in 8 16; do for cfg in "5 16" "5 8" "6 32" "6 16"; do for t in 3 4 5; do
  set -- $cfg
  r=2000; [ "$t" = 4 ] && r=1000; [ "$t" = 5 ] && r=400
  "$bin" $m $1 $2 $t $r 7 | tail -4 | grep -v '^final' | tail -2
done; done; done
