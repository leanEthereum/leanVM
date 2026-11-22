#!/bin/sh
# usage: 02_ct32_run.sh <binary> <label> <m> <modlow_hex> <b0> <b1> <b2> <b3> <b4>
# Runs 02_ct32 for T = 2..16 (four at a time), tmax = 8, with one maximal class dumped per (T, t).
bin=$1; label=$2; m=$3; mod=$4; shift 4
echo "# $label: m=$m modlow=$mod basis=$*"
for T in 16 14 12 10 15 13 11 9 8 7 6 5 4 3 2; do echo $T; done | xargs -P 4 -I{} "$bin" "$m" "$mod" 8 1 {} "$@" | sort -t= -k2 -n
