#!/bin/bash
# 53_run.sh: all computations of 53-goppa-structure-degenerate.md. Binaries and dumps go to a build directory
# outside the repository (first argument, default /tmp/r53). About 4 minutes on one core.
#   bash 53_run.sh [builddir] > 53_results.txt
set -e
B=${1:-/tmp/r53}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$B"
cc -O2 -o "$B/53_codes" "$here/53_codes.c"
cc -O2 -o "$B/53_gap" "$here/53_gap.c"
cd "$here"
echo "===== 53_flat.py"
python3 53_flat.py
echo "===== 53_planted.py"
python3 53_planted.py
echo "===== 53_families.py"
python3 53_families.py
echo "===== 53_tight.py"
python3 53_tight.py
echo "===== 53_window.py"
python3 53_window.py
echo "===== 53_strata.py"
python3 53_strata.py "$B/53_codes" big
echo "===== 53_gap: weight gap of RM(2, N) on small-field domains, D = span(1, x, .., x^(N-1)), g = 0.2065 n"
for cfg in "10 12 211" "10 16 211" "10 64 211" "12 20 845" "12 24 845" "12 32 845" "12 64 845"; do
  set -- $cfg
  "$B/53_codes" inf "$1" "$2" span 0 "$B/b_$1_$2.txt" "$3" > /dev/null
  n=$((1 << $1))
  lo=$((2 * ((7065 * n + 9999) / 10000 - n / 2)))
  hi=$((7 * n / 16))
  echo "== N=$1 m=$2 g=$3, window [$lo, $hi)"
  "$B/53_gap" "$1" "$B/b_$1_$2.txt" "$lo" "$hi" 100 1
done
