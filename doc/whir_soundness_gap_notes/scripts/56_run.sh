#!/bin/sh
# Researcher 56. Rebuilds and reruns everything quoted in 56-witt-real-field.md; output on stdout
# (56_results.txt is this output). About 8 minutes on four cores, 2.5 GB for each 56_acc32 run.
# usage: 56_run.sh [builddir]      (default: a fresh directory under ${TMPDIR:-/tmp})
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
B=${1:-$(mktemp -d "${TMPDIR:-/tmp}/56_build.XXXXXX")}
mkdir -p "$B"
for p in 56_acc32 56_dual 56_struct; do cc -O2 -mcpu=native -o "$B/$p" "$HERE/$p.c" -lm; done
python3 "$HERE/13_irred.py" 8 64 > "$B/irred.txt"
tail_of() { awk -v m="$1" '$1 == m { print $2 }' "$B/irred.txt"; }

# long jobs in the background, at most four at a time
( for N in 25 26; do "$B/56_struct" $N 64 0x1b > "$B/struct$N.txt"; done ) &
( for N in 27 28; do "$B/56_struct" $N 64 0x1b > "$B/struct$N.txt"; done ) &
( for N in 9 12 13; do "$B/56_struct" $N 64 0x1b > "$B/struct$N.txt"; done ) &
( for cfg in "5 0x5 0" "6 0x3 0" "7 0x3 0" "7 0x3 2" "8 0x1b 0" "9 0x11 0"; do "$B/56_acc32" 10 9 $cfg; done > "$B/acc32.txt"
  for N in 10 11; do "$B/56_dual" $N 64 0x1b 0 six; done > "$B/dual_big.txt" ) &

echo "#### 56_witt.py"
python3 "$HERE/56_witt.py" all
echo "#### 56_strata.py"
python3 "$HERE/56_strata.py"
echo "#### 56_lowlevel.py"
python3 "$HERE/56_lowlevel.py" all
wait
echo "#### 56_acc32 10 9 m r seed  (n = 32, all 10-subsets)"
cat "$B/acc32.txt"
echo "#### 56_dual N m r 0  (power shape; six-point and eight-point words against the field degree)"
for m in 9 10 11 12 14 16 18 20 22 24 26 28 30 32 36 64; do "$B/56_dual" 8 $m "$(tail_of $m)" 0; done
for m in 10 12 16 20 24 28 40 64; do "$B/56_dual" 9 $m "$(tail_of $m)" 0; done
echo "#### 56_dual N 64 0x1b 0 six  (N = 10, 11: exhaustive count of the six-point words in GF(2^64))"
cat "$B/dual_big.txt"
echo "#### 56_dual 8 64 0x1b seed six  (random bases: no structural word)"
for s in 3 4 5; do "$B/56_dual" 8 64 0x1b $s six; done
echo "#### 56_struct N 64 0x1b  (structural six-point words of the power shape)"
for N in 9 12 13 25 26 27 28; do cat "$B/struct$N.txt"; done
echo "#### 56_family.py 25 words verify"
python3 "$HERE/56_family.py" 25 "$B/struct25.txt" verify
echo "#### 56_verify.py  (deg(Z_A - Z_B) = 0 for the pairs of the structural words, at the real sizes)"
python3 "$HERE/56_verify.py" 25 "$B/struct25.txt" 26 "$B/struct26.txt" 27 "$B/struct27.txt" 28 "$B/struct28.txt"
