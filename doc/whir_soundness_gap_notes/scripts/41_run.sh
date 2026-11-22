#!/bin/sh
# Referee 41: all numerical runs behind 41-referee-note-35.md. About 4 minutes on one core
# (2 of them for the exhaustive 5n/8 list at n = 32, 40 s for 41_counts.py). Output: 41_results.txt next to this script.
# usage: sh 41_run.sh [build-dir]     (the binary goes to build-dir, default: a fresh temporary directory)
set -e
here=$(cd "$(dirname "$0")" && pwd)
bld=${1:-$(mktemp -d)}
cc -O2 -o "$bld/41_theory" "$here/41_theory.c"
T="$bld/41_theory"
f() { grep -v '^local rank at point [12]\|^   orders'; }
{
echo "===== 41_counts.py"
python3 "$here/41_counts.py"
echo
echo "===== flat word alpha^(n/2-1), rate 1/4 (Proposition 5, Theorem 4, Lemma C local ranks)"
for N in 4 5 6; do n=$((1 << N)); k=$((n / 4))
  for dom in 0 1; do
    if [ $N = 4 ]; then mB="5 2"; else mB="6 2"; fi
    set -- $mB
    "$T" $N $dom $((10 + N)) flat $((k - 1)) $((n / 2 - 1)) $1 $2 1 | f; echo
  done
done
echo "===== flat word: the whole list down to agreement 3n/8 - 1 (and 10 at n = 32), three domains"
for dom in 0 1 3; do "$T" 4 $dom 2 flat 3 5 0 0; "$T" 5 $dom 2 flat 7 11 0 0; done
"$T" 5 3 2 flat 7 10 0 0
echo
echo "===== slack 1: word alpha^(n/2), degree <= n/4, agreement n/2 (exactly the Johnson boundary)"
for N in 4 5 6; do n=$((1 << N)); "$T" $N 1 $((40 + N)) flat1 $((n / 4)) $((n / 2)) 7 2 1 | f; echo; done
"$T" 4 0 1 flat1 4 6 0 0; "$T" 5 0 1 flat1 8 12 0 0
echo
echo "===== Sidon tangent lines (Delta = 1); n = 64, A = 8 is at the Johnson boundary A^2 = n Delta"
"$T" 4 0 11 sidon 1 5 2 1 1 | f; echo
"$T" 5 0 17 sidon 1 6 3 1 1 | f; echo
"$T" 6 0 22 sidon 1 8 4 2 1 | f; echo
echo "===== random and planted words, arbitrary evaluation sets"
"$T" 4 0 7 rand 3 7 5 2 1 | f; echo
"$T" 4 2 7 plant2 3 7 5 2 1 | f; echo
"$T" 5 0 16 rand 7 15 6 2 1 | f; echo
"$T" 5 2 15 plant2 7 15 6 2 1 | f; echo
"$T" 5 0 25 plant2 7 15 6 2 1 | f; echo
"$T" 5 1 19 plant3 3 10 4 2 1 | f; echo
"$T" 6 2 9 plant4 3 14 4 2 1 | f; echo
echo "===== rate 1/2"
"$T" 4 2 9 code:5 7 11 4 1 1 | f; echo
"$T" 4 0 9 pad:8:3 7 11 4 1 1 | f; echo
"$T" 5 2 18 code:10 15 22 8 2 1 | f; echo
"$T" 5 0 9 pad:16:6 15 22 8 2 1 | f; echo
echo "===== Wronskians of two random explainers: first integrals with contact 2m on every line"
w() { grep '^n = \|Wronskian\|jet coordinates\|at a random tau'; }
for args in "4 0 7 rand 3 7 5 2" "4 2 71 rand 3 7 5 2" "4 1 72 rand 3 8 2 1" "5 0 16 rand 7 15 6 2" "5 2 73 rand 7 16 3 1" \
            "4 2 74 rand 7 11 4 1" "5 2 18 code:10 15 22 8 2" "5 0 75 rand 15 22 8 2" "5 2 15 plant2 7 15 6 2" "4 0 3 flat 3 7 5 2" "5 0 17 sidon 1 6 3 1"; do
  "$T" $args 2 | w; echo
done
echo "===== below a_1: no explainer in the supports tried (the theory is silent), lists recounted"
for mB in "4 2" "6 3" "8 4" "10 4"; do set -- $mB; "$T" 4 0 1 five8 8 10 $1 $2 1 | grep 'monomials\|^list\|explainer space'; done
for mB in "4 1" "6 2" "8 3" "10 4"; do set -- $mB; "$T" 4 0 9 pad:8:3 7 10 $1 $2 1 | grep 'monomials\|^list\|explainer space'; done
"$T" 5 0 33 five8 16 20 0 0
} > "$here/41_results.txt" 2>&1
echo "wrote $here/41_results.txt"
