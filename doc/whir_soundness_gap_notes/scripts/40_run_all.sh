#!/bin/sh
# Regenerates scripts/40_results.txt (about 6 minutes on 4 cores). Run from the scripts directory.
set -e
T=${TMPDIR:-/tmp}/run40.$$
mkdir -p "$T"
cc -O2 -o "$T/scale" 40_scale.c
cc -O2 -o "$T/list" 40_list.c
S="$T/scale"
# group 1: window tables
( python3 40_checks.py; python3 40_window.py 1 2 3 ) > "$T/g1.txt" 2>&1 &
# group 2: the family, random words, verification
( for N in 5 6 7 8 9; do "$S" $N $((3 * (1 << N) / 4 - 1)) 1 "$T/E$N.txt"; done
  for N in 5 6 7 8; do "$S" $N r 1 "$T/R$N.txt"; done
  "$S" 7 95 5; "$S" 7 95 9; "$S" 8 191 7; "$S" -7 95 9
  "$S" 7 sweep
  for N in 5 6 7; do python3 40_bezout.py "$T/E$N.txt"; done
  python3 40_bezout.py "$T/R5.txt"
  J=3 "$S" 4 r 1 "$T/J4.txt"; python3 40_bezout.py "$T/J4.txt"
  J=3 "$S" 5 r 1 "$T/J5.txt"; python3 40_bezout.py "$T/J5.txt" ) > "$T/g2.txt" 2>&1 &
# group 3: scans, first solution and whole solution space
( for N in 5 6; do "$S" $N full | tail -1; "$S" $N bin | tail -1; "$S" $N tri | tail -1; "$S" $N inv | tail -1; done
  for N in 5 6 7; do "$S" $N lin; done
  for N in 5 6; do FULL=1 "$S" $N bin | tail -2; FULL=1 "$S" $N tri | tail -2; FULL=1 "$S" $N lin | tail -2; FULL=1 "$S" $N inv | tail -2; done ) > "$T/g3.txt" 2>&1 &
# group 4: the list of X^23 at n = 32, and the Python cross-check of the search
( "$S" 5 23 1 "$T/L5.txt" > /dev/null; "$T/list" "$T/L5.txt" 18 20000000; python3 40_search.py 5 ) > "$T/g4.txt" 2>&1 &
wait
{ echo "### 40_checks.py and 40_window.py"; cat "$T/g1.txt"
  echo; echo "### 40_scale: the family, random words, 40_bezout.py"; cat "$T/g2.txt"
  echo; echo "### 40_scale: scans"; cat "$T/g3.txt"
  echo; echo "### 40_list and 40_search.py"; cat "$T/g4.txt"; } > 40_results.txt
rm -rf "$T"
