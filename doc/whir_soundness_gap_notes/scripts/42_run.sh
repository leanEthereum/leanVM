#!/bin/sh
# Note 42: reproduces 42_results.txt on standard output. Needs python3 and cc; builds in a temporary
# directory; four processes, about 25 minutes (the 5-lateral samples at p = 499 and the later levels of
# Theorem B are the long parts).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
cc -O2 -o "$tmp/toy" "$here/42_toy.c"
cc -O2 -o "$tmp/lateral" "$here/42_lateral.c"

( python3 "$here/42_theoremB.py" level0 > "$tmp/b0.txt"; python3 "$here/42_theoremB.py" listsize >> "$tmp/b0.txt" ) &
python3 "$here/42_theoremB.py" later > "$tmp/b1.txt" &
python3 "$here/42_multiparent.py" > "$tmp/mp.txt" &
(
  "$tmp/toy" 13 6 2 > "$tmp/t1.txt"
  "$tmp/toy" 17 6 2 > "$tmp/t2.txt"
  "$tmp/toy" 11 7 2 > "$tmp/t3.txt"
  "$tmp/toy" 11 6 3 > "$tmp/t4.txt"
  "$tmp/toy" 11 6 2 lists > "$tmp/t5.txt"
  python3 "$here/42_toy_check.py" "$tmp/t1.txt" "$tmp/t2.txt" "$tmp/t3.txt" "$tmp/t4.txt" "$tmp/t5.txt" > "$tmp/toy.txt"
  python3 "$here/42_coset_rank.py" > "$tmp/rank.txt"
  python3 "$here/42_lemmas_check.py" > "$tmp/lem.txt"
  python3 "$here/42_lemmaM_t4.py" >> "$tmp/lem.txt"
  {
    "$tmp/lateral" 53 20000 7
    "$tmp/lateral" 101 60000 23
    "$tmp/lateral" 211 200000 8
    "$tmp/lateral" 499 300000 9
    "$tmp/lateral" 499 500000 21
    "$tmp/lateral" 499 500000 22
  } > "$tmp/lat.txt"
) &
wait

echo "#### 42_theoremB.py level0, then listsize"
cat "$tmp/b0.txt"
echo
echo "#### 42_theoremB.py later"
cat "$tmp/b1.txt"
echo
echo "#### 42_lateral (complete 5-laterals, honest lists)"
cat "$tmp/lat.txt"
echo
echo "#### 42_toy and 42_toy_check.py (all patterns of three members)"
cat "$tmp/toy.txt"
echo
echo "#### 42_coset_rank.py"
cat "$tmp/rank.txt"
echo
echo "#### 42_lemmas_check.py and 42_lemmaM_t4.py"
cat "$tmp/lem.txt"
echo
echo "#### 42_multiparent.py"
cat "$tmp/mp.txt"
rm -rf "$tmp"
