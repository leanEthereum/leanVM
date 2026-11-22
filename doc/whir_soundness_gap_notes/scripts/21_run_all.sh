#!/bin/bash
# Researcher 21 (referee). Rebuilds and reruns every check of note 21 into 21_results.txt.
# Usage: 21_run_all.sh [builddir]   (default: a fresh directory under ${TMPDIR:-/tmp}). At most three processes at a time.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
B="${1:-$(mktemp -d "${TMPDIR:-/tmp}/ref21.XXXXXX")}"
mkdir -p "$B"
export PYTHONDONTWRITEBYTECODE=1
cc -O2 -o "$B/21_walsh" "$here/21_walsh.c" || exit 1
cc -O2 -o "$B/21_multiset16" "$here/21_multiset16.c" || exit 1
cc -O2 -o "$B/21_dual32" "$here/21_dual32.c" || exit 1
cd "$here"

stream_a() {
  echo "== 21_gf.py"; python3 21_gf.py
  echo "== 21_attack_checks.py flats"; python3 21_attack_checks.py flats
  echo "== 21_attack_checks.py thmw"; python3 21_attack_checks.py thmw
  echo "== 21_attack_checks.py five8 7"; python3 21_attack_checks.py five8 7
  echo "== 21_attack_checks.py mitm"; python3 21_attack_checks.py mitm
  echo "== 21_attack_checks.py extra"; python3 21_attack_checks.py extra
  echo "== 21_real_checks.py padding padfield pair sparse curve consts"
  for w in padding padfield pair sparse curve consts; do python3 21_real_checks.py $w; done
  echo "== 21_real_checks.py phantom"; python3 21_real_checks.py phantom
}
stream_b() {
  echo "== 21_walsh classes32 (all s-subsets of F_2^5; s <-> 32 - s by complement)"
  for s in 3 4 5 6 7 8 9 10 11 12 13 14 15 16; do "$B/21_walsh" classes32 $s 4; done
  for s in 3 4 5 6 7 8 9 10 11 12 13 14 15 16; do "$B/21_walsh" classes32 $s 8; done
  for s in 4 8 12 16; do "$B/21_walsh" classes32 $s 16; done
  echo "== 21_walsh rm2 (classes of seeds at n = 32, 64, 128)"
  "$B/21_walsh" rm2 5 4 cosets:2:0,1,2 2
  "$B/21_walsh" rm2 6 8 cosets:3:0,1,2 3
  "$B/21_walsh" rm2 7 16 cosets:4:0,1,2 4
  "$B/21_walsh" rm2 5 4 cosets:2:0,1,2+31 2
  "$B/21_walsh" rm2 6 8 cosets:3:0,1,2+63 3
  "$B/21_walsh" rm2 7 16 cosets:4:0,1,2+127 4
  "$B/21_walsh" rm2 5 4 cosets:1:0,1,2,3,4,5,6 1 "$B/c7_32.txt"
  "$B/21_walsh" rm2 6 8 cosets:2:0,1,2,3,4,5,6 2 "$B/c7_64.txt"
  "$B/21_walsh" rm2 7 16 cosets:3:0,1,2,3,4,5,6 3 "$B/c7_128.txt"
  echo "== 21_nine16_checks.py"; python3 21_nine16_checks.py "$B/c7_32.txt" "$B/c7_64.txt" "$B/c7_128.txt"
  echo "== 21_multiset16"
  "$B/21_multiset16" 8 10 13; "$B/21_multiset16" 8 11 17; "$B/21_multiset16" 8 12 16; "$B/21_multiset16" 2 4 9; "$B/21_multiset16" 2 5 11
  "$B/21_multiset16" 9 11 14; "$B/21_multiset16" 9 12 15
}
stream_c() {
  echo "== 21_dual32 m r seed s g ntargets"
  for f in "5 0x5 0" "5 0x5 3" "6 0x3 1" "6 0x3 5" "7 0x3 2" "8 0x1b 2" "8 0x1b 0" "12 0x53 4"; do
    for sg in "6 4" "6 5" "7 4" "7 5" "7 6" "8 4" "8 6" "9 5" "9 6" "10 4" "10 6" "11 4" "11 5" "11 6" "11 7"; do
      "$B/21_dual32" $f $sg 3
    done
  done
  for f in "6 0x3 7" "8 0x1b 9" "7 0x3 11"; do
    for sg in "12 4" "12 6" "13 5" "13 6" "10 5" "10 7"; do
      "$B/21_dual32" $f $sg 2
    done
  done
}
stream_a > "$B/out_a.txt" 2>&1 &
stream_b > "$B/out_b.txt" 2>&1 &
stream_c > "$B/out_c.txt" 2>&1 &
wait
cat "$B/out_a.txt" "$B/out_b.txt" "$B/out_c.txt" > "$here/21_results.txt"
echo "wrote $here/21_results.txt"
