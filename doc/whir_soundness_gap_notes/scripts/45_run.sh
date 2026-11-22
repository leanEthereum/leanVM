#!/bin/sh
# 45_run.sh: regenerates scripts/45_results.txt for 45-rate-half-second-attempt.md (run inside scripts/, about 8 minutes on one core).
# Usage: sh 45_run.sh [build-dir]     (the C binary goes to build-dir, default: a temporary directory)
set -e
B=${1:-$(mktemp -d)}
OUT=45_results.txt
cc -O2 -o "$B/45_scale" 45_scale.c
cc -O2 -o "$B/45_fn_check" 45_fn_check.c
{
echo "== 45_lattice.py 4"; python3 45_lattice.py 4 all
echo "== 45_lattice.py 5"; python3 45_lattice.py 5 all
echo "== 45_family.py 4 5 6"; python3 45_family.py 4 5 6
echo "== 45_det.py 4"; python3 45_det.py 4
echo "== 45_det.py 5"; python3 45_det.py 5
echo "== 45_b2.py 4"; python3 45_b2.py 4 fam rand zero
echo "== 45_b2.py 5"; python3 45_b2.py 5 fam rand
echo "== 45_scale: X^178 at n = 256 on a random F2-subspace, on GF(256), on an F16-subspace"
"$B/45_scale" 8 178
DOM=fk8 "$B/45_scale" 8 178
DOM=fk4 "$B/45_scale" 8 178
echo "== 45_scale: X^191 at n = 256 on GF(256)"; DOM=fk8 "$B/45_scale" 8 191
echo "== 45_scale: sweep at n = 256 on GF(256)"; DOM=fk8 "$B/45_scale" 8 sweep
echo "== 45_scale: sweep at n = 64 on an F4-subspace and on a random F2-subspace"; DOM=fk2 "$B/45_scale" 6 sweep; "$B/45_scale" 6 sweep
echo "== 45_fn_check: Theorem 7 at n = 64, exhaustive at low degree"
for e in 46 44; do "$B/45_fn_check" $e 3 30; "$B/45_fn_check" $e 5 36; "$B/45_fn_check" $e 7 38; done
echo "== 45_window.py"; python3 45_window.py 1 2 3 4 5
} > $OUT 2>&1
echo "wrote $OUT"
