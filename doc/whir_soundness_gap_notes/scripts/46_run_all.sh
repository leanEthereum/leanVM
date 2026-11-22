#!/bin/sh
# Referee 46: every run quoted in 46-referee-notes-37-39.md. Builds into a scratch directory (argument 1,
# default a fresh mktemp directory) and leaves nothing in the repository. Four threads, about 15 minutes in all;
# the three long runs are 46_rm at n = 64 (2 minutes each), 46_pade16 (45 s each) and "prim 600" (2 minutes).
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"
S="${1:-$(mktemp -d)}"
mkdir -p "$S"
for p in 46_tops 46_rm 46_triples 46_pade16; do cc -O2 -Wno-unused-function -o "$S/$p" "$HERE/$p.c" -lpthread; done
cc -O2 -Wno-unused-function -o "$S/46_family" "$HERE/46_family.c"
cc -O2 -o "$S/46_perturb" "$HERE/46_perturb.c" -lm
cd "$S"
echo "== arithmetic =="; python3 "$HERE/46_numbers.py"
echo "== n = 32, exhaustive over all 19-subsets, three domains =="
./46_tops 5 1 17 19 xlw 16 2 dump tops32_s1.txt
./46_tops 5 7 17 19 xlw 16 2 dump tops32_s7.txt
./46_tops 5 0 17 19 xlw 16 2 dump tops32_real.txt
cmp tops32_s1.txt tops32_s7.txt && cmp tops32_s1.txt tops32_real.txt && echo "three domains: same list"
echo "== the claimed family, generated and verified in GF(2^64) =="
./46_family 5 1 dump fam32.txt; cmp fam32.txt tops32_s1.txt && echo "n = 32: family == exhaustive list"
./46_family 6 1 dump fam64.txt
./46_family 7 1
echo "== n = 64, exhaustive by power sums =="
./46_rm 5 1 17 19 xlw 16 2 dump rm32.txt; cmp rm32.txt tops32_s1.txt && echo "n = 32: power-sum method == subset enumeration"
./46_rm 6 1 33 38 xlw 32 3 dump rm64.txt; cmp rm64.txt fam64.txt && echo "n = 64 seed 1: exhaustive list == family"
./46_rm 6 2 33 38 xlw 32 3 dump rm64_s2.txt; cmp rm64_s2.txt fam64.txt && echo "n = 64 seed 2: exhaustive list == family"
./46_rm 6 0 33 38 xlw 32 3 dump rm64_real.txt maxe 2; cmp rm64_real.txt fam64.txt && echo "n = 64 real shape, case A only: list == family"
echo "== Theorem S and its sharpness at n = 32 =="
for a in "5 1 12 13 pow 15" "5 0 12 13 pow 15" "5 1 10 11 pow 15" "5 1 10 12 pow 15" "5 0 10 12 pow 15" "5 1 8 9 pow 15" "5 1 15 17 xlw 16 2" "5 1 13 16 xlw 16 2" "5 1 14 16 xlw 16 2"; do echo "# 46_tops $a"; ./46_tops $a; done
echo "== Theorem 2.3 at n = 16 =="
./46_pade16 1; ./46_pade16 0
echo "== triples: periods, primitive sublists, descent, transfer, perturbation =="
./46_triples 5 1 tops32_s1.txt pairs 300
./46_triples 5 1 tops32_s1.txt bmin
./46_triples 5 1 tops32_s1.txt prim 600
./46_triples 5 1 tops32_s1.txt descent
./46_triples 5 1 tops32_s1.txt transfer 3000
./46_triples 5 1 tops32_s1.txt classes cls32.txt; ./46_triples 5 1 cls32.txt prim 40
./46_tops 5 1 8 15 pow 15 dump flats32.txt; ./46_triples 5 1 flats32.txt descent pow 15 8
./46_tops 5 1 12 13 pow 15 dump pow15k12.txt; ./46_triples 5 1 pow15k12.txt descent pow 15 12
./46_tops 5 1 16 18 xlw 16 1 dump l32_16_18.txt; ./46_triples 5 1 l32_16_18.txt prim 16
./46_triples 6 1 fam64.txt pairs 12
./46_triples 6 1 fam64.txt prim 8
./46_triples 6 1 fam64.txt descent
./46_triples 6 1 fam64.txt descent b
./46_triples 6 1 fam64.txt transfer 3000
./46_triples 6 1 fam64.txt classes cls64.txt; ./46_triples 6 1 cls64.txt prim 40
./46_triples 6 1 fam64.txt perturb 0.125
./46_triples 6 1 fam64.txt perturb 0.03
./46_perturb 12 0.1 400 1; ./46_perturb 14 0.1 400 1; ./46_perturb 16 0.02 200 1
echo "scratch directory: $S"
