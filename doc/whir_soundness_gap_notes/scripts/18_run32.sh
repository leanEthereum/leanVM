#!/bin/sh
# Researcher 18. The n = 32 runs of note 18, section 4 (generic domain, 4 threads). Each line is one run of 18_sub;
# the times in the note are wall times on an Apple M-series machine. Results go to <out dir>/<name>.txt.
# usage: 18_run32.sh <bin dir> <out dir> [group ...]     groups: half pairs eighth (default: all)
BIN=$1; OUT=$2; shift 2
mkdir -p "$OUT"
run() { name=$1; shift; "$BIN/sub" "$@" > "$OUT/$name.txt" 2>&1; echo "$name: $(grep RESULT "$OUT/$name.txt")"; }
want() { [ -z "$GROUPS_" ] && return 0; case " $GROUPS_ " in *" $1 "*) return 0;; esac; return 1; }
GROUPS_="$*"

if want half; then
  # rate 1/2: all words invariant under one translation (lifts of 16 points), genuine degree. 7 minutes.
  run fix1_22 5 16 22 rand 1 4 fix 1
  # words of phantom degree <= r (polynomials of degree <= T + r modulo codewords): 40 s, 76 s, 158 s, 10 min, 8 min
  for r in 1 2 3 4 5; do run osc${r}_22 5 16 22 rand 1 4 osc $r; done
  # T = 21: 109 s, 215 s, 7 min, 11 min
  for r in 1 2 3 4; do run osc${r}_21 5 16 21 rand 1 4 osc $r; done
  # degree <= n/2: the fully translation-invariant words X^(n/2) l(X). 66 s, 22 s, 7 s
  for T in 21 22 23; do run s17_${T}_fix5 5 17 $T rand 1 4 fix 5; done
  # second basis
  run osc1_22_seed2 5 16 22 rand 2 4 osc 1
  run fix1_22_seed2 5 16 22 rand 2 4 fix 1
fi
if want pairs; then
  # largest list containing a given pair of 22-sets: a lifted pair, an interval pair, four random pairs with union D.
  # About one minute each.
  run pair_22_lift 5 16 22 rand 1 4 fam 00fffcff ff00fcff
  run pair_22_int 5 16 22 rand 1 4 fam 003fffff fffffc00
  run pair_22_r1 5 16 22 rand 1 4 fam fb7cf23b d7cbbdc7
  run pair_22_r2 5 16 22 rand 1 4 fam ede5f65e 3a7efbb5
  run pair_22_r3 5 16 22 rand 1 4 fam 6f69dd6f d99ef3f5
  run pair_22_r4 5 16 22 rand 1 4 fam bacfd67b 5f7c3be7
fi
if want eighth; then
  # rate 1/8: lists containing four and five of the six lifted Sidon lines (197 s, 1 s), and low phantom degree at
  # T = 11 (r = 0: 178 s with 2 GB, then 40 to 110 s)
  run k4_fam_10 5 4 10 rand 1 4 fam 033fc000 03c03f00 0c3030f0 300c0ccc
  run k4_fam_10b 5 4 10 rand 1 4 fam 033fc000 03c03f00 0c3030f0 300c0ccc c003033c
  for r in 0 1 2 3 4 5; do run osc_k4_T11_r$r 5 4 11 rand 1 4 osc $r; done
  for r in 1 2 3 4 5; do run osc_k4_T10_r$r 5 4 10 rand 1 4 osc $r; done
  for r in 1 2 3 4; do run osc_k4_T9_r$r 5 4 9 rand 1 4 osc $r; done
  # slack 1: the fully translation-invariant words at degree <= 4
  for T in 9 10 11 12; do run s5_${T}_fix5 5 5 $T rand 1 4 fix 5; done
fi
