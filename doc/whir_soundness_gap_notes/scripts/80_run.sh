#!/bin/sh
# Referee 80 (note 76): regenerates the outputs quoted in 80-referee-76-79.md. About twelve minutes on four cores without "n16";
# "./80_run.sh n16" also re-runs note 76's search at n = 16 with seed 3 (about nine more minutes, four cores).
cd "$(dirname "$0")" || exit 1
mkdir -p 80_bin 80_tmp
for p in match match4 dual lists lem23 conj44 t1; do cc -O2 -o 80_bin/$p 80_$p.c || exit 1; done
./80_match_run.sh                                   # Theorem 4.1, Corollaries 4.2, 4.3 (T2, T1): 80_match_output.txt
{ for m in 3 4 5 6; do ./80_bin/match4 $m 100000 $m 2; done; ./80_bin/match4 4 100000 9 1; ./80_bin/match4 5 100000 10 1; } > 80_match4_output.txt
./80_bin/dual 1 > 80_dual_output.txt                # Lemma 1.1
{ for var in 2 1; do ./80_bin/lem23 deriv 3 3 $var 20000 1; ./80_bin/lem23 deriv 3 4 $var 20000 2; ./80_bin/lem23 deriv 4 4 $var 4000 3; done
  ./80_bin/lem23 lift 1 76_tmp/n16_orbits5.txt; } > 80_lem23_output.txt   # Lemmas 2.3 and 2.1
{ ./80_bin/lists n8 1; ./80_bin/lists n8 2; ./80_bin/lists n16 1 76_tmp/n16_orbits5.txt; } > 80_lists_output.txt   # exact list sizes
/usr/bin/python3 80_r3.py 2 3 4 5 6 > 80_r3_output.txt   # three members: closed form of the best matching bound (parts C, D)
./80_bin/t1 5 "3 3 1 1 2 2 0 4 3 3 4 0 1 1 4 0" "0 4 1 1 3 3 0 4 4 0 1 1 2 2 2 2" "2 2 4 4 0 0 0 4 0 4 4 0 3 3 1 1" "2 2 2 2 0 0 0 0 4 0 4 0 4 0 0 0 3 3 3 3 1 1 1 1 0 4 4 4 4 4 4 4" > 80_t1_output.txt
# Conjecture 4.4
for s in 1 2 3 4; do ./80_bin/conj44 rand16 $s 1000000 > 80_tmp/conj16_seed$s.txt 2>&1 & done; wait
for s in 1 2 3 4; do ./80_bin/conj44 rand32 $s 500000 > 80_tmp/conj32_seed$s.txt 2>&1 & done; wait
{ ./80_bin/conj44 all48 1
  for s in 1 2 3 4; do tail -1 80_tmp/conj16_seed$s.txt; done
  echo "counterexamples at (8,16) by (weight, r_3, rank):"; cat 80_tmp/conj16_seed?.txt | grep COUNTER | sed 's/:.*//' | sort | uniq -c
  echo "first counterexamples at (8,16):"; grep -h COUNTER 80_tmp/conj16_seed1.txt | head -6
  for s in 1 2 3 4; do tail -1 80_tmp/conj32_seed$s.txt; done
  echo "counterexamples at (16,32) by (r_4, rank, weight):"; cat 80_tmp/conj32_seed?.txt | grep COUNTEREXAMPLE | sed 's/:.*exact r_4 = \([0-9]*\) < rank \([0-9]*\) (w \([0-9]*\)).*/ r4=\1 rank=\2 w=\3/' | sort | uniq -c
  echo "first counterexamples at (16,32):"; grep -h COUNTEREXAMPLE 80_tmp/conj32_seed1.txt | head -4
  ./80_bin/conj44 exact32 1 "2 2 4 4 0 0 0 4 0 4 4 0 3 3 1 1"
  FULL=1 ./80_bin/conj44 exact32 1 "2 2 4 4 0 0 0 4 0 4 4 0 3 3 1 1"
  echo "with note 76's own recursion and rank code:"; /usr/bin/python3 80_conj44_check.py "2 2 4 4 0 0 0 4 0 4 4 0 3 3 1 1" "3 3 4 0 0 0 2 2 1 1 4 0 4 4 4 0" "0 4 1 1 0 4 4 0 3 3 0 0 4 4 2 2"
  echo "T1 against T2:"; grep -h 'T1 rank' 80_tmp/conj16_seed1.txt | head -4
  ./80_bin/t1 5 "3 3 1 1 2 2 0 4 3 3 4 0 1 1 4 0" "0 4 1 1 3 3 0 4 4 0 1 1 2 2 2 2"
} > 80_conj44_output.txt 2>&1
if [ "$1" = "n16" ]; then
  cc -O2 -o 80_bin/76_n16 76_n16.c || exit 1
  for p in 0 1 2 3; do ./80_bin/76_n16 3 $p 4 5 5 > 80_tmp/n16_seed3_part$p.txt 2> 80_tmp/n16_seed3_part$p.err & done; wait
  { grep -h -v LIST 80_tmp/n16_seed3_part?.txt; /usr/bin/python3 76_orbits.py 5 80_tmp/n16_seed3_part0.txt 80_tmp/n16_seed3_part1.txt 80_tmp/n16_seed3_part2.txt 80_tmp/n16_seed3_part3.txt 2>/dev/null | head -1; } > 80_n16_seed3_output.txt
fi
