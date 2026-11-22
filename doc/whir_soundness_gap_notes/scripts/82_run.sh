#!/bin/sh
# Note 82: regenerates 82_output.txt (about fifteen minutes on one core; `82_k2 multi 5 6` is separate, about ten more).
cd "$(dirname "$0")" && mkdir -p 82_bin 82_tmp
cc -O2 -o 82_bin/82_rank 82_rank.c && cc -O2 -o 82_bin/82_bin 82_binary.c && cc -O2 -o 82_bin/82_big 82_big.c && cc -O2 -o 82_bin/82_k2 82_k2.c || exit 1
R=82_bin/82_rank; B=82_bin/82_bin; G=82_bin/82_big; K=82_bin/82_k2; T=82_tmp
{
echo "== partition patterns, tables one level up (82_rank.c)"
$R table 0 1 3 $T/t_0_1_3.bin; $R table 1 1 3 $T/t_1_1_3.bin; $R table 2 1 3 $T/t_2_1_3.bin; $R table 1 2 3 $T/t_1_2_3.bin
$R table 0 1 4 $T/t_0_1_4.bin; $R table 1 1 4 $T/t_1_1_4.bin
$R all 1 1 3 $T/t_0_1_3.bin; $R all 2 1 3 $T/t_1_1_3.bin
$R file 3 1 3 $T/t_2_1_3.bin 69_t2_def_8_16_3.txt; $R file 2 1 3 $T/t_1_1_3.bin 69_t2_def_4_8_3_full.txt
$R rand 3 1 3 $T/t_2_1_3.bin 20000 1 10; $R file 2 2 3 $T/t_1_2_3.bin 69_t2_def_4_16_3.txt; $R rand 2 2 3 $T/t_1_2_3.bin 20000 2 0
$R all 1 1 4 $T/t_0_1_4.bin; $R file 2 1 4 $T/t_1_1_4.bin 74_def_4_8_4.txt
echo "== binary patterns (82_binary.c)"
for m in 3 4; do $B table 0 1 $m $T/b_0_1_$m.bin; $B table 1 1 $m $T/b_1_1_$m.bin; $B all 1 1 $m $T/b_0_1_$m.bin; done
$B file 2 1 4 $T/b_1_1_4.bin 74_def_4_8_4.txt
echo "x | 012 023 013 . 123 . 013 12" > $T/p76.txt; $B file 2 1 4 $T/b_1_1_4.bin $T/p76.txt
for kind in class graphic binary; do $B rand 2 1 4 $T/b_1_1_4.bin 30000 5 6 $kind; done
echo "x | 02 02 012 012 . . . 012 . 012 012 . 12 12 01 01" > $T/p80.txt; $R file 3 1 3 $T/t_2_1_3.bin $T/p80.txt
if [ -n "$FIVE" ]; then $B table 0 1 5 $T/b_0_1_5.bin; $B table 1 1 5 $T/b_1_1_5.bin; for kind in class graphic binary; do $B rand 2 1 5 $T/b_1_1_5.bin 1500 7 8 $kind; done; fi
echo "== the binary full part Q* (82_big.c)"
$G rand 2 1 3 20000 1 4 binary; $G file 3 1 3 69_t2_def_8_16_3.txt; $G file 3 1 3 $T/p80.txt; $G rand 2 1 4 5000 1 6 class
$G rand 4 1 3 3000 1 24 binary; $G file 4 1 3 69_t2_def_8_16_3.txt lift; $G file 4 1 3 $T/p80.txt lift
for nf in 2 4 8; do $G pert 3 1 3 100000 $nf 8 class $nf; done; for nf in 2 4 8; do $G pert 4 1 3 30000 $nf 16 class $nf; done
$G rand 3 1 4 20000 1 14 class; $G pert 3 1 4 20000 2 12 class 3; $G rand 3 1 4 10000 3 14 binary; $G pert 4 1 4 2000 5 24 class 4
$G rand 3 1 5 3000 1 18 class; $G pert 3 1 5 3000 2 16 class 3
$G rand 2 1 6 3000 1 10 class; $G rand 2 2 6 2000 2 12 class; $G pert 3 1 6 1000 3 20 class 3; $G rand 2 1 6 2000 4 10 graphic
$G rand 2 1 6 40000 21 8 binary; $G rand 2 1 6 40000 22 8 graphic; $G rand 2 1 6 40000 23 10 class; $G rand 2 2 6 20000 24 8 graphic
echo "== Pappus (six members, rate 1/4) and its lifts"
echo "x | 012 03/14 23/15 05/24 345 . . ." > $T/pappus.txt
echo "x | 012 012 03/14 03/14 23/15 23/15 05/24 05/24 345 345 . . . . . ." > $T/pappus_mid.txt
echo "x | 012 012 012 012 03 03 14 14 23 15 23 15 05 24 24 05 345 345 345 345 012345 . . . . 012345 . . . . 012345 ." > $T/pappus_lift.txt
VERBOSE=1 $G file 3 2 6 $T/pappus_lift.txt; VERBOSE=1 $G file 2 2 6 $T/pappus_mid.txt; VERBOSE=1 $G file 1 2 6 $T/pappus.txt
echo "x | . 012 12 12 02 02 01 01" > $T/basic.txt; VERBOSE=1 $G file 2 1 3 $T/basic.txt
echo "== k = 2 (82_k2.c)"
$K planes 6 graphic
$K rand 6 8 200000 1 graphic 8; $K rand 6 8 200000 2 class 8; $K rand 6 6 200000 3 binary 8
for n in 5 6 8; do $K rand 5 $n 300000 $n binary 6; done
for mm in 4 5 6; do ONLY_GRAPHIC_THETA=1 $K rand $mm 8 200000 $mm class 0; done; for nl in 4 5 6; do ONLY_GRAPHIC_THETA=1 $K rand 6 $nl 200000 $nl class 0; done
$K rand 6 4 300000 11 binary 0; $K rand 7 4 100000 12 binary 0; $K rand 6 5 300000 13 binary 0
$K multi 4 5; $K multi 4 6; $K multi 4 7; $K multi 4 8; $K multi 5 5
echo "== the full-part tuple is not exact (82_fullpart.py)"
/usr/bin/python3 82_fullpart.py
} > 82_output.txt 2>&1
