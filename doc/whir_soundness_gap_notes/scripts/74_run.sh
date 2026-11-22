#!/bin/bash
# Note 74: reproduces every number of the note except the local searches (74_climb_run.sh). Output: 74_output.txt.
# Needs 69_gf.h, 69_tree.h, 69_pat.h, 69_lin.h and note 69's lists 69_t2_def_*.txt; 74_def_4_8_4.txt is the list of the 1740
# deficient orbits at (4,8) with four members (regenerate: cc -O2 -DFB=64 69_t2_exh.c, then "t2_exh 2 1 3 canon p 4 seed U2 out" for p = 0..3).
cd "$(dirname "$0")"; mkdir -p 74_bin 74_tmp
for p in rec star classify stair thmA; do cc -O2 -DFB=64 74_$p.c -o 74_bin/$p || exit 1; done
{
echo "== Section 2: one-level identity (74_rec) =="
grep ' 2=7 ' 69_t2_def_4_8_3_full.txt > 74_tmp/def_4_8_3_T2.txt
./74_bin/rec 2 1 2 1 6 74_tmp/def_4_8_3_T2.txt | tail -1
./74_bin/rec 2 1 3 21 6 74_def_4_8_4.txt | tail -1
./74_bin/rec 3 1 2 2 6 69_t2_def_8_16_3.txt | tail -1
./74_bin/rec 2 2 2 3 6 69_t2_def_4_16_3.txt | tail -1
python3 74_allpat.py 8 3 all | ./74_bin/rec 2 1 2 5 5 - | tail -1
python3 74_allpat.py 16 3 random 60000 1 10 | ./74_bin/rec 3 1 2 7 5 - | tail -1
python3 74_allpat.py 8 4 random 150000 2 6 | ./74_bin/rec 2 1 3 8 5 - | tail -1
python3 74_allpat.py 16 4 random 30000 3 16 | ./74_bin/rec 3 1 3 9 5 - | tail -1
python3 74_allpat.py 16 3 random 60000 4 5 | ./74_bin/rec 2 2 2 10 5 - | tail -1
python3 74_allpat.py 8 5 random 60000 5 8 | ./74_bin/rec 2 1 4 11 5 - | tail -1
python3 74_allpat.py 32 3 random 5000 6 24 | ./74_bin/rec 4 1 2 12 4 - | tail -1
echo "== Section 2: arbitrary subspaces (74_star, 74_star_one, 74_segre) =="
./74_bin/star 300000 1 5 7 3; ./74_bin/star 300000 2 7 10 3; ./74_bin/star 200000 3 8 12 4
python3 74_star_one.py '011011,111100;111000,001010,111111;011100,100001;011010,101110,010100;010010,010110,011001'
python3 74_segre.py
echo "== Section 3: classification (74_classify, 74_sublists) =="
./74_bin/classify 2 1 2 1 74_tmp/def_4_8_3_T2.txt | tail -1
./74_bin/classify 3 1 2 4 69_t2_def_8_16_3.txt v | grep -v '^#' | awk '{print $1,$2,$3,$5,$6,$7,$8,$9}' | sort | uniq -c | sort -rn
./74_bin/classify 3 1 2 4 69_t2_def_8_16_3.txt | tail -1
./74_bin/classify 2 2 2 3 69_t2_def_4_16_3.txt | tail -1
./74_bin/classify 2 1 3 2 74_def_4_8_4.txt v > 74_tmp/cls_4_8_4_v.txt; tail -1 74_tmp/cls_4_8_4_v.txt
grep -v '^#' 74_tmp/cls_4_8_4_v.txt > 74_tmp/all_4_8_4.txt
python3 74_sublists.py 4 3 < 74_tmp/all_4_8_4.txt > 74_tmp/all_4_8_4_sub3.txt
./74_bin/classify 2 1 2 5 74_tmp/all_4_8_4_sub3.txt v > 74_tmp/cls_all_sub3.txt
python3 74_sublists_join.py 74_tmp/all_4_8_4.txt 74_tmp/cls_all_sub3.txt
echo "== Section 4: Theorem 4.2 (74_thmA), linear program (74_lp) =="
./74_bin/thmA 2 1 2 300000 1 g; ./74_bin/thmA 3 1 2 200000 2 g; ./74_bin/thmA 3 1 3 200000 3 g; ./74_bin/thmA 2 2 2 200000 4 g
./74_bin/thmA 3 1 3 200000 5 a; ./74_bin/thmA 4 1 2 60000 6 g; ./74_bin/thmA 4 1 4 40000 7 a; ./74_bin/thmA 3 2 3 100000 8 a
python3 74_lp.py
echo "== Section 5: the (16,32) kernel with a two-dimensional lower-factor space (74_two_dim) =="
python3 74_two_dim.py
echo "== Section 6: one-sided staircase by encoding (74_stair) =="
./74_bin/stair 4 1 3 0 1000 1; ./74_bin/stair 5 1 3 0 1000 2; ./74_bin/stair 6 1 4 0 1000 3; ./74_bin/stair 7 1 5 0 1000 3
./74_bin/stair 5 1 2 0 100000 4; ./74_bin/stair 6 1 3 0 100000 5; ./74_bin/stair 7 1 4 0 100000 5
./74_bin/stair 7 1 4 4 64 6; ./74_bin/stair 7 1 5 0 16 7; ./74_bin/stair 7 1 5 0 32 8; ./74_bin/stair 7 1 5 1 15 8; ./74_bin/stair 7 1 4 5 45 8
./74_bin/stair 6 2 3 0 100000 9; ./74_bin/stair 6 2 4 0 100000 9
} > 74_output.txt 2>&1
