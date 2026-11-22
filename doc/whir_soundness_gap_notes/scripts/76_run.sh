#!/bin/sh
# Note 76: regenerates 76_output.txt (about fifteen minutes, one core). "./76_run.sh n16" runs the exhaustive search at
# n = 16 instead (seeds 1 and 2, four processes a seed, about nine minutes a seed) and classifies the lists of five.
cd "$(dirname "$0")" || exit 1
mkdir -p 76_bin 76_tmp
cc -O2 -o 76_bin/76_n8 76_n8.c || exit 1
cc -O2 -o 76_bin/76_n16 76_n16.c || exit 1
if [ "$1" = "n16" ]; then
    for seed in 1 2; do
        for p in 0 1 2 3; do ./76_bin/76_n16 $seed $p 4 5 5 > 76_tmp/n16_seed${seed}_part$p.txt 2> 76_tmp/n16_seed${seed}_part$p.err & done
        wait
        grep -h -v LIST 76_tmp/n16_seed${seed}_part?.txt
    done
    /usr/bin/python3 76_orbits.py 5 76_tmp/n16_seed2_part0.txt 76_tmp/n16_seed2_part1.txt 76_tmp/n16_seed2_part2.txt 76_tmp/n16_seed2_part3.txt > 76_tmp/n16_orbits5.txt
    head -1 76_tmp/n16_orbits5.txt
    /usr/bin/python3 76_verify16.py
    exit 0
fi
{
    echo "== Lemma 1.1 (76_dual.py)"; /usr/bin/python3 76_dual.py
    echo "== Experiment 3.1 (76_n8, seeds 1 and 2)"; ./76_bin/76_n8 2 3 1; ./76_bin/76_n8 2 3 2
    echo "== the 35-member staircase at (8,16) (76_stair_rank.py)"; /usr/bin/python3 76_stair_rank.py
    echo "== Corollaries 4.2 and 4.3 on random patterns (76_match.py)"; /usr/bin/python3 76_match.py
    echo "== Corollaries 4.2 and 4.3 on the deficient orbits (76_match_def.py)"; /usr/bin/python3 76_match_def.py
    echo "== recursion of Theorem 4.1 on the deficient orbits at (4,8) (76_scheme.py)"; /usr/bin/python3 76_scheme.py
    echo "== recursion of Theorem 4.1 on random patterns at (4,8) (76_scheme_rand.py)"; /usr/bin/python3 76_scheme_rand.py
    echo "== recursion of Theorem 4.1 on the deficient three-member orbits at (8,16) (76_scheme16.py)"; /usr/bin/python3 76_scheme16.py
    echo "== recursion of Theorem 4.1 on random three-member patterns at (8,16) (76_scheme16_rand.py)"; /usr/bin/python3 76_scheme16_rand.py
} > 76_output.txt 2>&1
