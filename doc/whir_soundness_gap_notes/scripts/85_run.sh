#!/bin/bash
# Note 85: regenerates scripts/85_tmp/*.txt (about three minutes, one core). Needs 83_bin/libgf83.dylib (83_run.sh), 82_bin/82_big (82_run.sh),
# and the lists of notes 76 and 83 (76_tmp/n16_orbits5.txt, 83_tmp/n8_lists4.txt, 83_tmp/votes_*.txt).
cd "$(dirname "$0")"; mkdir -p 85_tmp; P=/usr/bin/python3
echo "classes per leaf: 012 012 012 . 012 012 012 . 012 012 012 . 01 01 01 01 02 02 02 02 12 12 12 12 . . . . . . . ." > 85_tmp/cex3.txt
echo "x | 012 012 012 . 012 012 012 . 012 012 012 . 01 01 01 01 02 02 02 02 12 12 12 12 . . . . . . . ." > 85_tmp/cex3_82.txt
{ $P 85_cex.py; $P 85_cex.py 10; VERBOSE=1 82_bin/82_big file 4 1 3 85_tmp/cex3_82.txt; $P 85_chain.py 85_tmp/cex3.txt; } > 85_tmp/cex_output.txt 2>&1
{ for f in 83_tmp/n8_lists4.txt 76_tmp/n16_orbits5.txt 83_tmp/votes_c8_b2.txt 83_tmp/votes_c8_b4.txt 83_tmp/votes_c8_b4_m7.txt 83_tmp/votes_c8_b8.txt 83_tmp/votes_c16_b2.txt; do $P 85_chain.py $f 100000 brief; done; } > 85_tmp/chain_lists_brief.txt 2>&1
{ for a in "stair 8 16 1" "stair 8 2 0" "stair 8 4 0" "stair 8 8 0" "stairm 8 4 2 0" "stairm 8 8 2 0" "stairm 8 8 2 1" "stairm 8 4 3 0" "stairm 8 8 3 0" "stairm 8 8 3 1" "stairm 8 4 4 0"; do echo "== $a"; $P 85_chain.py $a; done; $P 85_chain.py 83_tmp/votes_c8_b4_m7.txt 1; $P 85_chain.py 83_tmp/votes_c8_b8.txt 1; } > 85_tmp/chain_families.txt 2>&1
grep -c . 85_tmp/*.txt
