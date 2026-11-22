#!/bin/bash
# Best lifted lists: patterns of a small top tree code (64-bit, generic twiddles), scored by the balanced agreement of
# their lift by 5 bottom layers. Top [4,2] is done exhaustively (restarts = 0), the others by climbing.
cd "$(dirname "$0")"; mkdir -p 69_bin 69_tmp
cc -O2 -DFB=64 69_t3_climb.c -o 69_bin/t3_climb_64 || exit 1
jobs=69_tmp/lift_jobs.txt; : > $jobs
for L in 2 3 4 5; do echo "./69_bin/t3_climb_64 1 1 $L 2 0 0 1 1 5" >> $jobs; done
for L in 2 3 4 5 6 7; do echo "./69_bin/t3_climb_64 2 1 $L 2 500 500 5$L 2 5" >> $jobs; echo "./69_bin/t3_climb_64 1 2 $L 2 500 500 6$L 2 5" >> $jobs; done
for L in 2 3 4 5; do echo "./69_bin/t3_climb_64 2 2 $L 2 150 600 7$L 2 5" >> $jobs; echo "./69_bin/t3_climb_64 3 1 $L 2 100 600 8$L 2 5" >> $jobs; done
tr '\n' '\0' < $jobs | xargs -0 -P 4 -I{} sh -c '{}' > 69_tmp/lift_raw.txt
paste - - < 69_tmp/lift_raw.txt | sort > 69_lift_output.txt
