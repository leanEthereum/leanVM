#!/bin/bash
# Task 3: climbing searches, 4 processes. Output 69_t3_output.txt (one summary line and one pattern line per job).
cd "$(dirname "$0")"; mkdir -p 69_bin 69_tmp
for fb in 8 16 64; do cc -O2 -DFB=$fb 69_t3_climb.c -o 69_bin/t3_climb_$fb || exit 1; done
jobs=69_tmp/t3_jobs.txt; : > $jobs
add() { echo "./69_bin/t3_climb_$1 $2 $3 $4 $5 $6 $7 $8 2" >> $jobs; }   # fb v r L kind restarts steps seed
for fb in 8 16; do
  for kind in 2 1 S R U; do add $fb 4 1 1 $kind 300 1500 21; add $fb 4 1 2 $kind 300 2000 22; add $fb 4 1 3 $kind 200 2000 23; add $fb 4 1 5 $kind 60 2500 24; done
  for kind in 2 S R U; do add $fb 5 1 1 $kind 150 3000 25; add $fb 5 1 2 $kind 40 3000 26; add $fb 3 2 1 $kind 300 1500 27; add $fb 3 2 2 $kind 300 2000 28; add $fb 3 2 3 $kind 200 2000 29; done
done
for kind in 2 S U; do add 64 4 1 2 $kind 300 2000 31; add 64 4 1 3 $kind 200 2000 32; add 64 4 1 5 $kind 60 2500 33; done
tr '\n' '\0' < $jobs | xargs -0 -P 4 -I{} sh -c '{}' > 69_tmp/t3_raw.txt
grep "^FB" 69_tmp/t3_raw.txt | sort -t= -k4,4 -k5,5n -k2,2n -k3,3 > 69_t3_output.txt
