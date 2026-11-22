#!/bin/bash
# Note 74, task 4: local searches (4 processes). Output: 74_climb_output.txt
cd "$(dirname "$0")"; mkdir -p 74_bin 74_tmp
cc -O2 -DFB=64 74_climb.c -o 74_bin/climb || exit 1
jobs=74_tmp/climb_jobs.txt; : > $jobs
for M in 8 12 15 16 20 24 32 35; do f=0; [ $M -le 15 ] && f=1; echo "./74_bin/climb 2 $M 5 F 40000 1$M $f" >> $jobs; echo "./74_bin/climb 2 $M 5 R 40000 2$M" >> $jobs; echo "./74_bin/climb 2 $M 5 R 40000 3$M" >> $jobs; done
for M in 16 32; do echo "./74_bin/climb 3 $M 5 S 15000 4$M" >> $jobs; echo "./74_bin/climb 3 $M 5 F 15000 5$M 5" >> $jobs; echo "./74_bin/climb 3 $M 5 R 15000 6$M" >> $jobs; done
for M in 36 40 48; do echo "./74_bin/climb 3 $M 5 F 8000 7$M 4" >> $jobs; done
echo "./74_bin/climb 3 64 5 F 8000 81 4" >> $jobs; echo "./74_bin/climb 3 64 5 F 8000 82 3" >> $jobs; echo "./74_bin/climb 3 64 5 R 6000 83" >> $jobs
tr '\n' '\0' < $jobs | xargs -0 -P 4 -I{} sh -c '{}' > 74_tmp/climb_raw.txt
sort 74_tmp/climb_raw.txt > 74_climb_output.txt
