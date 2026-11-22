#!/bin/bash
# Task 2 sampled scans (4 processes), then the kernel profiles of the deficient patterns found.
cd "$(dirname "$0")"; mkdir -p 69_bin 69_tmp
cc -O2 -DFB=64 69_t2_samp.c -o 69_bin/t2_samp || exit 1
cc -O2 -DFB=64 69_t2_file.c -o 69_bin/t2_file || exit 1
run() { ./69_bin/t2_samp $1 $2 $3 $4 $5 U2R1S 69_tmp/samp_$6.txt > 69_tmp/samp_out_$6.txt; ./69_bin/t2_file $1 $2 $3 U21RS $(( $5 + 1 )) 69_tmp/samp_$6.txt | grep "^#" >> 69_tmp/samp_out_$6.txt; }
run 3 1 3 100000 11 8_16_4 &
run 4 1 2 30000 12 16_32_3 &
run 4 1 3 20000 13 16_32_4 &
run 3 2 2 30000 14 8_32_3 &
wait
cat 69_tmp/samp_out_8_16_4.txt 69_tmp/samp_out_16_32_3.txt 69_tmp/samp_out_16_32_4.txt 69_tmp/samp_out_8_32_3.txt > 69_t2_samp_output.txt
