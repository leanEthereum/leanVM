#!/bin/bash
# Task 2 exhaustive scans: usage 69_t2_run_exh.sh v r L kinds tag  (4 processes, canonical patterns)
cd "$(dirname "$0")"; mkdir -p 69_bin 69_tmp
cc -O2 -DFB=64 69_t2_exh.c -o 69_bin/t2_exh || exit 1
v=$1; r=$2; L=$3; kinds=$4; tag=$5
for p in 0 1 2 3; do ./69_bin/t2_exh $v $r $L canon $p 4 $((100+p)) $kinds 69_tmp/def_${tag}_$p.txt > 69_tmp/out_${tag}_$p.txt & done
wait
cat 69_tmp/out_${tag}_?.txt > 69_t2_exh_${tag}_output.txt
cat 69_tmp/def_${tag}_?.txt > 69_tmp/def_${tag}.txt
wc -l 69_tmp/def_${tag}.txt >> 69_t2_exh_${tag}_output.txt
