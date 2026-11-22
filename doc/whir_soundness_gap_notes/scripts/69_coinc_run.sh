#!/bin/bash
# Coincidences: planted (64-bit) and exhaustive classification over GF(2^8) and GF(2^16) at k = 8, n = 16.
cd "$(dirname "$0")"; mkdir -p 69_bin 69_tmp
cc -O2 -DFB=64 69_coinc_plant.c -o 69_bin/coinc_plant || exit 1
cc -O2 -DFB=8 69_coinc_exh.c -o 69_bin/coinc_exh_8 || exit 1; cc -O2 -DFB=16 69_coinc_exh.c -o 69_bin/coinc_exh_16 || exit 1
./69_bin/coinc_exh_8 60000 1 2 > 69_tmp/ce_a.txt & ./69_bin/coinc_exh_8 60000 2 1 > 69_tmp/ce_b.txt & ./69_bin/coinc_exh_16 60000 3 2 > 69_tmp/ce_c.txt & ./69_bin/coinc_exh_16 60000 4 1 > 69_tmp/ce_d.txt &
wait
cat 69_tmp/ce_a.txt 69_tmp/ce_b.txt 69_tmp/ce_c.txt 69_tmp/ce_d.txt > 69_coinc_exh_output.txt
