#!/bin/bash
# Note 83: regenerate the data of Sections 4 and 5. About ten minutes on four cores.
cd "$(dirname "$0")"; mkdir -p 83_bin 83_tmp
cc -O2 -shared -fPIC -o 83_bin/libgf83.dylib 83_gflib.c || exit 1
cc -O2 -DFB=64 -o 83_bin/votes 83_votes.c || exit 1
./76_bin/76_n8 2 3 1 4 > 83_tmp/n8_lists4.txt
/usr/bin/python3 83_profile.py 8 83_tmp/n8_lists4.txt > 83_tmp/profile_n8.txt
/usr/bin/python3 83_profile.py 16 76_tmp/n16_orbits5.txt > 83_tmp/profile_n16.txt
/usr/bin/python3 83_products.py 8 83_tmp/n8_lists4.txt > 83_tmp/products_n8.txt
/usr/bin/python3 83_products.py 16 76_tmp/n16_orbits5.txt > 83_tmp/products_n16.txt
par() { tr '\n' '\0' | xargs -0 -P 4 -I{} sh -c '{}'; }
(for s in 1 2 3; do echo "./83_bin/votes 2 2 5 10 300000 $s"; echo "./83_bin/votes 2 2 6 10 300000 $s"; done) | par > 83_tmp/votes_c8_b2.txt
(for s in 1 2 3 4 5 6 7 8; do echo "./83_bin/votes 2 4 6 20 2000000 $s"; done; for s in 1 2 3 4; do echo "./83_bin/votes 2 4 5 20 1000000 $s"; done) | par > 83_tmp/votes_c8_b4.txt
(for s in 11 12 13 14 15 16 17 18; do echo "./83_bin/votes 2 4 7 20 3000000 $s"; done) | par > 83_tmp/votes_c8_b4_m7.txt
(for M in 8 9 10 11; do for s in 21 22 23 24; do echo "./83_bin/votes 2 4 $M 20 4000000 $s$M"; done; done) | par > 83_tmp/votes_c8_b4_m8plus.txt
(echo "./83_bin/votes 2 8 11 40 6000000 5111"; echo "./83_bin/votes 2 8 12 40 6000000 5112") | par > 83_tmp/votes_c8_b8.txt
(for M in 6 7 8; do for s in 31 32 33 34; do echo "./83_bin/votes 3 2 $M 20 1500000 $s$M"; done; done) | par > 83_tmp/votes_c16_b2.txt
for f in votes_c8_b4 votes_c8_b4_m7 votes_c8_b8; do /usr/bin/python3 83_verify.py 83_tmp/$f.txt > 83_tmp/verify_$f.txt; done
/usr/bin/python3 83_scales.py 83_tmp/votes_c8_b4_m7.txt 0 135 > 83_tmp/scales_m7.txt
# negative control of the annealer at scale 16 (about fifteen minutes): ./83_bin/votes 3 1 20 9 1200000 4120 0 1.0 0x1
