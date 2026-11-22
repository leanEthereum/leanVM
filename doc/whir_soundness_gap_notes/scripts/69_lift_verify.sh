#!/bin/bash
# Lifts of the best patterns of the top [4,2] code (rate 1/2), checked by exact rank at 64 bits on U, T2, T1, S, R.
cd "$(dirname "$0")"; mkdir -p 69_tmp 69_bin; cc -O2 -DFB=64 69_t2_file.c -o 69_bin/t2_file || exit 1; : > 69_lift_verify_output.txt
chk() { echo "$1" | python3 69_lift.py $2 $3 2>/dev/null > 69_tmp/lv.txt; v=$((1+$3))
  ./69_bin/t2_file $v 1 $(($2-1)) U21SR $4 69_tmp/lv.txt | grep -v "^#" | sed 's/prof=[0-9,]* up=[0-9,]* //g; s/ | [0-9. ]*$//' | sed "s/^/top [$1] members $2 lifted to n=$((4<<$3)): /" >> 69_lift_verify_output.txt; }
for lo in 3 4 5; do chk "12 02 01 ." 3 $lo 5; chk "123 03 02 01" 4 $lo 6; chk "134 024 23 01" 5 $lo 7; chk "012 034 135 245" 6 $lo 8; done
