#!/bin/bash
# The main lifted lists at n = 256 (lift by 5 layers), exact rank at 64 bits on U, T2, S. Output 69_lift_verify3_output.txt.
cd "$(dirname "$0")"; mkdir -p 69_tmp 69_bin; cc -O2 -DFB=64 69_t2_file.c -o 69_bin/t2_file || exit 1
: > 69_lift_verify3_output.txt
chk() { echo "$1" | python3 69_lift.py $2 5 2>/dev/null > 69_tmp/lv3.txt
  ./69_bin/t2_file $3 $4 $(($2-1)) U2S 11 69_tmp/lv3.txt | grep -v "^#" | sed 's/prof=[0-9,]* up=[0-9,]* //g; s/ | [0-9. ]*$//' | sed "s/^/top [$1] members $2, n=256: /" >> 69_lift_verify3_output.txt; }
chk ". 0123 123 12 02 023 013 01" 4 7 1; chk ". 0124 0123 . 0134 . 0234 1234" 5 7 1; chk "35 123456 . 0134567 0157 12347 024567 0236" 8 7 1
chk ". 23 01 02 . . 03 12" 4 6 2; chk ". 23 12 . 134 03 024 ." 5 6 2
