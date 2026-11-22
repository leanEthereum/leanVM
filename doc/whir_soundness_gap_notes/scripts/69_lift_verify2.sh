#!/bin/bash
# Every best pattern of 69_lift_output.txt, lifted by 3 bottom layers and checked by exact rank at 64 bits on U, T2, T1, S, R.
cd "$(dirname "$0")"; mkdir -p 69_tmp 69_bin; cc -O2 -DFB=64 69_t2_file.c -o 69_bin/t2_file || exit 1
: > 69_lift_verify2_output.txt
while IFS= read -r line; do
  top=$(echo "$line" | sed 's/.*top \[\([0-9]*\),\([0-9]*\)\].*/\1 \2/'); N=${top% *}; ku=${top#* }
  mem=$(echo "$line" | sed 's/.*members=\([0-9]*\).*/\1/'); pat=$(echo "$line" | sed 's/.*best: //')
  vtop=0; t=$ku; while [ $t -gt 1 ]; do t=$((t/2)); vtop=$((vtop+1)); done
  r=0; t=$((N/ku)); while [ $t -gt 1 ]; do t=$((t/2)); r=$((r+1)); done
  echo "$pat" | python3 69_lift.py $mem 3 2>/dev/null > 69_tmp/lv2.txt
  ./69_bin/t2_file $((vtop+3)) $r $((mem-1)) U21SR 9 69_tmp/lv2.txt | grep -v "^#" | sed 's/prof=[0-9,]* up=[0-9,]* //g; s/ | [0-9. ]*$//' | sed "s/^/top [$N,$ku] members $mem, n=$((N*8)) k=$((ku*8)): /" >> 69_lift_verify2_output.txt
done < 69_lift_output.txt
