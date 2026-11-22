#!/bin/bash
# Note 78, experiment 4: the lifted lists of notes 69 and 74 as message lists, encoded by each variant. Output 78_e4_output.txt.
cd "$(dirname "$0")"; mkdir -p 78_bin 78_tmp
cc -O2 -DFB=64 78_e4_lists.c -o 78_bin/e4_lists || exit 1
SPECS="T2 T2:d1a T2:d1x T2:d2a T2:d2x T2:d3a T2:d3x T2:Mup T2:Mdn T2:Mud T2:Mcr T2:Mup:d1x"
out=78_e4_output.txt; : > $out
# small lists: every best pattern of 69_lift_output.txt (3 to 8 members), lifted to n = 64, 128, 256
lift() { # N ku lo v r
  grep "top \[$1,$2\]" 69_lift_output.txt | while IFS= read -r line; do
    mem=$(echo "$line" | sed 's/.*members=\([0-9]*\).*/\1/'); pat=$(echo "$line" | sed 's/.*best: //')
    echo "$pat" | python3 69_lift.py $mem $3 2>/dev/null > 78_tmp/e4_pat.txt
    echo "## top [$1,$2] pattern '$pat' ($mem members) lifted by $3 layers: (k,n)=($((1<<$4)),$((1<<($4+$5))))" >> $out
    ./78_bin/e4_lists pat $4 $5 $((1000+mem)) 78_tmp/e4_pat.txt $SPECS | sed 's/^pattern 0 //' >> $out
  done
}
lift 4 2 4 5 1; lift 8 4 3 5 1; lift 16 8 2 5 1        # n = 64
lift 4 2 5 6 1; lift 8 4 4 6 1; lift 16 8 3 6 1        # n = 128
lift 4 2 6 7 1; lift 8 4 5 7 1; lift 16 8 4 7 1        # n = 256
lift 8 2 5 6 2; lift 16 4 4 6 2                        # n = 256, rate 1/4
# staircases: one-sided (note 74) with 35 and 6435 members, balanced (note 69) with 70 members; rate 1/4: 1365 one-sided
echo "## staircases" >> $out
for v in 5 6 7; do
  ./78_bin/e4_lists stair $v 1 $((v-2)) 0 100000 $((2000+v)) $SPECS >> $out      # N = 8: 35 members
  ./78_bin/e4_lists bal   $v 1 $((v-2)) 100000 $((3000+v)) $SPECS >> $out        # N = 8: 70 members
  ./78_bin/e4_lists stair $v 1 $((v-3)) 0 100000 $((4000+v)) $SPECS >> $out      # N = 16: 6435 members
done
./78_bin/e4_lists stair 7 1 4 4 64 5001 $SPECS >> $out                            # N = 16, four free blocks, 64 members
./78_bin/e4_lists stair 6 2 4 0 100000 6001 $SPECS >> $out                        # rate 1/4, N = 16: 1365 members
./78_bin/e4_lists bal 6 2 5 100000 6002 $SPECS >> $out                            # rate 1/4, N = 8: 28 members
