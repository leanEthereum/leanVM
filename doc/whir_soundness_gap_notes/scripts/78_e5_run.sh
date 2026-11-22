#!/bin/bash
# Note 78, experiment 5(a): adaptive pattern search. usage: 78_e5_run.sh small|large   (4 processes; outputs 78_e5_climb_<size>_output.txt)
cd "$(dirname "$0")"; mkdir -p 78_bin 78_tmp
cc -O2 -DFB=64 78_e5_climb.c -o 78_bin/e5_climb || exit 1
jobs=78_tmp/e5_jobs_$1.txt; : > $jobs
if [ "$1" = small ]; then   # (16,32)
  for spec in U T2 T2:d1a T2:d1x T2:d2x T2:Mup T2:Mud T2:Mud:d1x; do
    echo "./78_bin/e5_climb 4 1 2 $spec 1500 3000 902 a" >> $jobs; echo "./78_bin/e5_climb 4 1 3 $spec 800 3000 903 a" >> $jobs
    echo "./78_bin/e5_climb 4 1 4 $spec 300 3000 904 a" >> $jobs; echo "./78_bin/e5_climb 4 1 5 $spec 200 3000 905 a" >> $jobs
  done
  for spec in T2 T2:d1a T2:d1x T2:d2x T2:Mup T2:Mud; do echo "./78_bin/e5_climb 4 1 2 $spec 800 3000 912 w" >> $jobs; echo "./78_bin/e5_climb 4 1 3 $spec 500 3000 913 w" >> $jobs; done
else                        # (32,64)
  for spec in U T2 T2:d1a T2:d1x T2:Mup T2:Mud; do
    echo "./78_bin/e5_climb 5 1 2 $spec 300 2500 922 a" >> $jobs; echo "./78_bin/e5_climb 5 1 3 $spec 200 2500 923 a" >> $jobs
    echo "./78_bin/e5_climb 5 1 4 $spec 100 2500 924 a" >> $jobs; echo "./78_bin/e5_climb 5 1 5 $spec 60 2500 925 a" >> $jobs
  done
fi
tr '\n' '\0' < $jobs | xargs -0 -P 4 -I{} sh -c '{}' > 78_tmp/e5_raw_$1.txt
cp 78_tmp/e5_raw_$1.txt 78_e5_climb_$1_output.txt
