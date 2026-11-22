#!/bin/sh
# 51_run.sh: regenerates 51_results.txt (about 2 to 4 minutes per run on one core, 20 minutes in all; the runs are independent).
# Run inside scripts/.
out=51_results.txt
: > $out
for lg in 25 26 27 28; do
  echo "=== python3 51_profiles.py a=0.7065 lg=$lg depth=8" >> $out
  python3 51_profiles.py a=0.7065 lg=$lg depth=8 >> $out
done
for lg in 25 26 27 28; do
  echo "=== python3 51_profiles.py a=0.705 lg=$lg depth=8" >> $out
  python3 51_profiles.py a=0.705 lg=$lg depth=8 >> $out
done
for s in 1 2 3 4; do
  echo "=== python3 51_planted.py $s" >> $out
  python3 51_planted.py $s >> $out
done
