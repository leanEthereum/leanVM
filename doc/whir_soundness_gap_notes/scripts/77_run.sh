#!/bin/sh
# Note 77: regenerates 77_*_output.txt. About 40 minutes on four cores (the n = 16 three-member scans at degree bounds 6 and 7 dominate).
set -e
cd "$(dirname "$0")"
B=${TMPDIR:-/tmp}/77_bin; mkdir -p "$B"
cc -O2 -o "$B/scan3" 77_scan3.c
cc -O2 -o "$B/scan4" 77_scan4.c
cc -O2 -DMEMB=3 -o "$B/scan4_m3" 77_scan4.c
/usr/bin/python3 77_q3_48.py > 77_q3_output.txt
/usr/bin/python3 77_q3_family.py >> 77_q3_output.txt
/usr/bin/python3 77_q3_pigeonhole.py >> 77_q3_output.txt
/usr/bin/python3 77_aligned_check.py >> 77_q3_output.txt
# three members, one functional per point (Q_3 at degree bound k), n = 8 and 16
: > 77_scan3_output.txt
njobs=0
# "even": 2k labelled points; "odd": 2k + 1 labelled points, same degree bound
for job in "3 4 P 1 even" "3 4 G 11 even" "4 3 P 1 even" "4 3 G 11 even" "4 4 P 1 even" "4 4 G 11 even" "4 4 H 3 even" "4 5 P 1 even" "4 5 G 11 even" "4 6 P 1 even" "4 6 G 11 even" "4 7 P 1 even" "4 7 G 11 even" "4 8 P 1 even" "4 8 G 11 even" "4 8 H 3 even" "4 4 P 1 odd" "4 4 G 11 odd" "4 5 P 1 odd" "4 5 G 11 odd" "4 6 P 1 odd" "4 6 G 11 odd" "4 7 P 1 odd" "4 7 G 11 odd"; do
  set -- $job
  ( "$B/scan3" $1 $2 $3 $4 $5 > "$B/s3_$5_$1_$2_$3.txt" 2> "$B/s3_$5_$1_$2_$3.err" ) &
  njobs=$((njobs + 1)); if [ $((njobs % 4)) -eq 0 ]; then wait; fi
done
wait
for f in "$B"/s3_*.err; do cat "$f" >> 77_scan3_output.txt; done
/usr/bin/python3 77_scan3_classify.py "$B"/s3_*_?.txt | sed "s|$B/||" >> 77_scan3_output.txt
# all deficient patterns at (4, 8): three members, then four members (four parts in parallel)
: > 77_scan4_output.txt
for kind in "P 5" "G 5" "H 9" "G 123"; do
  set -- $kind
  "$B/scan4_m3" $1 $2 0 1 > "$B/m3_$1_$2.txt" 2>> 77_scan4_output.txt
  for p in 0 1 2 3; do "$B/scan4" $1 $2 $p 4 > "$B/m4_$1_$2_$p.txt" 2>> 77_scan4_output.txt & done; wait
  cat "$B"/m4_$1_$2_?.txt > "$B/m4_$1_$2.txt"
done
/usr/bin/python3 77_scan4_summary.py "$B"/m3_*.txt "$B"/m4_P_5.txt "$B"/m4_G_5.txt "$B"/m4_H_9.txt "$B"/m4_G_123.txt | sed "s|$B/||" >> 77_scan4_output.txt
echo "--- kind P, family II and family IV orbits (pattern | orbit size, weight, ranks, flags)" >> 77_scan4_output.txt
grep -E "F 001|F 000 G . S . . NL [1-9]|F 000 G . S 0 0" "$B/m4_P_5.txt" >> 77_scan4_output.txt
echo "--- kind P, three members" >> 77_scan4_output.txt
cat "$B/m3_P_5.txt" >> 77_scan4_output.txt
