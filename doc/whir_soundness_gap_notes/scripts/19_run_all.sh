#!/bin/sh
# Researcher 19. Rebuilds and reruns every check of note 19. usage: 19_run_all.sh [builddir]
# About 4 minutes on four cores, 3 GB. Binaries and outputs go to builddir (default: a temporary directory).
set -e
here=$(cd "$(dirname "$0")" && pwd)
B=${1:-$(mktemp -d)}
cc -O2 -mcpu=native -o "$B/19_ct32" "$here/19_ct32.c"
python3 "$here/19_dual_check.py" all
python3 "$here/19_real_pair.py" 8 9 25 26 27 28
python3 "$here/19_real_pair.py" 25 28 --field 64 0x1d
run() { "$B/19_ct32" "$@"; }
( run 10 6 5 0x5 1; run 10 6 6 0x3 1; run 10 6 6 0x3 2; run 10 6 7 0x3 1; run 10 6 8 0x1b 1; run 9 6 5 0x5 1; run 9 6 6 0x3 1 ) > "$B/o1.txt" &
( run 11 5 6 0x3 1; run 11 5 8 0x1b 1; run 11 5 7 0x3 0 ) > "$B/o2.txt" &
( run 11 7 6 0x3 1; run 11 7 8 0x1b 1; run 11 6 6 0x3 1; run 9 5 6 0x3 1; run 9 5 8 0x1b 0 ) > "$B/o3.txt" &
( run 6 4 5 0x5 1; run 6 4 6 0x3 1; run 6 5 6 0x3 3; run 7 4 5 0x5 1; run 7 5 6 0x3 1; run 7 4 8 0x1b 1; run 8 4 6 0x3 1; run 8 6 6 0x3 1; run 12 6 6 0x3 1 ) > "$B/o4.txt" &
wait
cat "$B/o1.txt" "$B/o2.txt" "$B/o3.txt" "$B/o4.txt"
if grep -q FAILED "$B"/o?.txt; then echo "SOME CHECK FAILED"; exit 1; fi
echo "all checks passed"
