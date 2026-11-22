#!/bin/bash
# 55_run.sh: all computations of 55-referee-note-53.md. The binary goes to a build directory outside the
# repository (first argument, default ${TMPDIR:-/tmp}/r55). About 2 minutes on one core and 2 GB of memory
# (4 minutes and 3 GB with "full", which adds c = 11 to the exhaustive search).
#   bash 55_run.sh [builddir] [full] > 55_results.txt
set -e
B=${1:-${TMPDIR:-/tmp}/r55}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$B"
cc -O2 -o "$B/55_pencils" "$here/55_pencils.c"
cd "$here"
echo "===== 55_identity.py"
python3 55_identity.py
echo "===== 55_planted.py"
python3 55_planted.py
echo "===== 55_goppa.py"
python3 55_goppa.py
echo "===== 55_strata.py"
python3 55_strata.py
echo "===== 55_gap.py"
python3 55_gap.py
echo "===== 55_window.py"
python3 55_window.py
echo "===== 55_pencils (field self test, then the exhaustive search at N = 5)"
"$B/55_pencils" 4 1 selftest
cs="4 5 6 7 8 9 10"
if [ "$2" = "full" ]; then cs="$cs 11"; fi
for c in $cs; do
  "$B/55_pencils" "$c" 1
done
