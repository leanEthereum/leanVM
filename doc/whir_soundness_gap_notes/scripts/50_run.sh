#!/bin/sh
# 50_run.sh: regenerates 50_results.txt (run inside scripts/; about 5 minutes on 4 cores).
# Usage: sh 50_run.sh
set -e
T=$(mktemp -d)
{
  echo "=== 50_parity.py A B C ==="
  python3 50_parity.py A B C
  echo
  echo "=== 50_local.py ==="
  python3 50_local.py
  echo
  echo "=== 50_window.py 1 3 4 5 6 ==="
  python3 50_window.py 1 3 4 5 6
} > "$T/a.txt" 2>&1 &
{ echo "=== 50_parity.py D ==="; python3 50_parity.py D; echo; echo "=== 50_window.py 2 ==="; python3 50_window.py 2; } > "$T/b.txt" 2>&1 &
run() { python3 50_lattice.py "$@" | grep -v "successive minima found"; echo; }
{
  for w in rand fam plant:3; do
    for bj in "2 2" "2 3" "3 2" "3 3" "2 4"; do run 4 $bj word=$w; done
  done
  run 4 4 3 word=rand
  run 4 2 2 word=rand dom=pts
  run 4 2 3 word=rand dom=pts
  run 4 2 3 word=rand x=0.75 jrest=0
  run 4 2 3 word=rand x=0.75 jrest=1
  run 4 2 3 word=rand x=0.75 jrest=2
  run 4 2 4 word=rand x=0.5 jrest=3
  run 4 2 4 word=fam x=0.5 jrest=3
  run 4 2 2 word=two
  run 4 2 3 word=two
} > "$T/c.txt" 2>&1 &
{
  for w in rand fam plant:6; do
    for bj in "2 2" "2 3" "3 2"; do run 5 $bj word=$w; done
  done
  run 5 2 2 word=rand dom=pts
  run 5 2 2 word=two
  run 5 3 3 word=fam
  run 5 3 3 word=rand
  run 6 2 2 word=rand
  run 6 2 2 word=fam
} > "$T/d.txt" 2>&1 &
wait
{
  cat "$T/a.txt"
  echo
  cat "$T/b.txt"
  echo
  echo "=== 50_lattice.py, n = 16 ==="
  cat "$T/c.txt"
  echo "=== 50_lattice.py, n = 32, 64 ==="
  cat "$T/d.txt"
} > 50_results.txt
rm -r "$T"
echo "wrote 50_results.txt"
