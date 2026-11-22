#!/bin/sh
# Referee 52: regenerates 52_results.txt. Run inside scripts/. Optional argument: a build directory for the two
# C tools (default: a temporary directory). About 3 minutes on one core.
set -e
B="${1:-$(mktemp -d)}"
mkdir -p "$B"
cc -O2 -o "$B/52_even" 52_even.c
cc -O2 -o "$B/52_list" 52_list.c
{
  echo "### 52_ranks.py (exact local ranks over prime fields)"
  python3 52_ranks.py
  echo
  echo "### 52_thresholds.py (exact integers)"
  python3 52_thresholds.py
  echo
  echo "### 52_toy.py (GF(2^8), GF(2^10), GF(2^12); linear algebra by 52_even.c, lists by 52_list.c)"
  python3 52_toy.py "$B" rank flat gold slack r16 f4 pencil half half22
} > 52_results.txt 2>&1
echo "wrote 52_results.txt"
