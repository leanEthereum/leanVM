#!/bin/sh
# Referee 75: regenerates 75_toy_output.txt (about nine minutes on four cores). Run from scripts/.
B=${TMPDIR:-/tmp}/75_toy_bin
cc -O2 -o "$B" 75_toy.c || exit 1
{ "$B" 1 3 2 1 200000 1 & "$B" 1 3 2 2 200000 2 & "$B" 1 3 1 1 200000 3 & "$B" 1 3 1 2 200000 4 & wait
  "$B" 2 2 1 1 2000000 5 & "$B" 2 2 1 2 2000000 6 & wait; } > 75_toy_output.txt 2>&1
