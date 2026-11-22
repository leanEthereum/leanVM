#!/bin/sh
# Referee 75: regenerates 75_qt_output.txt (about ten minutes on four cores). Run from scripts/.
B=${TMPDIR:-/tmp}/75_qt_bin
cc -O2 -o "$B" 75_qt.c || exit 1
run() { "$B" "$@"; }
{
echo "== exhaustive, T2 =="
run 1 2 3 2 E 0 1 & run 1 3 3 2 E 0 2 & run 2 2 2 2 E 0 3 & run 1 2 4 2 E 0 4 & wait
echo "== exhaustive, T1 =="
run 1 2 3 1 E 0 1 & run 2 2 2 1 E 0 3 & run 2 1 2 1 E 0 5 & wait
echo "== sampled, T2, three members =="
run 2 2 2 2 S 600000 11 & run 2 3 2 2 S 600000 12 & run 2 4 2 2 S 400000 13 & run 3 2 2 2 S 400000 14 & wait
run 3 3 2 2 S 300000 15 & run 3 1 2 2 S 400000 16 & run 4 1 2 2 S 100000 17 & run 4 2 2 2 S 60000 18 & wait
echo "== sampled, T2, four members =="
run 2 2 3 2 S 600000 21 & run 2 3 3 2 S 600000 22 & run 2 4 3 2 S 400000 23 & run 3 2 3 2 S 300000 24 & wait
run 3 3 3 2 S 200000 25 & run 3 1 3 2 S 300000 26 & run 1 3 3 2 S 600000 27 & run 2 3 4 2 S 300000 28 & wait
echo "== lifted lists, T2 =="
run 2 2 2 2 F 100000 31 & run 2 3 2 2 F 100000 32 & run 3 2 2 2 F 100000 33 & run 3 3 2 2 F 50000 34 & wait
run 2 2 3 2 F 100000 35 & run 2 3 3 2 F 100000 36 & run 3 2 3 2 F 100000 37 & run 3 3 3 2 F 50000 38 & wait
run 2 4 3 2 F 50000 39 & run 4 2 3 2 F 20000 40 & run 3 2 4 2 F 50000 41 & run 4 1 3 2 F 20000 42 & wait
echo "== T1: sampled and lifted =="
run 2 2 3 1 S 300000 51 & run 2 1 3 1 S 300000 52 & run 3 1 2 1 S 300000 53 & run 3 1 3 1 S 300000 54 & wait
run 2 2 3 1 F 50000 55 & run 3 2 3 1 F 50000 56 & run 2 2 2 1 S 300000 57 & run 3 2 2 1 S 300000 58 & wait
} > 75_qt_output.txt 2>&1
