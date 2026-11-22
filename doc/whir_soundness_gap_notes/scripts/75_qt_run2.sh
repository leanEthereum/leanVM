#!/bin/sh
# Referee 75: second batch (staircases of note 74 Proposition 6.1, pattern weights of lifted three-member lists, T1 at k = 2). Run from scripts/.
B=${TMPDIR:-/tmp}/75_qt_bin
cc -O2 -o "$B" 75_qt.c || exit 1
run() { "$B" "$@"; }
{
echo "== one-sided staircases, T2 (every split level; random sub-lists of 3, 4, 5 members tested against Q_t) =="
run 3 2 2 2 O 20000 71 > ${TMPDIR:-/tmp}/75_o1.$$ & run 4 2 2 2 O 20000 72 > ${TMPDIR:-/tmp}/75_o2.$$ & run 3 3 2 2 O 20000 73 > ${TMPDIR:-/tmp}/75_o3.$$ & run 2 3 2 2 O 20000 74 > ${TMPDIR:-/tmp}/75_o4.$$ & wait
cat ${TMPDIR:-/tmp}/75_o1.$$ ${TMPDIR:-/tmp}/75_o2.$$ ${TMPDIR:-/tmp}/75_o3.$$ ${TMPDIR:-/tmp}/75_o4.$$; rm -f ${TMPDIR:-/tmp}/75_o?.$$
run 4 1 2 2 O 20000 75 > ${TMPDIR:-/tmp}/75_o1.$$ & run 5 1 2 2 O 20000 76 > ${TMPDIR:-/tmp}/75_o2.$$ & wait
cat ${TMPDIR:-/tmp}/75_o1.$$ ${TMPDIR:-/tmp}/75_o2.$$; rm -f ${TMPDIR:-/tmp}/75_o?.$$
echo "== lifted three-member lists, T2: pattern weight against 5k/2 - 2 =="
run 2 2 2 2 F 50000 81 & run 3 2 2 2 F 50000 82 & run 3 3 2 2 F 30000 83 & run 4 1 2 2 F 20000 84 & wait
run 4 2 2 2 F 20000 85 & run 3 1 2 2 F 50000 86 & wait
echo "== T1 at k = 2, exhaustive: five lines on n = 8, four lines on n = 16 =="
run 1 2 4 1 E 0 9 | tail -1 & run 1 3 3 1 E 0 9 | tail -1 & wait
echo "== T1, three members (Q_3): sampled and lifted =="
run 2 3 2 1 S 300000 91 & run 3 3 2 1 S 200000 92 & run 4 2 2 1 S 60000 93 & run 2 4 2 1 S 200000 94 & wait
run 3 2 2 1 F 50000 95 & run 2 3 2 1 F 50000 96 & run 4 2 2 1 F 20000 97 & run 3 3 2 1 F 30000 98 & wait
} > 75_qt_output2.txt 2>&1
