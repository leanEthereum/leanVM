#!/bin/sh
# Referee 87: the counterexamples to (C*) and (C') of note 82 and the exhaustive checks (87_cstar.c); about four minutes.
cd "$(dirname "$0")" && mkdir -p 87_bin && cc -O2 -o 87_bin/87_cstar 87_cstar.c || exit 1
C=87_bin/87_cstar
S1="012 012 012 012 012 012 012 . 02 02 02 02 01 01 01 01 . . 01 . . . . . 012 . 012 . 12 12 12 012"
S2=". . . . . 012 012 012 . . . . 02 02 02 02 12 12 12 12 . 012 . 012 01 01 01 01 012 012 012 012"
SA="012 012 012 012 012 012 012 . 02 02 02 02 01 01 01 01 . . . . . . . . 012 . 012 . 12 12 12 12"
{
echo "== exhaustive checks"
$C exh 2 3 31; $C exh 1 4 32
echo "== counterexamples, three members at (16,32): min over all binary Q inside Q* (exhaustive), two draws each"
for s in 401 402; do for P in "$S1" "$S2" "$SA"; do $C minq 1 4 3 "$P" $s; done; done
echo "== chain of binary full parts of the reduced counterexample"
$C chain 1 4 3 "$SA" 77
echo "== failures of (C*) with five and six members at (8,16), and their saturations"
$C minq 1 3 5 "01 01234 34 34 03 03 23 01234 14 14 01234 01234 04 01234 24 24" 301
$C minq 1 3 5 "02 01234 14 14 0134 01234 23 23 01 01 01234 34 01234 04 13 13" 302
$C minq 1 3 5 "12 01234 13 13 24 24 34 01234 01234 01 14 14 01234 01234 02 02" 303
$C minq 1 3 6 "15 15 012345 012345 12 12 012345 25 02 02 012345 13 23 23 012345 014" 304
echo "== note 82's own program on the three-member counterexamples (if 82_bin/82_big is present)"
if [ -x 82_bin/82_big ]; then for P in "$S1" "$S2" "$SA"; do echo "x | $P" > 87_bin/tmp_pat.txt; VERBOSE=1 82_bin/82_big file 4 1 3 87_bin/tmp_pat.txt | tail -2; done; fi
echo "== a larger search, three members at (16,32), mode lift"
$C search 4 3 lift 1500000 991
} > 87_cstar_extra_output.txt 2>&1
