#!/bin/sh
# Referee 87: checks of note 82 (87_cstar.c). Four streams in parallel, about ten minutes.
cd "$(dirname "$0")" && mkdir -p 87_bin && cc -O2 -o 87_bin/87_cstar 87_cstar.c || exit 1
C=87_bin/87_cstar
{
$C selftest; $C atom 5; $C lift 11
$C chain 2 3 6 "012 012 012 012 | 03 03 14 14 | 23 15 23 15 | 05 24 24 05 | 345 345 345 345 | 012345 . . . | . 012345 . . | . . 012345 ." 21
$C chain 1 2 3 ". 012 | 12 12 | 02 02 | 01 01" 22
$C chain 1 3 3 "02 02 012 012 . . . 012 . 012 012 . 12 12 01 01" 23
} > 87_bin/cstar_0.txt 2>&1
stream() { # members
  m=$1
  $C search 3 $m full 2000000 ${m}01; $C search 3 $m lift 2000000 ${m}02; $C climb 3 $m 300000 ${m}03
  $C search 4 $m full 300000 ${m}04; $C search 4 $m lift 300000 ${m}05; $C climb 4 $m 25000 ${m}06
}
for m in 3 4 5 6; do stream $m > 87_bin/cstar_$m.txt 2>&1 & done
wait
cat 87_bin/cstar_0.txt 87_bin/cstar_3.txt 87_bin/cstar_4.txt 87_bin/cstar_5.txt 87_bin/cstar_6.txt > 87_cstar_output.txt
