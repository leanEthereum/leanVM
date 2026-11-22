#!/bin/sh
# Referee 80: exact-rank tests of note 76's Theorem 4.1 and Corollaries 4.2, 4.3 (writes 80_match_output.txt; about two minutes, one core)
cd "$(dirname "$0")" || exit 1
mkdir -p 80_bin
cc -O2 -o 80_bin/match 80_match.c || exit 1
{
  for variant in 2 1; do
    for m in 3 4 5 6; do ./80_bin/match 3 $m $variant 3000 $((10 * variant + m)); done
    for m in 3 4 5 6; do ./80_bin/match 4 $m $variant 2000 $((100 * variant + m)); done
    ./80_bin/match 2 3 $variant 3000 7; ./80_bin/match 2 4 $variant 3000 8; ./80_bin/match 1 4 $variant 2000 9
  done
} > 80_match_output.txt 2>&1
