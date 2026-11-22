#!/bin/sh
# usage: 02_climb_run.sh <lists-binary> <outdir> <steps> <N> "<k T>" ["<k T>" ...]
# Annealing searches for general lists (degree < k, agreement >= T) at n = 2^N on the leanVM-shaped domain
# (pow: span of 1, x, ..., x^(N-1)) and on a random domain (rnd: random basis, seed 21) in GF(2^64), three seeds
# each, four processes at a time. One output file per (domain, k, T, seed): "best <list size> : <word>".
bin=$1; out=$2; steps=$3; N=$4; shift 4
gen() { python3 -c "
import random, sys
N = $N
r = random.Random(21); b = [r.getrandbits(64) for _ in range(N)] if '$1' == 'rnd' else [1 << i for i in range(N)]
p = [0]
for x in b: p += [y ^ x for y in p]
print(' '.join('%x' % y for y in p))"; }
for dom in pow rnd; do
  pts=$(gen $dom)
  for cfg in "$@"; do
    for seed in 1 2 3; do
      echo "$dom $cfg $seed $pts"
    done
  done
done | xargs -P 4 -L 1 sh -c 'dom=$0; k=$1; T=$2; seed=$3; shift 3; echo "$@" | '"$bin"' climb 64 1b '"$((1 << N))"' $k $T '"$steps"' $seed > '"$out"'/climb'"$N"'_${dom}_${k}_${T}_${seed}.txt'
