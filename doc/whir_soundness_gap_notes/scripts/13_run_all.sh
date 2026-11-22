#!/bin/bash
# Researcher 13. Builds the 13_* programs into a scratch directory (argument 1, default a fresh temporary directory)
# and reruns every experiment of 13-real-domain.md. Nothing is written inside the repository.
# Total about 30 minutes on four cores; the largest run (N = 25 in GF(2^64)) needs about 16 GB of memory.
# usage: 13_run_all.sh [builddir] [quick]      (quick: skip the N = 25 runs and the n = 32 batch)
set -e
here=$(cd "$(dirname "$0")" && pwd)
W=${1:-$(mktemp -d)}
quick=$2
mkdir -p "$W"
for p in planes class58; do cc -O2 -mcpu=native -I"$here" -o "$W/$p" "$here/13_$p.c"; done
cc -O2 -mcpu=native -I"$here" -o "$W/ct32" "$here/13_ct32.c" -lpthread

echo "== checks (Lemma 2.1, Proposition 3.1, Witt criterion 3.3)"
"$W/class58" 8 power random:3 64 0x1b -n 3 -check
"$W/class58" 9 power high 23 0x21 -check
python3 "$here/13_sparse_key_check.py"

# scaled real shape: m about 2.56 N, lowest irreducible modulus of that degree (13_irred.py)
scaled="8 20 0x9;9 23 0x21;10 26 0x1b;11 28 0x3;12 31 0x9;13 33 0x4b;14 36 0x35;15 38 0x63;16 41 0x9"
echo "== section 4.2: planes and 3-spaces of the dual space, scaled real shape"
IFS=';'; for cfg in $scaled; do IFS=' '; set -- $cfg
  "$W/planes" $1 iota2 power $2 $3; "$W/planes" $1 pi2 power $2 $3
  if [ $1 -le 12 ]; then "$W/planes" $1 iota3 power $2 $3; fi
  if [ $1 -le 11 ]; then "$W/planes" $1 aff2 power $2 $3; fi
done
"$W/planes" 11 iota3 power 16 0x2b; "$W/planes" 11 iota3 random:1 16 0x2b; "$W/planes" 12 iota3 power 20 0x9
echo "== section 4.3: structural coincidences (real field, then two moduli)"
for N in 6 8 10 12 14 16; do "$W/planes" $N iota2 power 64 0x1b -v; "$W/planes" $N pi2 power 64 0x1b; done
for N in 8 10 12; do "$W/planes" $N iota3 power 64 0x1b; done
for N in 8 10 11; do "$W/planes" $N aff2 power 64 0x1b; done
for st in iota2 pi2 iota3; do "$W/planes" 12 $st power 64 0x1b 64 0x1d; done
"$W/planes" 10 aff2 power 64 0x1b 64 0x1d

echo "== section 4.1: fibres of e_{n/8} on the 5n/8 class, scaled real shape"
counts="2000 2000 2000 2000 1000 1000 600 400 300"
i=0; IFS=';'; for cfg in $scaled; do IFS=' '; set -- $cfg; i=$((i+1)); cnt=$(echo $counts | cut -d' ' -f$i)
  "$W/class58" $1 power random:1000 $2 $3 -n $cnt -q
  "$W/class58" $1 power low $2 $3 -q; "$W/class58" $1 power high $2 $3 -q
done
for cfg in "17 44 0x21 150" "18 46 0x3 100" "19 49 0x71 50" "20 51 0x4b 30"; do set -- $cfg
  "$W/class58" $1 power random:1000 $2 $3 -n $4 -q; "$W/class58" $1 power low $2 $3 -q
done
for N in 8 12 16 20; do "$W/class58" $N power low 64 0x1b 64 0x1d -q; "$W/class58" $N power random:7 64 0x1b 64 0x1d -q -n 3; done
if [ -z "$quick" ]; then
  echo "== section 4.1: the real domain, N = 25, K = GF(2^64)"
  "$W/class58" 25 power low 64 0x1b; "$W/class58" 25 power high 64 0x1b
  "$W/class58" 25 power random:1 64 0x1b -n 16
  echo "== section 4.4: exhaustive n = 32"
  for tg in "12 4" "11 5" "10 6" "9 5" "11 7" "5 3" "6 4" "7 5"; do set -- $tg
    "$W/ct32" $1 $2 random:1 64 0x1b 64 0x1d; "$W/ct32" $1 $2 power 64 0x1b
    for cfg in "13 0x1b" "16 0x2b" "20 0x9" "26 0x1b"; do set -- $cfg; "$W/ct32" ${tg% *} ${tg#* } power $1 $2; "$W/ct32" ${tg% *} ${tg#* } random:1 $1 $2; done
  done
  for T in 11 10 9; do "$W/ct32" $T 3 random:1 64 0x1b 64 0x1d; done
fi
