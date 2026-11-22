#!/bin/sh
# Researcher 15: builds 15_nesting.c (which includes 10_deep_redteam.c) into a temporary directory and runs the
# experiments of note 15. Usage: sh 15_run.sh [all|A1|A2|A3|A4|B|C|D|E]   (each item under ten minutes, one thread)
set -e
here=$(cd "$(dirname "$0")" && pwd)
bin=${TMPDIR:-/tmp}/nest15_$$
cc -O2 -Wall -Wextra -o "$bin" "$here/15_nesting.c" -lpthread
trap 'rm -f "$bin"' EXIT
sec=${1:-all}
want() { [ "$sec" = all ] || [ "$sec" = "$1" ]; }

if want A1; then
  echo "#### A1. Construction N1, two members, GF(2^5), n = 16, d = 3, A = 6: every first challenge"
  echo "## three generic points"
  "$bin" m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=generic cor=2 trials=2
  echo "## one point at a root of R0, two generic"
  "$bin" m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=roots1 cor=2 trials=2
  echo "## two points at the roots of R0, one generic"
  "$bin" m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=roots cor=3
  "$bin" m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=roots cor=3 seed=2
fi
if want A2; then
  echo "#### A2. The same over GF(2^6): every first challenge, two points at the roots of R0; then one fresh point after c1"
  "$bin" m=6 N=4 d=3 A=6 word=n1 M=2 r=2 mode=scan s=3 pts=roots cor=3 fresh=1
fi
if want A3; then
  echo "#### A3. N1 with four members (six pairs, six lines), GF(2^6), n = 32, d = 3, A = 8"
  echo "## K0 = 2.72 q: four members that share s - 1 answers give four lines to one answer vector, for every c1"
  "$bin" m=6 N=5 d=3 A=8 word=n1 M=4 r=2 mode=scan s=3 pts=roots nc1=3 cor=0
  echo "## K0 = 4.72 q (so that four lines do not count): 12 first challenges from the predicted lines, 8 uniform"
  "$bin" m=6 N=5 d=3 A=8 word=n1 M=4 r=2 mode=scan s=3 pts=roots nc1=8 online=12 cor=2 k0=4.72
fi
if want A4; then
  echo "#### A4. A flats family (note 01): GF(2^6), n = 16, d = 4, A = 7, lanes mu x^7 and G + x^7; two points in D"
  "$bin" m=6 N=4 d=4 A=7 word=flat4 mode=scan s=3 pts=roots nc1=6 online=6 cor=1 k0=8.72
fi
if want B; then
  echo "#### B. The collision predicate of N1 over all point tuples and all first challenges: is Markov tight?"
  "$bin" m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=alg s=2
  "$bin" m=5 N=4 d=3 A=6 word=n1 M=2 r=2 mode=alg s=3
  "$bin" m=6 N=4 d=3 A=6 word=n1 M=2 r=2 mode=alg s=3
  "$bin" m=6 N=5 d=3 A=8 word=n1 M=4 r=2 mode=alg s=3
fi
if want C; then
  echo "#### C. The red team's nested words (note 10, section 5.5) with the stronger test: GF(2^5), every first challenge"
  for w in random planted1 planted2 pole poleflat; do "$bin" m=5 N=4 d=3 A=6 word=$w mode=scan s=3 pts=generic cor=1; done
  echo "## uniform points (half of GF(2^5) is D here)"
  for w in random pole poleflat; do "$bin" m=5 N=4 d=3 A=6 word=$w mode=scan s=3 pts=uniform trials=3 cor=0; done
fi
if want D; then
  echo "#### D. Depth two: an 8-lane word, one point at the root, two generic points"
  "$bin" m=5 N=4 d=3 A=6 word=n2 mode=scan2 s=3 ns=40
  "$bin" m=5 N=4 d=3 A=6 word=n2 mode=scan2 s=3 ns=40 seed=3
fi
if want E; then
  echo "#### E. Schedules (Lemma S) and the completeness of batches introduced in the middle of a level"
  python3 "$here/15_schedules.py" selftest
  python3 "$here/15_schedules.py"
  python3 "$here/15_batch_toy.py"
fi
