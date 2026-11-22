#!/bin/sh
# Researcher 10: builds 10_deep_redteam.c into a temporary directory and runs the experiments of note 10.
# Usage: sh 10_run.sh [all|A|B|C|D|E|A1|..|A7|B1|..|B4]   (default all; each item is under ten minutes, at most 4 threads)
set -e
here=$(cd "$(dirname "$0")" && pwd)
bin=${TMPDIR:-/tmp}/deep10_$$
cc -O2 -o "$bin" "$here/10_deep_redteam.c" -lpthread
trap 'rm -f "$bin"' EXIT
run() { "$bin" "$@" | grep -v '^  points ('; }
sec=${1:-all}
want() { [ "$sec" = all ] || [ "$sec" = "$1" ] || [ "$sec" = "$(echo "$1" | cut -c1)" ]; }


case $sec in all | A*) echo "#### A. Structure: lists of all folds, dependency classes, exact maximum over all answer vectors" ;; esac
if want A1; then
  echo "## A1. GF(2^6), n = 16, rate 1/4, generic points (outside D, distinct, not the pole)"
  for w in random planted0 planted1 planted2 pole poleflat; do run m=6 N=4 d=3 A=6 word=$w check=20 s=4 trials=40 pmode=1 quiet=1; done
  run m=6 N=4 d=3 A=6 word=flatlist check=20 s=3 smin=2 trials=5 pmode=1 floor=63 quiet=1
fi
if want A2; then
  echo "## A2. the same, uniform points (the distribution of Theorem 3)"
  for w in random planted1 planted2 pole poleflat; do run m=6 N=4 d=3 A=6 word=$w s=4 smin=2 trials=300 pmode=0 floor=63 quiet=1; done
fi
if want A3; then
  echo "## A3. GF(2^6), n = 16, rate 1/2 (d = 7, A = 10, below Johnson)"
  for w in random planted1 planted2 pole; do run m=6 N=4 d=7 A=10 word=$w check=5 s=4 trials=40 pmode=1 quiet=1; done
fi
if want A4; then
  echo "## A4. GF(2^8), n = 32, rate 1/4 (d = 7, A = 12, Johnson 14.97)"
  for w in random planted1 planted2 pole poleflat; do run m=8 N=5 d=7 A=12 word=$w s=3 smin=2 trials=10 pmode=1 floor=255 anchors=300 quiet=1; done
fi
if want A5; then
  echo "## A5. GF(2^8), n = 32, rate 1/8 (d = 3, A = 8): pole pair over x^8, 620 flats of size 8"
  run m=8 N=5 d=3 A=8 word=poleflat s=4 smin=2 trials=3 pmode=1 floor=255 anchors=200 quiet=1
fi
if want A6; then
  echo "## A6. GF(2^6), n = 32, rate 1/2 (d = 15, A = 20 = 5n/8): pole pair over the word x^16 L_W of note 05"
  run m=6 N=5 d=15 A=20 word=five8 s=5 smin=2 trials=6 pmode=1 floor=63 anchors=200 quiet=1
fi
if want A7; then
  echo "## A7. two lanes per half (H = 2), GF(2^6), n = 16"
  for w in random planted0 planted1 planted2 pole poleflat; do run m=6 N=4 d=3 A=6 H=2 word=$w check=5 s=4 smin=2 trials=20 pmode=1 floor=63 quiet=1; done
fi

case $sec in all | B*) echo "#### B. Corollary 4: exact maximum over all answer vectors and all round messages (running claim included)" ;; esac
if want B1; then
  echo "## B1. GF(2^6), n = 16 (C(n,2) = 120 <= 2q = 128, the hypothesis of Corollary 4 holds)"
  for w in planted0 planted1 flatlist pole poleflat random; do run m=6 N=4 d=3 A=6 word=$w mode=tables s=2 trials=3 pmode=1 minc=32 maxcells=60; done
fi
if want B2; then
  echo "## B2. GF(2^5), two lanes per half"
  for w in planted0 flatlist pole; do run m=5 N=4 d=3 A=6 H=2 word=$w mode=tables s=2 trials=3 pmode=1 minc=8 maxcells=200; done
fi
if want B3; then
  echo "## B3. two pairs of L_pair that differ by a multiple of R: generic points, then the roots of R"
  run m=6 N=4 d=3 A=6 word=twopairs mode=tables s=2 trials=2 pmode=1 minc=32 maxcells=60 nopoints=0
  run m=6 N=4 d=3 A=6 word=twopairs mode=tables s=2 trials=1 pmode=2 minc=32 maxcells=60 nopoints=0
fi
if want B4; then
  echo "## B4. GF(2^7), n = 16: one list member with a false claim"
  run m=7 N=4 d=3 A=6 word=planted0 mode=tables s=2 trials=1 pmode=1 minc=64 maxcells=4 nopoints=0
fi

if want C; then
  echo "#### C. The probability bound where it is not vacuous: GF(2^8) and GF(2^7), n = 16, d = 3, uniform points"
  for w in random planted2 pole poleflat; do run m=8 N=4 d=3 A=6 word=$w s=4 smin=2 trials=20000 pmode=0 floor=255 quiet=1; done
  for w in pole poleflat; do run m=7 N=4 d=3 A=6 word=$w s=4 smin=2 trials=20000 pmode=0 floor=127 quiet=1; done
fi

if want D; then
  echo "#### D. An explicit exceptional point tuple: pole family C_i = C_0 + R H_i, points at the roots of R, then generic points"
  "$bin" m=8 N=5 d=5 A=10 word=polerh s=3 smin=2 trials=2 pmode=2 floor=255 anchors=200
  run m=8 N=5 d=5 A=10 word=polerh s=3 smin=2 trials=20 pmode=1 floor=255 anchors=200 quiet=1
fi

if want E; then
  echo "#### E. Two fold rounds of a 4-lane word with the same points (variant P)"
  for w in random planted1 planted2 pole poleflat; do "$bin" m=5 N=4 d=3 A=6 word=$w mode=nested s=3 trials=2; done
  for w in random planted2 poleflat; do "$bin" m=6 N=4 d=3 A=6 word=$w mode=nested s=3 trials=1 nc1=500; done
fi
