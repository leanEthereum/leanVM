"""Describe dumped common-top classes (from 02_ct32 with dump = 1): for each member S (a mask over F_2^N, point i is
the vector i) report its period group {w : S + w = S}, the dimension of its affine span, and how the class is spread.

usage: python3 02_class_structure.py <dumpfile> [N]
"""
import sys
from collections import Counter

N = int(sys.argv[2]) if len(sys.argv) > 2 else 5
n = 1 << N


def pts(mask):
    return [i for i in range(n) if mask >> i & 1]


def periods(mask):
    P = pts(mask)
    s = set(P)
    return [w for w in range(n) if all((p ^ w) in s for p in P)]


def rank(vs):
    piv = {}
    for v in vs:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    return len(piv)


def affdim(mask):
    P = pts(mask)
    return rank([p ^ P[0] for p in P[1:]])


for line in open(sys.argv[1]):
    if not line.startswith("dump"):
        continue
    head, rest = line.split(":")
    masks = [int(x, 16) for x in rest.split()]
    if len(masks) < 2:
        continue
    per = Counter()
    ad = Counter()
    pergroups = Counter()
    for mk in masks:
        pg = periods(mk)
        per[len(pg)] += 1
        pergroups[tuple(pg)] += 1
        ad[affdim(mk)] += 1
    inter = masks[0]
    union = 0
    for mk in masks:
        inter &= mk
        union |= mk
    # pairwise intersection sizes
    isz = Counter()
    if len(masks) <= 3000:
        for i in range(len(masks)):
            for j in range(i):
                isz[bin(masks[i] & masks[j]).count("1")] += 1
    print(f"{head}: size {len(masks)}; period-group sizes {dict(per)}; distinct period groups {len(pergroups)};"
          f" affine-span dims {dict(ad)}; common points {bin(inter).count('1')}; covered points {bin(union).count('1')};"
          f" pairwise intersections {dict(sorted(isz.items()))}")
