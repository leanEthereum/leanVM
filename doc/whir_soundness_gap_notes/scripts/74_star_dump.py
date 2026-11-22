#!/usr/bin/env python3
"""Note 74: dump the sub-system of hulls of an instance (F_2-rational case) and its incidence data."""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module
g = import_module("74_gfpy")
spec = sys.argv[1]
U = [[[int(ch) for ch in vec] for vec in part.split(",")] for part in spec.split(";")]
N = len(U[0][0]); rnd = random.Random(7); W = sum(len(u) for u in U)
off = [0]
for u in U: off.append(off[-1] + len(u))
hull = [[] for _ in U]
for s in range(8):
    t = [g.rand(rnd) for _ in U]
    rows = [[x for x in b] + [g.mul(t[i], x) for x in b] for i, u in enumerate(U) for b in u]
    At = [[rows[a][c] for a in range(W)] for c in range(2 * N)]
    for kv in g.kernel(At, W):
        for i in range(len(U)): hull[i].append(kv[off[i]:off[i + 1]])
sub = []
for i, u in enumerate(U):
    R = [r for r in g.rref(hull[i])[0] if any(r)]
    sub.append([[sum(r[a] * u[a][c] for a in range(len(u))) % 2 for c in range(N)] for r in R])
def f2rank(vs):
    vs = [int("".join(map(str, v)), 2) for v in vs]; r = 0; basis = []
    for v in vs:
        for b in basis: v = min(v, v ^ b)
        if v: basis.append(v); r += 1
    return r
for i, u in enumerate(sub): print(f"H_{i}:", " ".join("".join(map(str, v)) for v in u))
print("dim sum all:", f2rank([v for u in sub for v in u]))
for a, b in itertools.combinations(range(len(sub)), 2): print(f"dim(H_{a}+H_{b}) = {f2rank(sub[a] + sub[b])}", end="; ")
print()
for c in itertools.combinations(range(len(sub)), 3): print(f"dim sum {c} = {f2rank([v for i in c for v in sub[i]])}", end="; ")
print()
for c in itertools.combinations(range(len(sub)), 4): print(f"dim sum {c} = {f2rank([v for i in c for v in sub[i]])}", end="; ")
print()
