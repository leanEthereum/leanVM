#!/usr/bin/env python3
"""Note 74, Section 5: note 69's (16,32) three-member pattern whose kernel has a two-dimensional lower-factor space.
Checks: kernel dimension, rank of the level-2 flattening, and that the lower-factor space W is spanned by b, b' with
b vanishing on the three triple leaves of block 3 and b' on those of block 4."""
import sys, os, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module
g = import_module("74_gfpy")
v, r, L = 4, 1, 2; n, k = 1 << (v + r), 1 << v
rnd = random.Random(5)
tw = [[g.rand(rnd) for _ in range(n >> i)] for i in range(v)]
def row(j):
    out = [1]
    for i in range(v):
        x = tw[i][j >> i]; out = out + [g.mul(e, x) for e in out]
    return out
G = [row(j) for j in range(n)]
pat = "02 02 02 02 . . . . . . . . 012 . 012 012 012 . 012 012 01 01 01 01 01 12 12 12 012 012 012 012".split()
rows = []
for x, c in enumerate(pat):
    if c == ".": continue
    mem = [int(ch) for ch in c]; l0 = mem[0]
    for l in mem[1:]:
        rw = [0] * (L * k)
        for e in range(k):
            rw[(l - 1) * k + e] ^= G[x][e]
            if l0 >= 1: rw[(l0 - 1) * k + e] ^= G[x][e]
        rows.append(rw)
ker = g.kernel(rows, L * k)
print("weight", len(rows), "Lk", L * k, "kernel dimension", len(ker))
M = ker[0]
flat = [[M[l * k + (e << 2) + f] for f in range(4)] for l in range(L) for e in range(4)]
R, piv = g.rref(flat)
print("rank of the level-2 flattening (rows (l, e_up), columns f):", len(piv), "; level-1:", g.rank([[M[l * k + (e << 1) + f] for f in range(2)] for l in range(L) for e in range(8)]), "; level-3:", g.rank([[M[l * k + (e << 3) + f] for f in range(8)] for l in range(L) for e in range(2)]))
W = [rw for rw in R if any(rw)]
def ev(x, w): 
    s = 0
    for f in range(4): s ^= g.mul(G[x][f], w[f])
    return s
for name, leaves in (("block 3 triple leaves", [12, 14, 15]), ("block 4 triple leaves", [16, 18, 19]), ("block 6 leaves", [24, 25, 26, 27]), ("block 3 and 4 together", [12, 14, 15, 16, 18, 19])):
    print(name, ": rank of (ev_x restricted to W) =", g.rank([[ev(x, w) for w in W] for x in leaves]), "of", len(W))
