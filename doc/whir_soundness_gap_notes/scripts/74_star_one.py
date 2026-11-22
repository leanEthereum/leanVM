#!/usr/bin/env python3
"""Note 74: one instance of the one-level system sum U_i (x) (1,t_i), U_i given by 0/1 basis vectors.
Prints rank, relation dimension, the hull of the relation components (dims and whether F_2-rational), Phi(hull),
and the same for the sub-system formed by the hulls. usage: 74_star_one.py 'v1,v2;v3,...' (bit strings; ';' separates subspaces)"""
import sys, random
from importlib import import_module
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
g = import_module("74_gfpy")
def analyse(U, N, rnd, label, nsamp=8):
    m = len(U); W = sum(len(u) for u in U); off = [0]
    for u in U: off.append(off[-1] + len(u))
    hull = [[] for _ in U]; rk = None
    for s in range(nsamp):
        t = [g.rand(rnd) for _ in U]
        rows = [[x for x in b] + [g.mul(t[i], x) for x in b] for i, u in enumerate(U) for b in u]
        At = [[rows[a][c] for a in range(W)] for c in range(2 * N)]
        ker = g.kernel(At, W); rk = W - len(ker)
        for i in range(m):
            for kv in ker: hull[i].append(kv[off[i]:off[i + 1]])
    hb = []; drop = 0; up = []
    for i, u in enumerate(U):
        R, piv = g.rref(hull[i]) if hull[i] else ([], [])
        R = [r for r in R if any(r)]
        hb.append(R); drop += len(u) - len(R)
        for r in R:
            up.append([__import__("functools").reduce(lambda a, b: a ^ b, [g.mul(r[a], u[a][c]) for a in range(len(u))], 0) for c in range(N)])
    du = g.rank(up) if up else 0
    rational = all(all(x in (0, 1) for x in r) for R in hb for r in R)
    print(f"[{label}] N={N} dims={[len(u) for u in U]} W={W} rank={rk} relations={W - rk} dim(sum U)={g.rank([b for u in U for b in u])} hull dims={[len(R) for R in hb]} F2-rational={rational} dim(sum hull)={du} Phi(hull)={2 * du + drop}")
    newU = []
    for i, u in enumerate(U):
        newU.append([[__import__("functools").reduce(lambda a, b: a ^ b, [g.mul(r[a], u[a][c]) for a in range(len(u))], 0) for c in range(N)] for r in hb[i]])
    return newU, rational
spec = sys.argv[1]
U = [[[int(ch) for ch in vec] for vec in part.split(",")] for part in spec.split(";")]
N = len(U[0][0]); rnd = random.Random(7)
sub, rat = analyse(U, N, rnd, "full system")
sub = [u for u in sub if u]
if sub: sub2, _ = analyse(sub, N, rnd, "sub-system of the hulls")
