#!/usr/bin/env python3
"""Note 74: the counterexample to Theorem 2.5 for arbitrary subspaces is Segre's five associated lines in P^4.
(1) Pluecker rank of the five planes found by 74_star (over F_2). (2) A generic construction over GF(2^64): four random
planes of K^5 and the fifth associated one (the fifth decomposable point of the span of the four Pluecker vectors), then the
rank of sum U_i (x) (1,t_i) for random t (10 generators in dimension 10). (3) Control: five random planes."""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from importlib import import_module
g = import_module("74_gfpy")
pairs = list(itertools.combinations(range(5), 2))
def plucker(a, b): return [g.mul(a[i], b[j]) ^ g.mul(a[j], b[i]) for i, j in pairs]
H = ["011011 111100", "000111 110101", "011100 100001", "011010 010100", "010010 001111"]
P = [plucker(*[[int(c) for c in v] for v in h.split()]) for h in H]
print("(1) rank of the five Pluecker vectors of the planes found over F_2:", g.rank(P), "(4 = associated lines)")
def onelevel_rank(U, rnd):
    t = [g.rand(rnd) for _ in U]
    rows = [[x for x in b] + [g.mul(t[i], x) for x in b] for i, u in enumerate(U) for b in u]
    return g.rank(rows)
rnd = random.Random(11)
def rv(): return [g.rand(rnd) for _ in range(5)]
# (2) fifth associated plane: find c with sum c_i p_i decomposable, by a normal form: choose coordinates so that
# U_1 = <e0,e1>, U_2 = <e2,e3>; then solve the Pluecker relations for the combination numerically by brute force on a pencil.
# Simpler exact route: the planes U_i = <a_i, b_i> with b_i = A a_i-type families are associated when they are the columns of
# a 2 x 5 "scroll": take a 3-dimensional space Z and five planes meeting ... instead use the classical normal form:
# U_i = <e_i, e_{i+1}> + correction is not general. We use the direct solve: p5 = sum c_i p_i must satisfy p ^ p = 0 (five quadrics).
def wedge2(p, q):  # p ^ q in wedge^4 K^5 ~ K^5 (coefficient of the complement of index m)
    out = []
    for m in range(5):
        idx = [i for i in range(5) if i != m]; s = 0
        for (i, j) in itertools.combinations(idx, 2):
            kl = tuple(x for x in idx if x not in (i, j))
            s ^= g.mul(p[pairs.index((i, j))], q[pairs.index(kl)])
        out.append(s)
    return out
def fifth(Us):
    P4 = [plucker(*u) for u in Us]
    # p = sum c_i p_i, p^p = sum_{i<j} 2 c_i c_j p_i^p_j: in characteristic 2 use the quadratic form directly: (p^p)/2 has
    # coefficients sum_{i<j} c_i c_j (p_i ^ p_j) with the pairing counted once. Unknown products c_i c_j (6 of them), 5 equations:
    W = [[wedge2(P4[i], P4[j])[m] for (i, j) in itertools.combinations(range(4), 2)] for m in range(5)]
    ker = g.kernel(W, 6)
    return P4, ker
ok = 0
for trial in range(20):
    Us = [(rv(), rv()) for _ in range(4)]
    P4, ker = fifth(Us)
    # the kernel is spanned by one vector y_{ij} = c_i c_j (rank 5 of 6 unknowns); recover c up to scale: c_i = y_{0i} y_{12}... use c_0 = 1
    if len(ker) != 1: continue
    y = dict(zip(itertools.combinations(range(4), 2), ker[0]))
    # c_0 c_1 = y01, c_0 c_2 = y02, c_1 c_2 = y12  ->  c_0^2 = y01 y02 / y12 (square roots exist in GF(2^64))
    def sqrt(a):
        for _ in range(63): a = g.mul(a, a)
        return a
    c0 = sqrt(g.mul(g.mul(y[(0, 1)], y[(0, 2)]), g.inv(y[(1, 2)])))
    c = [c0, g.mul(y[(0, 1)], g.inv(c0)), g.mul(y[(0, 2)], g.inv(c0)), g.mul(y[(0, 3)], g.inv(c0))]
    consistent = all(g.mul(c[i], c[j]) == y[(i, j)] for i, j in y)
    p5 = [0] * 10
    for i in range(4): p5 = [x ^ g.mul(c[i], z) for x, z in zip(p5, P4[i])]
    # plane of the decomposable bivector p5: its kernel as a map K^5 -> wedge^3 is the plane; use {v : v ^ p5 = 0}
    rows = []
    for tri in itertools.combinations(range(5), 3):
        row = [0] * 5
        for m in tri:
            rest = tuple(x for x in tri if x != m)
            row[m] ^= p5[pairs.index(rest)]
        rows.append(row)
    plane = g.kernel(rows, 5)
    if len(plane) != 2 or not consistent: continue
    U = [list(u) for u in Us] + [plane]
    r_assoc = onelevel_rank(U, rnd)
    r_ctrl = onelevel_rank([list(u) for u in Us] + [[rv(), rv()]], rnd)
    ok += 1
    if ok <= 5: print(f"(2) four random planes of K^5 + the fifth associated plane: rank {r_assoc} of 10;  (3) control, fifth plane random: rank {r_ctrl} of 10")
print("constructed", ok, "associated five-tuples")
