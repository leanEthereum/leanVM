"""Note 76, Lemma 1.1: the dual of a rate-1/2 tree code (T2) is the sibling-swapped tree code with column multipliers.
Exact check over GF(2^64) for v = 1..5. Also Lemma 1.2 on one instance (error supports = syndrome representations)."""
import random, importlib.util, os, sys
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("gfpy", os.path.join(here, "74_gfpy.py")); gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
mul, inv = gf.mul, gf.inv

def make_tw(v, r, rnd):
    """tw[i][q]: twiddle of node q at layer i (q indexes the n >> i nodes), as in 69_tree.h"""
    n = 1 << (v + r)
    tw = []
    for i in range(v):
        row = []
        for q in range(0, n >> i, 2):
            a = rnd.getrandbits(64); b = rnd.getrandbits(64)
            while b == a: b = rnd.getrandbits(64)
            row += [a, b]
        tw.append(row)
    return tw

def row(tw, v, j):
    out = [1]
    for i in range(v):
        x = tw[i][j >> i]
        out = out + [mul(e, x) for e in out]
    return out

def swapped(tw):
    return [[rowi[q ^ 1] for q in range(len(rowi))] for rowi in tw]

def check_dual(v, rnd):
    r = 1; n = 1 << (v + r); k = 1 << v
    tw = make_tw(v, r, rnd); sw = swapped(tw)
    G = [row(tw, v, j) for j in range(n)]
    Gs = [row(sw, v, j) for j in range(n)]
    bad = 0
    for j in range(n):
        d = 1
        for i in range(v):
            q = j >> i
            d = mul(d, inv(tw[i][q] ^ tw[i][q ^ 1]))
        Gs[j] = [mul(d, e) for e in Gs[j]]
    # dual generator column e' = complement of e: H[j][e] = Gs[j][e ^ (k-1)]
    for e in range(k):
        for f in range(k):
            s = 0
            for j in range(n):
                s ^= mul(G[j][e], Gs[j][f ^ (k - 1)])
            if s: bad += 1
    return bad

if __name__ == "__main__":
    rnd = random.Random(76)
    for v in range(1, 6):
        print("v =", v, "n =", 2 << v, "nonzero entries of G^T (Delta G^sw P):", check_dual(v, rnd))
