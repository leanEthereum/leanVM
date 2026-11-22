"""Note 76, Corollaries 4.2 and 4.3: exact rank of random patterns of the tree code (T2, GF(2^64)) against the
matching bound (best bijection between the two trees, by the Hungarian method) and the sibling bound."""
import random, importlib.util, os, sys
import numpy as np
from scipy.optimize import linear_sum_assignment
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
gf = load("74_gfpy"); du = load("76_dual")

def dim_union(C1, C2, t):
    """dim(Lambda_x + Lambda_y) for classes given as bitmasks over t members: t' - components on the union"""
    comps = [c for c in (C1, C2) if bin(c).count("1") >= 2]
    if not comps: return 0
    if len(comps) == 2 and comps[0] & comps[1]: return bin(comps[0] | comps[1]).count("1") - 1
    return sum(bin(c).count("1") - 1 for c in comps)

def inc_rank(G, k, t, cls):
    L = t - 1; rows = []
    for x, C in enumerate(cls):
        mem = [l for l in range(t) if (C >> l) & 1]
        if len(mem) < 2: continue
        l0 = mem[0]
        for l in mem[1:]:
            r = [0] * (L * k)
            if l >= 1: r[(l - 1) * k:(l) * k] = G[x]
            if l0 >= 1: r[(l0 - 1) * k:(l0) * k] = G[x]
            rows.append(r)
    return gf.rank(rows) if rows else 0, len(rows)

def run(v, t, trials, dens, rnd):
    n = 2 << v; k = 1 << v
    tw = du.make_tw(v, 1, rnd); G = [du.row(tw, v, j) for j in range(n)]
    viol = eq_m = eq_s = deficient = eq_best = 0
    for _ in range(trials):
        cls = [sum((rnd.random() < dens) << l for l in range(t)) for _ in range(n)]
        rk, w = inc_rank(G, k, t, cls)
        W = np.array([[dim_union(cls[x], cls[k + y], t) for y in range(k)] for x in range(k)])
        ri, ci = linear_sum_assignment(-W); mb = int(W[ri, ci].sum())
        sb = sum(dim_union(cls[2 * p], cls[2 * p + 1], t) for p in range(n // 2))
        if rk < mb or rk < sb: viol += 1
        if rk < w: deficient += 1
        eq_m += rk == mb; eq_s += rk == sb; eq_best += rk == max(mb, sb)
    print(f"(k,n)=({k},{n}) members {t} density {dens}: patterns {trials}, violations of rank >= bound: {viol}, rows dependent: {deficient}, rank = matching bound: {eq_m}, rank = sibling bound: {eq_s}, rank = larger of the two: {eq_best}")

if __name__ == "__main__":
    rnd = random.Random(4242)
    for (v, t, trials, dens) in [(2, 3, 3000, 0.6), (2, 4, 3000, 0.6), (2, 5, 2000, 0.6), (2, 4, 2000, 0.4), (3, 3, 400, 0.6), (3, 4, 300, 0.6), (3, 5, 200, 0.5)]:
        run(v, t, trials, dens, rnd)
