"""Note 76: independent primal check of lists found by 76_n16 (error supports as hex masks): the incidence system of
the pattern (classes = members not in error) has a kernel in which no two members coincide (exact ranks, GF(2^64), T2,
an independent draw of the twiddles), and a kernel point is re-encoded and its agreements counted."""
import random, os, importlib.util, sys
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
gf = load("74_gfpy"); du = load("76_dual")
mul = gf.mul
def rows_of(G, k, t, cls, merge=None):
    L = t - 1; rows = []
    for x, C in enumerate(cls):
        mem = [l for l in range(t) if (C >> l) & 1]
        for l in mem[1:]:
            r = [0] * (L * k); l0 = mem[0]
            if l >= 1: r[(l - 1) * k:l * k] = G[x]
            if l0 >= 1: r[(l0 - 1) * k:l0 * k] = G[x]
            rows.append(r)
    if merge:
        a, b = merge
        for e in range(k):
            r = [0] * (L * k)
            if a >= 1: r[(a - 1) * k + e] = 1
            if b >= 1: r[(b - 1) * k + e] = 1
            rows.append(r)
    return rows
def check(masks, G, n, k, rnd):
    t = len(masks); L = t - 1
    cls = [sum(1 << l for l, m in enumerate(masks) if not (m >> x) & 1) for x in range(n)]
    base = rows_of(G, k, t, cls); rk = gf.rank(base)
    distinct = all(gf.rank(rows_of(G, k, t, cls, (a, b))) > rk for a in range(t) for b in range(a + 1, t))
    ker = gf.kernel(base, L * k)
    # a random kernel point, its codewords (member 0 is the zero codeword), a word agreeing with each class
    pt = [0] * (L * k)
    for v in ker:
        c = rnd.getrandbits(64)
        pt = [p ^ mul(c, x) for p, x in zip(pt, v)]
    cw = [[0] * n] + [[0] * n for _ in range(L)]
    for l in range(1, t):
        for x in range(n):
            s = 0
            for e in range(k): s ^= mul(G[x][e], pt[(l - 1) * k + e])
            cw[l][x] = s
    agree = []
    for l in range(t):
        a = 0
        for x in range(n):
            mem = [m for m in range(t) if (cls[x] >> m) & 1]
            if l in mem and all(cw[m][x] == cw[l][x] for m in mem): a += 1
        agree.append(a)
    return rk, L * k, len(ker), distinct, agree, len(set(tuple(c) for c in cw))
if __name__ == "__main__":
    rnd = random.Random(31337); v = 3; n = 16; k = 8
    tw = du.make_tw(v, 1, rnd); G = [du.row(tw, v, j) for j in range(n)]
    lists = [l.split(":")[1].split() for l in open(os.path.join(here, "76_tmp/n16_seed2_part0.txt")) if l.startswith("LIST 5 ")]
    sample = [lists[0], lists[len(lists) // 2], lists[-1]] + [l.split(":")[1].split() for l in open(os.path.join(here, "76_tmp/n16_seed2_part1.txt")) if l.startswith("LIST 5 ")][:3]
    for hx in sample:
        masks = [int(h, 16) for h in hx]
        rk, Lk, kd, distinct, agree, ncw = check(masks, G, n, k, rnd)
        print("supports", " ".join(hx), ": rank", rk, "of", Lk, "kernel", kd, "members pairwise distinct on the kernel:", distinct, "distinct codewords of a kernel point:", ncw, "agreements with the word:", agree)
    # negative control: a sixth member added to the first list (the six-set 0x0fc0) must force a collision or kill the kernel
    masks = [int(h, 16) for h in sample[0]] + [0x0fc0]
    rk, Lk, kd, distinct, agree, ncw = check(masks, G, n, k, rnd)
    print("control, six supports:", "rank", rk, "of", Lk, "kernel", kd, "members pairwise distinct on the kernel:", distinct)
