#!/usr/bin/python3
# Referee 87: independent exact check of note 84, Lemma 3.1(d), Lemma 3.2 (reduction) and the chain
# identity e_{i+1} = 2 e_i + G - h, over GF(2^8), tree codes T2 with J = 0 (all twiddles random,
# optionally from a small pool so that systems with large excess exist).
import random, sys

# GF(2^8), polynomial x^8 + x^4 + x^3 + x + 1, generator 3
EXP = [0] * 510
LOG = [0] * 256
x = 1
for i in range(255):
    EXP[i] = x
    LOG[x] = i
    x ^= (x << 1) ^ (0x11B if x & 0x80 else 0)
    x &= 0xFF if x < 256 else 0x1FF
for i in range(255, 510):
    EXP[i] = EXP[i - 255]
def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]
def inv(a):
    return EXP[255 - LOG[a]]
assert all(mul(a, inv(a)) == 1 for a in range(1, 256))

class Span:
    """Row space over GF(2^8) kept in reduced echelon form."""
    def __init__(self, dim):
        self.dim = dim
        self.rows = {}  # pivot -> row (pivot entry 1)
    def reduce(self, v):
        v = list(v)
        for piv, row in self.rows.items():
            c = v[piv]
            if c:
                for i in range(self.dim):
                    if row[i]:
                        v[i] ^= mul(c, row[i])
        return v
    def add(self, v):
        v = self.reduce(v)
        piv = next((i for i in range(self.dim) if v[i]), None)
        if piv is None:
            return False
        c = inv(v[piv])
        v = [mul(c, a) for a in v]
        for p2, row in list(self.rows.items()):
            c2 = row[piv]
            if c2:
                self.rows[p2] = [a ^ mul(c2, b) for a, b in zip(row, v)]
        self.rows[piv] = v
        return True
    def contains(self, v):
        return not any(self.reduce(v))
    def rank(self):
        return len(self.rows)

def build_tree(r, v, rng, pool=None):
    g = [[[1] for _ in range(2 ** r)]]
    for j in range(v):
        nxt = []
        for p in range(len(g[j])):
            while True:
                t0 = rng.choice(pool) if pool else rng.randrange(256)
                t1 = rng.choice(pool) if pool else rng.randrange(256)
                if t0 != t1:
                    break
            for t in (t0, t1):
                nxt.append(g[j][p] + [mul(t, a) for a in g[j][p]])
        g.append(nxt)
    return g

def row(lmb, gp):
    return [mul(l, a) for l in lmb for a in gp]
def row2(lmb, gp, half):  # lambda (x) g_p (x) e_half at the next level
    z = [0] * len(gp)
    return [mul(l, a) for l in lmb for a in ((gp + z) if half == 0 else (z + gp))]

def span_of(g, level, Y, L):
    S = Span(L * len(g[level][0]))
    for p, lmb in Y.items():
        S.add(row(lmb, g[level][p]))
    return S

def genuine(g, level, Y, L, S=None):
    S = S or span_of(g, level, Y, L)
    k = len(g[level][0])
    for lmb in set(Y.values()):
        if all(S.contains(row(lmb, [1 if c == cc else 0 for cc in range(k)])) for c in range(k)):
            return False
    return True

def excess(g, level, Y, L):
    return len(Y) - span_of(g, level, Y, L).rank()

def one_level(g, lev, Y, L):
    """Y: system at level lev >= 1. Returns rounded set, tight set, parent (or None if not reduced), conflict."""
    S = span_of(g, lev, Y, L)
    R, D = {}, {}
    for xnode, lmb in Y.items():
        gp = g[lev - 1][xnode >> 1]
        if S.contains(row2(lmb, gp, 0)) and S.contains(row2(lmb, gp, 1)):
            R[xnode] = lmb
        else:
            D[xnode] = lmb
    parent, conflict = {}, None
    for xnode, lmb in R.items():
        p = xnode >> 1
        if p in parent and parent[p] != lmb:
            conflict = p
        parent.setdefault(p, lmb)
    return S, R, D, parent, conflict

def chain_or_conflict(g, v, X, L):
    """Walk the chain from the leaves. Returns ('ok', data) or ('conflict', level, p, Rsets)."""
    Y, Rsets, data = dict(X), {}, []
    for lev in range(v, 0, -1):
        S, R, D, parent, conflict = one_level(g, lev, Y, L)
        Rsets[lev] = R
        if conflict is not None:
            return ("conflict", lev, conflict, Rsets, Y)
        data.append((lev, Y, S, R, D, parent))
        Y = parent
    return ("ok", data, Y)

def check_reduced(g, v, X, L, stats):
    res = chain_or_conflict(g, v, X, L)
    assert res[0] == "ok"
    _, data, Y0 = res
    assert Y0 == {}, "Y_0 must be empty"
    for lev, Y, S, R, D, parent in data:
        klo = len(g[lev - 1][0])
        # S(Y^, D): rows of the parent tensored with K^2, and the rows of D
        T = Span(L * 2 * klo)
        for p, lmb in parent.items():
            T.add(row2(lmb, g[lev - 1][p], 0))
            T.add(row2(lmb, g[lev - 1][p], 1))
        for xnode, lmb in D.items():
            T.add(row(lmb, g[lev][xnode]))
        assert T.rank() == S.rank() and all(S.contains(rw) for rw in T.rows.values()), "N_{i+1}(Y) = S(Y^, D)"
        null_par = L * klo - span_of(g, lev - 1, parent, L).rank()
        G = (L * 2 * klo - T.rank()) - (2 * null_par - len(D))
        h = sum(1 for p in parent if not ((2 * p in R) and (2 * p + 1 in R)))
        e_hi = len(Y) - S.rank()
        e_lo = len(parent) - span_of(g, lev - 1, parent, L).rank()
        assert 0 <= G <= len(D)
        assert e_hi == 2 * e_lo + G - h, "chain identity"
        for xnode, lmb in D.items():
            assert parent.get(xnode >> 1) != lmb, "tight child with its parent's direction"
            assert not ((xnode ^ 1) in D and D[xnode ^ 1] == lmb), "two tight siblings with one direction"
        assert genuine(g, lev - 1, parent, L), "parent genuine"
        stats["levels"] += 1
        stats["half"] += h
        stats["Gpos"] += (G > 0)

def reduce_system(g, v, X, L, order, stats):
    X = dict(X)
    steps = 0
    while True:
        res = chain_or_conflict(g, v, X, L)
        if res[0] == "ok":
            return X, steps
        _, lev, p, Rsets, Y = res
        la, mu = Y[2 * p], Y[2 * p + 1]
        y = 2 * p + 1
        if order[la] > order[mu]:
            la, mu, y = mu, la, 2 * p
        # B(y): leaves below y rounded all the way up to y
        B = [y]
        for m in range(lev + 1, v + 1):
            B = [c for b in B for c in (2 * b, 2 * b + 1) if c in Rsets[m]]
        assert B, "B(y) not empty"
        assert all(X[b] == mu for b in B), "leaves of B(y) carry the direction of y"
        Sold = span_of(g, v, X, L)
        eold = len(X) - Sold.rank()
        for b in B:
            assert Sold.contains(row(la, g[v][b])), "rewritten row lies in the old row space"
            X[b] = la
        Snew = span_of(g, v, X, L)
        assert all(Sold.contains(rw) for rw in Snew.rows.values()), "R_v(X') inside R_v(X)"
        assert len(X) - Snew.rank() >= eold
        assert genuine(g, v, X, L, Snew)
        steps += 1

def directions(t):
    L = t - 1
    out = []
    for a in range(t):
        for b in range(a + 1, t):
            vec = [0] * L
            if a > 0:
                vec[a - 1] ^= 1
            vec[b - 1] ^= 1
            out.append((tuple(vec), (a, b)))
    return out

def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 87)
    stats = {"systems": 0, "needed": 0, "steps": 0, "levels": 0, "half": 0, "Gpos": 0, "maxe": 0}
    configs = [(1, 3, 3), (2, 2, 3), (1, 3, 4), (2, 3, 3), (2, 2, 4), (3, 2, 3)]
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    for (r, v, t) in configs:
        L = t - 1
        dirs = directions(t)
        order = {d: i for i, (d, _) in enumerate(dirs)}
        k, n = 2 ** v, 2 ** (v + r)
        for trial in range(per):
            poolsize = rng.choice([2, 3, 4, 4, 256])
            pool = None if poolsize == 256 else rng.sample(range(256), poolsize)
            g = build_tree(r, v, rng, pool)
            # t messages with entries in a small set, member 0 is zero
            vals = [0, 1] + ([rng.randrange(256)] if rng.random() < 0.5 else [])
            msgs = [[0] * k] + [[rng.choice(vals) for _ in range(k)] for _ in range(t - 1)]
            if len(set(map(tuple, msgs))) < t:
                continue
            cw = [[0] * n for _ in range(t)]
            for a in range(t):
                for xleaf in range(n):
                    s = 0
                    for c in range(k):
                        s ^= mul(msgs[a][c], g[v][xleaf][c])
                    cw[a][xleaf] = s
            X = {}
            for xleaf in range(n):
                pairs = [d for d, (a, b) in dirs if cw[a][xleaf] == cw[b][xleaf]]
                if pairs:
                    X[xleaf] = rng.choice(pairs)
            assert genuine(g, v, X, L)
            # greedy extension by further leaves while the system stays genuine
            free = [xl for xl in range(n) if xl not in X]
            rng.shuffle(free)
            for xl in free:
                d = rng.choice(dirs)[0]
                X[xl] = d
                if not genuine(g, v, X, L):
                    del X[xl]
            if not X:
                continue
            e0 = excess(g, v, X, L)
            Xs, steps = reduce_system(g, v, X, L, order, stats)
            assert set(Xs) == set(X) and excess(g, v, Xs, L) >= e0
            check_reduced(g, v, Xs, L, stats)
            stats["systems"] += 1
            stats["needed"] += (steps > 0)
            stats["steps"] += steps
            stats["maxe"] = max(stats["maxe"], excess(g, v, Xs, L))
        print("config rate 2^-%d k=%d n=%d t=%d done: %s" % (r, k, n, t, stats), flush=True)
    print("ALL ASSERTIONS PASSED", stats)

main()
