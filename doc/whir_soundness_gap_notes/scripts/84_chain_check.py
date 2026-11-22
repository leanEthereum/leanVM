#!/usr/bin/env python3
"""Note 84, Section 9: checks of the deterministic lemmas over GF(2^8) (standard library only).

 A. Lemma 3.1 / 3.2 / Corollary 3.3 on structured genuine systems (lifted solutions with
    planted pairs and triple coincidences, sub-blocks with different directions, extra leaves):
    every reduction step keeps the row space inside the old one, keeps the system genuine and
    does not lower the excess; on the reduced system e_{i+1} = 2 e_i + G - h and
    null_{i+1} = 2 null_i - d + G at every level, down to Y_0 = empty.
 B. Lemma 2.1(c): sampled Pr[tight and G >= 1] for labels with two tight children of one node.
 C. Proposition 6.2(c): six points on a line, the K4 system is dependent iff the three pairs of
    opposite edges are in involution.
"""
import random
import sys

# ---------- GF(2^8), polynomial 0x11b, generator 3 ----------
EXP = [0] * 510
LOG = [0] * 256
_x = 1
for _i in range(255):
    EXP[_i] = _x
    LOG[_x] = _i
    _y = _x << 1
    if _y & 0x100:
        _y ^= 0x11B
    _x = _y ^ _x
for _i in range(255, 510):
    EXP[_i] = EXP[_i - 255]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[255 - LOG[a]]


class Basis:
    def __init__(self):
        self.rows = {}  # pivot column -> row with a 1 at the pivot

    def reduce(self, v):
        v = list(v)
        for c, row in self.rows.items():
            f = v[c]
            if f:
                for i, x in enumerate(row):
                    if x:
                        v[i] ^= mul(f, x)
        return v

    def add(self, v):
        v = self.reduce(v)
        for c, f in enumerate(v):
            if f:
                fi = inv(f)
                v = [mul(fi, x) for x in v]
                for c2, row in list(self.rows.items()):
                    g = row[c]
                    if g:
                        self.rows[c2] = [a ^ mul(g, b) for a, b in zip(row, v)]
                self.rows[c] = v
                return True
        return False

    def contains(self, v):
        return not any(self.reduce(v))

    def rank(self):
        return len(self.rows)


def kron(lam, g):
    return [mul(gc, l) for gc in g for l in lam]


def make_tree(v, r, rng, pool=None):
    """pool: twiddles drawn from this small set (degenerate codes with many relations); None: all of GF(2^8)."""
    pool = pool or list(range(256))
    g = [[[1] for _ in range(2 ** r)]]
    for j in range(v):
        nxt = []
        for p in range(len(g[j])):
            t0 = rng.choice(pool)
            t1 = rng.choice(pool)
            while t1 == t0:
                t1 = rng.choice(pool)
            for t in (t0, t1):
                nxt.append(g[j][p] + [mul(t, x) for x in g[j][p]])
        g.append(nxt)
    return g


def dirs_graphic(t):
    L = t - 1
    out = []
    for a in range(t):
        for b in range(a + 1, t):
            vec = [0] * L
            if a > 0:
                vec[a - 1] ^= 1
            vec[b - 1] ^= 1
            out.append(vec)
    return out


def basis_of(g, j, Y, D):
    B = Basis()
    for p, d in Y.items():
        B.add(kron(D[d], g[j][p]))
    return B


def genuine(g, j, Y, D, B=None):
    B = B or basis_of(g, j, Y, D)
    L = len(D[0])
    kj = len(g[j][0])
    for d in set(Y.values()):
        ok = False
        for c in range(kj):
            unit = [0] * (L * kj)
            for l in range(L):
                unit[c * L + l] = D[d][l]
            if not B.contains(unit):
                ok = True
                break
        if not ok:
            return False
    return True


def excess(g, j, Y, D):
    return len(Y) - basis_of(g, j, Y, D).rank()


def split(g, i, Y, D):
    """Y at level i+1 -> (rounded set, tight set)."""
    B = basis_of(g, i + 1, Y, D)
    L = len(D[0])
    ki = len(g[i][0])
    R, T = set(), set()
    for x, d in Y.items():
        w = kron(D[d], g[i][x // 2])
        (R if B.contains([0] * (L * ki) + w) else T).add(x)
    return R, T


def chain(g, v, X, D):
    """Returns (levels, violation). levels[i+1] = (Y, R, T, Bsets); violation = (leaves to rewrite, new dir) or None."""
    Y = dict(X)
    Bsets = {x: {x} for x in X}
    levels = {}
    for i in range(v - 1, -1, -1):
        R, T = split(g, i, Y, D)
        levels[i + 1] = (Y, R, T)
        up, upB = {}, {}
        for x in sorted(R):
            p = x // 2
            if p in up and up[p] != Y[x]:
                sib = x ^ 1
                big, small = (x, sib) if Y[x] > Y[sib] else (sib, x)
                return levels, (set(Bsets[big]), Y[small])
            up[p] = Y[x]
            upB.setdefault(p, set()).update(Bsets[x])
        Y, Bsets = up, upB
    levels[0] = (Y, set(), set())
    return levels, None


def check_reduced(g, v, X, D, stats):
    L = len(D[0])
    cur = dict(X)
    steps = 0
    while True:
        levels, viol = chain(g, v, cur, D)
        if viol is None:
            break
        leaves, newdir = viol
        nxt = dict(cur)
        for x in leaves:
            nxt[x] = newdir
        B = basis_of(g, v, cur, D)
        for x in leaves:
            assert B.contains(kron(D[newdir], g[v][x])), "row space not contained"
        assert genuine(g, v, nxt, D), "reduction lost genuineness"
        assert excess(g, v, nxt, D) >= excess(g, v, cur, D), "reduction lowered the excess"
        cur = nxt
        steps += 1
        assert steps < 10000
    stats["reduction steps"] += steps
    stats["systems needing reduction"] += steps > 0
    assert len(levels[0][0]) == 0, "Y_0 not empty"
    tot_G = tot_h = 0
    for i in range(v - 1, -1, -1):
        Y, R, T = levels[i + 1]
        Yup = levels[i][0]
        ki = len(g[i][0])
        assert genuine(g, i + 1, Y, D)
        e1 = excess(g, i + 1, Y, D)
        null1 = L * 2 * ki - basis_of(g, i + 1, Y, D).rank()
        Bup = basis_of(g, i, Yup, D)
        nullup = L * ki - Bup.rank()
        eup = len(Yup) - Bup.rank()
        S = Basis()
        for p, d in Yup.items():
            w = kron(D[d], g[i][p])
            S.add(w + [0] * (L * ki))
            S.add([0] * (L * ki) + w)
        for x in T:
            S.add(kron(D[Y[x]], g[i + 1][x]))
            assert not (x // 2 in Yup and Yup[x // 2] == Y[x]), "tight child with its parent's direction"
            assert not ((x ^ 1) in T and Y[x ^ 1] == Y[x]), "tight siblings with one direction"
        dimS = L * 2 * ki - S.rank()
        G = dimS - (2 * nullup - len(T))
        h = 2 * len(Yup) - len(R)
        assert G >= 0 and h >= 0
        assert dimS == null1, "N(Y) != S(Y^, D)"
        assert e1 == 2 * eup + G - h, "excess identity"
        tot_G += G
        tot_h += h
    stats["systems"] += 1
    stats["with G > 0"] += tot_G > 0
    stats["with half-rounded nodes"] += tot_h > 0
    stats["with excess > 0"] += excess(g, v, cur, D) > 0
    stats["max excess"] = max(stats["max excess"], excess(g, v, cur, D))


def structured_system(g, v, r, D, rng):
    """A genuine leaf system built from a lifted solution with planted coincidences."""
    L = len(D[0])
    i = rng.choice([1, 2]) if v >= 3 else 1
    ki = 2 ** i
    while True:
        lab = {}
        B = Basis()
        cnt = 0
        for p in rng.sample(range(len(g[i])), len(g[i])):
            u = rng.random()
            if u < 0.45 or cnt >= L * ki - 2:
                continue
            ds = rng.sample(range(len(D)), 1 if u < 0.8 else 2)
            lab[p] = ds
            for d in ds:
                cnt += B.add(kron(D[d], g[i][p]))
        if L * ki - B.rank() >= 1 and lab:
            break
    # a random solution a of the top system: null vector of the row basis
    free = [c for c in range(L * ki) if c not in B.rows]
    a = [0] * (L * ki)
    for c in free:
        a[c] = rng.randrange(256)
    for c, row in B.rows.items():
        a[c] = 0
        s = 0
        for c2 in free:
            s ^= mul(row[c2], a[c2])
        a[c] = s
    X = {}
    blk = 2 ** (v - i)
    for p in range(len(g[i])):
        val = [0] * L
        for c in range(ki):
            for l in range(L):
                val[l] ^= mul(a[c * L + l], g[i][p][c])
        allowed = [d for d in range(len(D)) if not any([sum_bits(D[d], val)])]
        if p in lab and allowed:
            depth = rng.randrange(v - i + 1)
            sub = blk >> depth
            for s in range(2 ** depth):
                d = rng.choice(allowed)
                for x in range(p * blk + s * sub, p * blk + (s + 1) * sub):
                    if rng.random() < 0.9:
                        X[x] = d
    if not X or not genuine(g, v, X, D):
        return None
    others = [x for x in range(len(g[v])) if x not in X]
    rng.shuffle(others)
    for x in others[: rng.randrange(0, 2 * blk + 1)]:
        X[x] = rng.randrange(len(D))
        if not genuine(g, v, X, D):
            del X[x]
    return X


def greedy_system(g, v, D, rng):
    """Add leaves with random directions while the system stays genuine (maximal genuine systems)."""
    X = {}
    leaves = list(range(len(g[v])))
    rng.shuffle(leaves)
    for x in leaves:
        ds = list(range(len(D)))
        rng.shuffle(ds)
        for d in ds[: rng.choice([1, len(D)])]:
            X[x] = d
            if genuine(g, v, X, D):
                break
            del X[x]
    return X or None


def sum_bits(lam, val):
    s = 0
    for l, x in zip(lam, val):
        if l:
            s ^= mul(l, x)
    return s


def part_A(rng):
    print("A. reduction and chain identities (assertions; any failure aborts)")
    for (v, r, t, trials) in ((3, 1, 3, 500), (3, 2, 3, 400), (3, 1, 4, 400), (4, 1, 3, 150), (3, 2, 4, 250)):
        D = dirs_graphic(t)
        stats = {k: 0 for k in ("systems", "systems needing reduction", "reduction steps", "with G > 0", "with half-rounded nodes", "with excess > 0", "max excess")}
        done = 0
        while done < trials:
            g = make_tree(v, r, rng)
            X = structured_system(g, v, r, D, rng)
            if X is None:
                continue
            check_reduced(g, v, X, D, stats)
            done += 1
        print(f"  k={2**v} n={2**(v+r)} t={t}: " + ", ".join(f"{k} {val}" for k, val in stats.items()) + "; 0 violations")
        sys.stdout.flush()
    print("A'. the same assertions on degenerate codes (twiddles from a pool of 2, 3 or 4 field elements: the lemmas are deterministic), maximal genuine systems built greedily")
    for (v, r, t, pool_size, trials) in ((3, 1, 3, 2, 300), (3, 1, 3, 3, 300), (3, 2, 3, 2, 200), (3, 1, 4, 2, 200), (3, 1, 4, 4, 200), (4, 1, 3, 2, 80), (2, 2, 4, 2, 300), (2, 3, 5, 3, 150)):
        D = dirs_graphic(t)
        stats = {k: 0 for k in ("systems", "systems needing reduction", "reduction steps", "with G > 0", "with half-rounded nodes", "with excess > 0", "max excess")}
        done = 0
        while done < trials:
            pool = rng.sample(range(256), pool_size)
            g = make_tree(v, r, rng, pool)
            X = greedy_system(g, v, D, rng)
            if X is None:
                continue
            check_reduced(g, v, X, D, stats)
            done += 1
        print(f"  k={2**v} n={2**(v+r)} t={t} pool {pool_size}: " + ", ".join(f"{k} {val}" for k, val in stats.items()) + "; 0 violations")
        sys.stdout.flush()


def part_B(rng):
    print("B. Lemma 2.1(c), sampled: label with Y empty at level 1 (k_1 = 2, L = 2, null = 4), D = 8 children of 4 nodes, two tight children with different directions under each node")
    D = dirs_graphic(3)
    L = 2
    g1 = make_tree(1, 2, rng)
    nodes = [0, 3, 5, 6]
    for name, dirpairs in (("directions (0,1) at every node", [(0, 1)] * 4), ("mixed direction pairs", [(0, 1), (1, 2), (2, 0), (1, 0)])):
        N = 30000
        hit = tight_hit = 0
        for _ in range(N):
            S = Basis()
            rows = []
            for p, (d0, d1) in zip(nodes, dirpairs):
                t0 = rng.randrange(256)
                t1 = rng.randrange(256)
                while t1 == t0:
                    t1 = rng.randrange(256)
                for t, d in ((t0, d0), (t1, d1)):
                    gp = g1[1][p]
                    S.add(kron(D[d], gp + [mul(t, x) for x in gp]))
                    rows.append((p, d))
            dimS = 8 - S.rank()
            if dimS >= 1:
                hit += 1
                # tightness: beta-part of every tight functional nonzero on S (dimension 1 almost always)
                free = [c for c in range(8) if c not in S.rows]
                sols = []
                for fc in free:
                    m = [0] * 8
                    m[fc] = 1
                    for c, row in S.rows.items():
                        m[c] = row[fc]
                    sols.append(m)
                tight = True
                for p, d in rows:
                    w = kron(D[d], g1[1][p])
                    if not any(sum_bits(w, m[4:]) for m in sols):
                        tight = False
                tight_hit += tight
        bound = (1 / 256) / (1 - 2 * 8 / 256)
        print(f"  {name}: Pr[G >= 1] = {hit/N:.5f}, Pr[tight and G >= 1] = {tight_hit/N:.5f}, bound {bound:.5f}, 1/q = {1/256:.5f} ({N} draws)")
        sys.stdout.flush()


def part_C(rng):
    print("C. Proposition 6.2(c): K4 system on six distinct points dependent iff opposite pairs in involution")
    D = dirs_graphic(4)  # order: 01 02 03 12 13 23
    agree = dep = 0
    N = 20000
    for trial in range(N):
        xs = rng.sample(range(256), 6)
        if trial % 2 == 0:
            # plant: solve the determinant, affine in x12 = xs[3], for x12
            def det(x12):
                rows3 = [(xs[0] ^ xs[5], mul(xs[0], xs[5])), (xs[1] ^ xs[4], mul(xs[1], xs[4])), (xs[2] ^ x12, mul(xs[2], x12))]
                (s1, p1), (s2, p2), (s3, p3) = rows3
                return mul(s2, p3) ^ mul(s3, p2) ^ mul(s1, p3) ^ mul(s3, p1) ^ mul(s1, p2) ^ mul(s2, p1)
            d0, d1 = det(0), det(1)
            slope = d0 ^ d1
            if slope == 0:
                continue
            x12 = mul(d0, inv(slope))
            if x12 in xs[:3] + xs[4:]:
                continue
            xs[3] = x12
        B = Basis()
        for d, x in zip(D, xs):
            B.add(kron(d, [1, x]))
        rows3 = [(xs[0] ^ xs[5], mul(xs[0], xs[5])), (xs[1] ^ xs[4], mul(xs[1], xs[4])), (xs[2] ^ xs[3], mul(xs[2], xs[3]))]
        (s1, p1), (s2, p2), (s3, p3) = rows3
        dt = mul(s2, p3) ^ mul(s3, p2) ^ mul(s1, p3) ^ mul(s3, p1) ^ mul(s1, p2) ^ mul(s2, p1)
        assert (B.rank() < 6) == (dt == 0), "involution criterion fails"
        assert B.rank() >= 5
        dep += B.rank() < 6
        agree += 1
    print(f"  {agree} configurations, {dep} dependent, criterion agrees on all, rank never below 5")


if __name__ == "__main__":
    rng = random.Random(84)
    part_C(rng)
    part_A(rng)
    part_B(rng)
