#!/usr/bin/env python3
"""Note 73, Section 8: toy checks of the lemmas behind the distance theorem.

Fields GF(2^4), GF(2^8); tree codes T1/T2; numpy only.
E1  Lemma 2.1: for fixed T_j and labels (Y, D, c) of three families (fine, coarse, mixed),
    the law of the fresh excess G and of tightness over the next level's twiddles,
    against q^-g / (1 - d/q); and note 68's Lemma 5.1 for the nullity of the set itself.
E2  Lemmas 3.1, 3.2: chain identities for closures of random leaf sets (deterministic, exact).
E3  Lemma 4.1: two consecutive levels, joint tail against the product bound.
E4  Theorem 5.1 at toy size (field size q in place of 2^64): largest excess of a flat against eps_0 n.
"""
import itertools, math, sys
import numpy as np

rng = np.random.default_rng(73)

class GF:
    def __init__(self, m):
        self.m = m; self.q = 1 << m
        poly = {4: 0x13, 8: 0x11b}[m]
        q = self.q
        mul = np.zeros((q, q), dtype=np.uint8)
        for a in range(q):
            for b in range(q):
                x, y, r = a, b, 0
                while y:
                    if y & 1: r ^= x
                    y >>= 1; x <<= 1
                    if x & q: x ^= poly
                mul[a, b] = r
        self.mul = mul
        inv = np.zeros(q, dtype=np.uint8)
        for a in range(1, q):
            inv[a] = int(np.nonzero(mul[a] == 1)[0][0])
        self.inv = inv

def brank(F, A):
    """Batched rank over GF. A: (B, R, C) uint8 (destroyed)."""
    B, R, C = A.shape
    r = np.zeros(B, dtype=np.int64)
    rows = np.arange(R)[None, :]
    ar = np.arange(B)
    for col in range(C):
        colv = A[:, :, col]
        mask = (colv != 0) & (rows >= r[:, None])
        has = mask.any(axis=1)
        if not has.any(): continue
        piv = mask.argmax(axis=1)
        idx = ar[has]; pr = piv[has]; rr = r[has]
        tmp = A[idx, rr].copy(); A[idx, rr] = A[idx, pr]; A[idx, pr] = tmp
        prow = A[idx, rr]
        prow = F.mul[F.inv[prow[:, col]][:, None], prow]
        A[idx, rr] = prow
        sub = A[idx]
        fac = sub[:, :, col].copy()
        fac[np.arange(len(idx)), rr] = 0
        sub ^= F.mul[fac[:, :, None], prow[:, None, :]]
        A[idx] = sub
        r[has] += 1
    return r

def rank1(F, M):
    if M.shape[0] == 0: return 0
    return int(brank(F, M[None].copy())[0])

def draw_twiddles(F, variant, shape):
    """shape (..., n_j): returns (..., n_j, 2) with distinct pairs."""
    t0 = rng.integers(0, F.q, size=shape, dtype=np.uint8)
    if variant == "T1":
        t1 = t0 ^ 1
    else:
        off = rng.integers(1, F.q, size=shape, dtype=np.uint8)
        t1 = t0 ^ off
    return np.stack([t0, t1], axis=-1)

def split(F, G, tw):
    """G: (n_j, k_j) rows of T_j. tw: (B, n_j, 2). Returns (B, 2 n_j, 2 k_j): child (p,b) at index 2p+b."""
    B = tw.shape[0]; nj, kj = G.shape
    out = np.zeros((B, 2 * nj, 2 * kj), dtype=np.uint8)
    out[:, 0::2, :kj] = G[None]; out[:, 1::2, :kj] = G[None]
    out[:, 0::2, kj:] = F.mul[tw[:, :, 0][:, :, None], G[None]]
    out[:, 1::2, kj:] = F.mul[tw[:, :, 1][:, :, None], G[None]]
    return out

def tree(F, variant, r, depth):
    """One random tree code: list of generator matrices T_0..T_depth and the twiddles."""
    G = np.ones((1 << r, 1), dtype=np.uint8)
    Ts = [G]; tws = []
    for _ in range(depth):
        tw = draw_twiddles(F, variant, (1, G.shape[0]))
        G = split(F, G, tw)[0]
        Ts.append(G); tws.append(tw[0])
    return Ts, tws

def is_mds(F, G):
    n, k = G.shape
    subs = np.array(list(itertools.combinations(range(n), k)))
    return bool((brank(F, G[subs].copy()) == k).all())

def label_stats(F, variant, G, Y, D, c, B):
    """Law of (tight, fresh excess) of label (Y, D, c) over B draws of the next level's twiddles."""
    nj, kj = G.shape
    rkY = rank1(F, G[Y]) if len(Y) else 0
    tw = draw_twiddles(F, variant, (B, nj))
    T1 = split(F, G, tw)
    pos = [2 * p + b for p in Y for b in (0, 1)] + [2 * p + cc for p, cc in zip(D, c)]
    M = T1[:, pos, :]
    rk = brank(F, M.copy())
    Gx = 2 * rkY + len(D) - rk
    tight = np.ones(B, dtype=bool)
    for p in D:
        extra = np.zeros((B, 1, 2 * kj), dtype=np.uint8); extra[:, 0, kj:] = G[p][None]
        rk2 = brank(F, np.concatenate([M, extra], axis=1))
        tight &= (rk2 > rk)
    null1 = 2 * kj - rk
    return tight, Gx, null1

def lemma51_rhs(F, G, Fset, H, nu):
    """Right side of note 68's Lemma 5.1 with the exact factor 1/(1 - |H|/q), given T_j."""
    q = F.q; kj = G.shape[1]; tot = 0.0
    for m in range(len(H) + 1):
        for R in itertools.combinations(H, m):
            Yr = list(Fset) + list(R)
            nl = kj - (rank1(F, G[Yr]) if Yr else 0)
            if nl >= 1: tot += float(q) ** (2 * nl - nu - (len(H) - m))
    return tot / (1 - len(H) / q)

def label_stats_chunked(F, variant, G, Y, D, c, B, chunk=50000):
    outs = [label_stats(F, variant, G, Y, D, c, min(chunk, B - o)) for o in range(0, B, chunk)]
    return tuple(np.concatenate([o[i] for o in outs]) for i in range(3))

def e1(F, variant, B):
    q = F.q
    print(f"E1  GF(2^{F.m}) {variant}: level j with n_j = 8, k_j = 4 (rate 1/2), {B} draws of the next twiddles per label")
    for topkind in ("MDS", "defective"):
        while True:
            Ts, _ = tree(F, variant, 1, 2); G = Ts[2]
            if topkind == "MDS" and is_mds(F, G): break
            if topkind == "defective" and not is_mds(F, G): break
        fams = [
            ("fine   (Y empty, D = 8 half pairs)", [], list(range(8))),
            ("fine   (Y = 1 node, D = 6 half pairs)", [0], [1, 2, 3, 4, 5, 6]),
            ("mixed  (Y = 2 nodes, D = 4 half pairs)", [0, 5], [1, 2, 6, 7]),
            ("mixed  (Y = 2 nodes, D = 5 half pairs)", [0, 5], [1, 2, 3, 6, 7]),
            ("coarse (Y = 3 nodes, D = 2 half pairs)", [0, 3, 6], [1, 4]),
        ]
        if topkind == "defective":
            sing = [list(Yc) for Yc in itertools.combinations(range(8), 4) if rank1(F, G[list(Yc)]) < 4]
            Ys = sing[0]
            for cand in sing:
                if len(closure(F, G, cand)[0]) <= 5: Ys = cand; break
            cl = closure(F, G, Ys)[0]; rest = [p for p in range(8) if p not in cl]
            fams += [
                ("inherited (Y = a singular 4-subset, D empty)", Ys, []),
                ("inherited (Y = a singular 4-subset, D = 2 half pairs)", Ys, rest[:2]),
                ("inherited (Y = a singular 4-subset, D = 3 half pairs)", Ys, rest[:3]),
                ("inherited (Y = 3 of the singular 4, D = the 4th and 2 more)", Ys[:3], [Ys[3]] + rest[:2]),
            ]
            print(f"  T_j defective ({len(sing)} singular 4-subsets of 70):")
        else:
            print(f"  T_j MDS:")
        for name, Y, D in fams:
            c = [int(x) for x in rng.integers(0, 2, size=len(D))]
            tight, Gx, null1 = label_stats_chunked(F, variant, G, Y, D, c, B)
            d = len(D); bnd = 1 / (1 - d / q)
            row = []
            for g in (1, 2, 3):
                meas = float((tight & (Gx >= g)).mean())
                row.append(f"g>={g}: {meas:.2e} (bound {bnd * q ** -g:.2e})")
            nuY = 4 - (rank1(F, G[Y]) if Y else 0)
            base = 2 * nuY - d
            lo = max(base, 0)
            hist = "  ".join(f"{nu}: {float((null1 == nu).mean()):.2e}" for nu in range(lo, lo + 4))
            nulls = "  ".join(f"P[null>={nu}] = {float((null1 >= nu).mean()):.2e} against {min(1.0, lemma51_rhs(F, G, Y, D, nu)):.2e}" for nu in range(lo + 1, lo + 3))
            print(f"    {name}: null_j(Y) = {nuY}, 2 null_j(Y) - d = {base}, P[tight] = {tight.mean():.4f}")
            print(f"        tight and " + "; ".join(row))
            print(f"        law of null_(j+1)(Z): {hist}")
            print(f"        measured against Lemma 5.1 of note 68: {nulls}")

def closure(F, G, Z):
    n, k = G.shape
    Z = sorted(set(Z)); rk = rank1(F, G[Z]) if Z else 0
    out = list(Z)
    for p in range(n):
        if p in Z: continue
        if rank1(F, G[Z + [p]]) == rk: out.append(p)
    return sorted(out), rk

def e2(F, variant, trials):
    r, depth = 1, 4
    bad = 0; tot = 0; maxE = 0
    for _ in range(trials):
        Ts, tws = tree(F, variant, r, depth)
        n = Ts[depth].shape[0]; k = Ts[depth].shape[1]
        size = int(rng.integers(k - 3, k + 4))
        kind = int(rng.integers(0, 3))
        if kind == 0: Z = list(rng.choice(n, size=size, replace=False))
        elif kind == 1: Z = [8 * b + i for b in rng.choice(n // 8, size=2, replace=False) for i in range(8)]
        else: Z = [8 * int(rng.integers(0, n // 8)) + i for i in range(8)] + list(rng.choice(n, size=size - 8, replace=False))
        Zc, rk = closure(F, Ts[depth], Z)
        if rk == k: continue
        tot += 1
        E = len(Zc) - rk; N = k - rk; sumG = 0; sumD = 0; ok = True
        cur = Zc
        for j in range(depth - 1, -1, -1):
            Gj = Ts[j]; nj, kj = Gj.shape; u1 = 1 << (depth - j - 1)
            s = set(cur)
            Fs = [p for p in range(nj) if 2 * p in s and 2 * p + 1 in s]
            D = [p for p in range(nj) if (2 * p in s) != (2 * p + 1 in s)]
            rkF = rank1(F, Gj[Fs]) if Fs else 0
            rkZ = rank1(F, Ts[j + 1][cur]) if cur else 0
            Gx = 2 * rkF + len(D) - rkZ
            # flatness of F and tightness
            Fc, _ = closure(F, Gj, Fs)
            if Fc != sorted(Fs): ok = False
            for p in D:
                extra = np.zeros((1, 2 * kj), dtype=np.uint8); extra[0, kj:] = Gj[p]
                if rank1(F, np.concatenate([Ts[j + 1][cur], extra])) == rkZ: ok = False
            if D and not (0 <= Gx <= len(D) - 1): ok = False
            if not D and Gx != 0: ok = False
            sumG += u1 * Gx; sumD += u1 * len(D)
            cur = Fs
        # T_0 is the repetition code: e_0 = 0 for sets of nullity >= 1 means cur is empty
        if cur: ok = False
        if sumG != E: ok = False
        if N != k - sumD + sumG: ok = False
        maxE = max(maxE, E)
        bad += (not ok)
    print(f"E2  GF(2^{F.m}) {variant}: n = 32, k = 16, {tot} closures of leaf sets with nullity >= 1 (random, block, mixed): {bad} violations of Lemmas 3.1/3.2; largest excess seen {maxE}")

def e3(F, variant, B, chunk=50000):
    q = F.q
    while True:
        Ts, _ = tree(F, variant, 1, 2); G = Ts[2]
        if is_mds(F, G): break
    # level j: Y = {0,5}, D = {1,2,6,7} (2 null - d = 0); level j+1: two half pairs under the untouched nodes 3 and 4
    Y, D, c = [0, 5], [1, 2, 6, 7], [0, 1, 0, 1]
    nj, kj = G.shape; k1 = 2 * kj
    pos = [2 * p + b for p in Y for b in (0, 1)] + [2 * p + cc for p, cc in zip(D, c)]
    D2 = [2 * 3, 2 * 4 + 1]; c2 = [0, 1]
    rkY = rank1(F, G[Y])
    acc = {"n": 0, "g1": 0, "g2": 0, "both": 0, "s1": 0, "s2": 0, "s3": 0}
    for o in range(0, B, chunk):
        b = min(chunk, B - o)
        tw = draw_twiddles(F, variant, (b, nj)); T1 = split(F, G, tw)
        M = T1[:, pos, :]; rk = brank(F, M.copy()); G1 = 2 * rkY + len(D) - rk
        tight1 = np.ones(b, dtype=bool)
        for p in D:
            extra = np.zeros((b, 1, 2 * kj), dtype=np.uint8); extra[:, 0, kj:] = G[p][None]
            tight1 &= brank(F, np.concatenate([M, extra], axis=1)) > rk
        tw2 = draw_twiddles(F, variant, (b, 2 * nj))
        def child(p, bb):
            g = T1[:, p, :]
            return np.concatenate([g, F.mul[tw2[:, p, bb][:, None], g]], axis=1)
        rows = []
        for p in pos: rows += [child(p, 0), child(p, 1)]
        for p, cc in zip(D2, c2): rows.append(child(p, cc))
        M2 = np.stack(rows, axis=1); rk2 = brank(F, M2.copy())
        G2 = 2 * rk + len(D2) - rk2
        tight2 = np.ones(b, dtype=bool)
        for p in D2:
            extra = np.zeros((b, 1, 2 * k1), dtype=np.uint8); extra[:, 0, k1:] = T1[:, p, :]
            tight2 &= brank(F, np.concatenate([M2, extra], axis=1)) > rk2
        both = tight1 & tight2
        acc["n"] += b; acc["g1"] += int((tight1 & (G1 >= 1)).sum()); acc["g2"] += int((both & (G2 >= 1)).sum())
        acc["both"] += int((both & (G1 >= 1) & (G2 >= 1)).sum())
        for gam in (1, 2, 3): acc[f"s{gam}"] += int((both & (G1 + G2 >= gam)).sum())
    n = acc["n"]; chi = 1 / ((1 - len(D) / q) * (1 - len(D2) / q))
    print(f"E3  GF(2^{F.m}) {variant}: prefix of two levels (d = 4 with 2 null - d = 0, then d' = 2), {n} draws")
    print(f"    P[tight, G >= 1] = {acc['g1']/n:.2e} (bound {q**-1/(1-len(D)/q):.2e});  P[both tight, G' >= 1] = {acc['g2']/n:.2e}")
    print(f"    P[both tight, G >= 1 and G' >= 1] = {acc['both']/n:.2e}   product bound of Lemma 4.1's proof {chi * q ** -2:.2e}")
    for gam in (1, 2, 3):
        print(f"    P[both tight, G + G' >= {gam}] = {acc[f's{gam}']/n:.2e}   Lemma 4.1 bound {min(1.0, math.comb(gam + 1, 1) * chi * q ** -gam):.2e}")

def eps0_toy(b, r, v, J, p, n):
    """Theorem 5.1 with log2 q = b (toy field), chi exact."""
    rho = 2.0 ** -r; L = v - J; nJ1 = 2 ** (J + 1 + r); best = 9.0
    chi = 1.0
    for j in range(J, v): chi /= (1 - 2 ** (j + r) / 2 ** b)
    for t in range(1, 100 * b - 1):
        lam = t / 100.0; C = 0.0
        for _ in range(L): C += math.log2(1 + 2 ** (1 - lam - C / 2))
        main = lam * rho + C / 2 + 0.5 * math.log2(1 + 2 ** (-2 * lam - C))
        eps = 1.0
        for _ in range(50):
            ck = 0.0
            for j in range(J, v):
                om = (2 ** (v - j - 1) - (2 ** (v - j - 2) if j <= v - 2 else 0)) / 2 ** (v - J - 1)
                Gm = math.floor(eps * 2 ** (j + 1 + r))
                ck += om * math.log2(math.comb(Gm + j - J, j - J))
            eps = (main + (math.log2(L * chi / p) + ck) / nJ1) / (b - lam)
        best = min(best, eps)
    return best

def e4(F, variant, codes):
    r, depth = 1, 3   # n = 16, k = 8
    n, k = 16, 8
    hist = {}
    subs = {z: np.array(list(itertools.combinations(range(n), z))) for z in range(k, n)}
    for _ in range(codes):
        Ts, _ = tree(F, variant, r, depth); G = Ts[depth]
        emax = 0
        for z in range(k, n):
            rk = brank(F, G[subs[z]].copy())
            if (rk < k).any(): emax = z - k + 1      # a set of size z with nullity >= 1 has excess >= z - k + 1
            else: break
        hist[emax] = hist.get(emax, 0) + 1
    print(f"E4  GF(2^{F.m}) {variant}: n = 16, k = 8, all levels random (J = 0), {codes} codes. Largest zero set of a nonzero codeword is k - 1 + e:")
    print("    e : " + "  ".join(f"{e}: {c}" for e, c in sorted(hist.items())))
    for p in (0.5, 0.1):
        e0 = eps0_toy(F.m, r, depth, 0, p, n)
        frac = sum(c for e, c in hist.items() if e >= e0 * n) / codes
        print(f"    Theorem 5.1 with q = 2^{F.m}, p = {p}: e < eps_0 n = {e0 * n:.2f}; measured fraction of codes violating it: {frac:.4f}")

if __name__ == "__main__":
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    for m in (4, 8):
        F = GF(m)
        for variant in ("T1", "T2"):
            e1(F, variant, 20000 if quick else 200000)
            e2(F, variant, 100 if quick else 1500)
            e3(F, variant, 20000 if quick else (1000000 if m == 4 else 400000))
            e4(F, variant, 20 if quick else 400)
            sys.stdout.flush()
