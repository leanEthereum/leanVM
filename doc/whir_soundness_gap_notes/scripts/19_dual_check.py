#!/usr/bin/env python3
# Researcher 19. Checks of note 19, sections 1 to 3, on small domains.
# Part A (Theorem 1): for random c in L_e, the sparse key theta_i(c) of note 13 Proposition 3.1 equals the
#   dual sum: theta_i^(2^(N-1-e)) = sum over the odd Walsh support Omega of delta_phi * c_i(ker phi), and the
#   triangular form in the power sums P_m(Omega) = sum a_phi^-(2^m - 1), a_phi = 1/delta_phi. Also a_phi additive.
# Part B (Theorems 2, 3): n = 16, every s-subset of a 4-dimensional subspace D of GF(2^m): inside a class of the
#   previous level (equal sums), two sets share e_2 (and e_3) iff P_1 (and P_2) vanish on Omega; the weights of
#   Omega, the distances and the class sizes are compared with the theorems.
# usage: 19_dual_check.py [A|B|all]
import sys, random, itertools
from math import comb
def mk(m, r):
    def mul(a, b):
        z = 0
        while b:
            if b & 1: z ^= a
            b >>= 1; a <<= 1
            if a >> m & 1: a ^= (1 << m) | r
        return z
    def inv(a):
        x, s = 1, mul(a, a)
        for _ in range(m - 1): x = mul(x, s); s = mul(s, s)
        return x
    return mul, inv
FIELDS = {64: 0x1b, 8: 0x1b, 6: 0x3, 5: 0x5, 4: 0x3, 13: 0x1b, 10: 0x9, 7: 0x3}
def span(basis):
    pts = [0]
    for b in basis: pts += [p ^ b for p in pts]
    return pts          # pts[x] for x a coordinate bitmask
def rand_basis(m, N, rng):
    while True:
        b = [rng.getrandbits(m) | 1 if False else rng.randrange(1, 1 << m) for _ in range(N)]
        if len(set(span(b))) == 1 << N: return b
def par(x): return bin(x).count("1") & 1
def dual(mul, inv, pts, N):
    n = 1 << N
    delta = [0] * n
    for phi in range(1, n):
        p = 1
        for x in range(n):
            if par(phi & x): p = mul(p, pts[x])
        delta[phi] = p
    return delta
def lin_coeffs(mul, pts, N, phi):
    # coefficients c_0..c_{N-1} of L_H(Y) = sum c_i Y^(2^(N-1-i)), H = ker phi
    n = 1 << N
    poly = [1]
    for x in range(n):
        if not par(phi & x):
            s = pts[x]; new = [0] * (len(poly) + 1)
            for i, c in enumerate(poly):
                new[i + 1] ^= c; new[i] ^= mul(c, s)
            poly = new
    return [poly[1 << (N - 1 - i)] for i in range(N)]
def series_Lambda(mul, inv, pts, c, prec):
    # prod (1 - s X)^c(s) mod X^prec
    def smul(a, b):
        r = [0] * prec
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if i + j >= prec: break
                    if y: r[i + j] ^= mul(x, y)
        return r
    def sinv(a):
        r = [0] * prec; r[0] = 1
        for k in range(1, prec):
            t = 0
            for j in range(1, k + 1):
                if a[j] and r[k - j]: t ^= mul(a[j], r[k - j])
            r[k] = t
        return r
    num = [0] * prec; num[0] = 1; den = [0] * prec; den[0] = 1
    for x, e in enumerate(c):
        if e == 0 or pts[x] == 0: continue
        f = [0] * prec; f[0] = 1
        if prec > 1: f[1] = pts[x]
        tgt = num if e > 0 else den
        for _ in range(abs(e)): tgt[:] = smul(tgt, f)
    return smul(num, sinv(den))
def partA():
    rng = random.Random(19); tests = 0
    for (m, N, shape) in [(64, 5, "power"), (64, 5, "rand"), (13, 5, "power"), (8, 5, "rand"), (64, 6, "power"), (10, 6, "rand")]:
        mul, inv = mk(m, FIELDS[m]); n = 1 << N
        basis = [1 << i for i in range(N)] if shape == "power" else rand_basis(m, N, rng)
        pts = span(basis); delta = dual(mul, inv, pts, N)
        a = [0] + [inv(delta[p]) for p in range(1, n)]
        for p in range(1, n):
            for q in range(1, p): assert a[p] ^ a[q] == a[p ^ q], "a not additive"
        ci = [None] + [lin_coeffs(mul, pts, N, p) for p in range(1, n)]
        LD = [1]
        for x in range(n):
            new = [0] * (len(LD) + 1)
            for i, cc in enumerate(LD): new[i + 1] ^= cc; new[i] ^= mul(cc, pts[x])
            LD = new
        Dc = [LD[1 << (N - i)] for i in range(N + 1)]
        def powr(x, k):
            for _ in range(k): x = mul(x, x)
            return x
        def ipow(x, e):
            r = 1
            while e:
                if e & 1: r = mul(r, x)
                x = mul(x, x); e >>= 1
            return r
        for e in range(1, N - 1):
            for trial in range(3):
                c = [0] * n
                for _ in range(6):
                    A = rng.randrange(1, n); sz = bin(A).count("1"); k = rng.choice([-1, 1, 1, 2, 3])
                    mult = k * (1 << max(0, e + 1 - sz))
                    for x in range(n):
                        if x & ~A == 0: c[x] += mult * (-1) ** (sz - bin(x).count("1"))
                prec = 1 << (e + 1)
                lam = series_Lambda(mul, inv, pts, c, prec)
                pos = {(1 << (e + 1)) - (1 << (e - i)): i for i in range(e + 1)}
                for j in range(1, prec):
                    if j not in pos: assert lam[j] == 0, "support"
                chat = [sum(c[x] * (-1) ** par(p & x) for x in range(n)) for p in range(n)]
                assert chat[0] == 0 and all(v % (1 << (e + 1)) == 0 for v in chat)
                Om = [p for p in range(1, n) if (chat[p] >> (e + 1)) & 1]
                P = [None] + [0] * (e + 2)
                for mm in range(1, e + 2):
                    for p in Om: P[mm] ^= ipow(delta[p], (1 << mm) - 1)
                for j, i in pos.items():
                    lhs = powr(lam[j], N - 1 - e); rhs = 0
                    for p in Om: rhs ^= mul(delta[p], ci[p][i])
                    assert lhs == rhs, ("theorem 1", m, N, e, i)
                    tri = P[i + 1]
                    for jj in range(1, i + 1): tri ^= mul(powr(Dc[jj], jj - 1), powr(P[i + 1 - jj], jj))
                    assert powr(lhs, i) == tri, ("triangular", m, N, e, i)
                    tests += 1
                # moments of Omega: sum a^t = 0 for binary weight of t at most N - e - 2
                for t in range(0, 16):
                    if bin(t).count("1") <= N - e - 2:
                        sm = 0
                        for p in Om: sm ^= ipow(a[p], t)
                        assert sm == 0, ("moment", t)
    print("part A: %d identities checked (Theorem 1, triangular form, moments, additivity of a)" % tests)
def partB():
    rng = random.Random(1919); N = 4; n = 16
    tot = {}
    cases = [(4, "rand")] * 3 + [(5, "rand")] * 6 + [(6, "rand")] * 6 + [(8, "rand")] * 4 + [(8, "power"), (13, "power"), (64, "power"), (64, "rand")]
    for (m, shape) in cases:
        mul, inv = mk(m, FIELDS[m])
        basis = [1 << i for i in range(N)] if shape == "power" else rand_basis(m, N, rng)
        pts = span(basis); delta = dual(mul, inv, pts, N)
        a = [0] + [inv(delta[p]) for p in range(1, n)]
        ia = [0] + [delta[p] for p in range(1, n)]
        ia3 = [0] + [mul(d, mul(d, d)) for d in ia[1:]]
        P1 = [0] * (1 << 15); P2 = [0] * (1 << 15)
        for mask in range(1, 1 << 15):
            low = mask & -mask; b = low.bit_length()   # functional b = 1..15
            P1[mask] = P1[mask ^ low] ^ ia[b]; P2[mask] = P2[mask ^ low] ^ ia3[b]
        for s in range(3, 9):
            groups = {}
            for S in itertools.combinations(range(n), s):
                e1 = e2 = e3 = 0
                for x in S:
                    v = pts[x]; e3 ^= mul(e2, v); e2 ^= mul(e1, v); e1 ^= v
                b2 = 0; xs = 0
                for x in S: xs ^= x
                for p in range(1, n):
                    np_ = sum(par(p & x) for x in S)
                    if np_ & 2: b2 |= 1 << (p - 1)
                bits = 0
                for x in S: bits |= 1 << x
                groups.setdefault(xs, []).append((e2, e3, b2, bits))
            st = tot.setdefault(s, dict(pairs=0, nf2=0, nf3=0, w={}, max2=0, max3=0, mind2=99, mind3=99))
            for xs, L in groups.items():
                cl2 = {}; cl3 = {}
                for i in range(len(L)):
                    e2, e3, b2, bits = L[i]
                    cl2.setdefault(e2, []).append(i); cl3.setdefault((e2, e3), []).append(i)
                    for j in range(i):
                        f2, f3, c2, bj = L[j]; om = b2 ^ c2
                        same2 = e2 == f2; same3 = same2 and e3 == f3
                        assert same2 == (P1[om] == 0), "criterion depth 2"
                        assert same3 == (P1[om] == 0 and P2[om] == 0), "criterion depth 3"
                        st["pairs"] += 1
                        if same2:
                            w = bin(om).count("1"); dist = bin(bits ^ bj).count("1")
                            st["w"][(w, dist, same3)] = st["w"].get((w, dist, same3), 0) + 1
                            assert w == 0 or w >= 6
                            assert dist >= 6
                            st["mind2"] = min(st["mind2"], dist)
                            if same3:
                                assert w == 0 or w >= 8; assert dist >= 8; st["mind3"] = min(st["mind3"], dist)
                st["max2"] = max(st["max2"], max(len(v) for v in cl2.values()))
                st["max3"] = max(st["max3"], max(len(v) for v in cl3.values()))
    print("part B: n = 16, %d domains (fields of degree 4, 5, 6, 8, 13, 64); the criterion held for every pair" % len(cases))
    print(" s | pairs in a previous-level class | largest class depth 2, bound | largest class depth 3, bound | min distance depth 2, 3 | (|Omega|, distance, also depth 3): pairs")
    for s in sorted(tot):
        st = tot[s]; rho2 = s * (16 - s) / 16.0; sm = min(s, 16 - s)
        b3 = int(1 / (1 - 2 * sm / 16.0) ** 2 + 1e-9) if sm != 8 else None
        b2 = int(3 / (3 - rho2) + 1e-9) if rho2 < 3 else None
        if b3 is not None: assert st["max3"] <= b3
        if b2 is not None: assert st["max2"] <= b2
        print(" %d | %d | %d, %s | %d, %s | %s, %s | %s" % (s, st["pairs"], st["max2"], b2, st["max3"], b3, st["mind2"], st["mind3"], sorted(st["w"].items())))
if __name__ == "__main__":
    w = sys.argv[1] if len(sys.argv) > 1 else "all"
    if w in ("A", "all"): partA()
    if w in ("B", "all"): partB()
