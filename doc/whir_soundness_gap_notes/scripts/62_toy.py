#!/usr/bin/env python3
"""Note 62 toy checks, part 1. Usage: python3 62_toy.py prob | lift | pairs | all

prob : Lemma 1.1 by exhaustive enumeration of mu (GF(4), n = 4, windows of 2 points).
lift : Proposition N: periodic triples for XOR windows that do not span (GF(2^8), n = 64),
       the identity c(g Q(L)) = Q(L) c(g), and the same triple under the cube window.
"""
import itertools, random, sys, importlib.util, os

_d = os.path.dirname(os.path.abspath(__file__))
_s = importlib.util.spec_from_file_location("gf62", os.path.join(_d, "62_gf.py"))
gf = importlib.util.module_from_spec(_s)
_s.loader.exec_module(gf)


def codeword(F, pts, windows, mu, coeffs):
    vals = {x: F.ev(coeffs, x) for x in pts}
    out = []
    for i, x in enumerate(pts):
        s = 0
        for l, y in enumerate(windows[i]):
            s ^= F.mul(mu[i][l], vals[y])
        out.append(s)
    return out


def triple_weight(c0, c1, c2):
    """max over words of sum_x (cover count - 1)_+ ; also (u2, u3)."""
    u2 = u3 = 0
    for a, b, c in zip(c0, c1, c2):
        if a == b == c:
            u3 += 1
        elif a == b or a == c or b == c:
            u2 += 1
    return u2 + 2 * u3, u2, u3


def test_prob(rng):
    F = gf.GF(2)
    pts = list(range(4))
    ok = True
    for trial in range(12):
        windows = [[x, rng.choice([y for y in pts if y != x])] for x in pts]
        P = [[rng.randrange(4) for _ in range(3)] for _ in range(3)]
        S = [set(x for x in pts if rng.random() < 0.7) for _ in range(3)]
        dims, centre_only = 0, False
        for i, x in enumerate(pts):
            I = [j for j in range(3) if x in S[j]]
            rows = []
            for j in I[1:]:
                dd = [a ^ b for a, b in zip(P[j], P[I[0]])]
                rows.append([F.ev(dd, y) for y in windows[i]])
            if rows:
                dims += F.rank(rows)
                R, piv = F.rref([r[:] for r in rows])
                centre_only |= any(r[0] and not r[1] for r in R[:len(piv)])
        for model in ("U", "1"):
            free = 8 if model == "U" else 4
            cnt = 0
            for mu_flat in itertools.product(range(4), repeat=free):
                if model == "U":
                    mu = [[mu_flat[2 * i], mu_flat[2 * i + 1]] for i in range(4)]
                else:
                    mu = [[1, mu_flat[i]] for i in range(4)]
                cw = [codeword(F, pts, windows, mu, p) for p in P]
                good = all(len({cw[j][i] for j in range(3) if x in S[j]}) <= 1 for i, x in enumerate(pts))
                cnt += good
            expect = 4 ** (free - dims)
            if model == "1" and centre_only:
                expect = 0
            ok &= (cnt == expect)
            if cnt != expect:
                print("  MISMATCH trial", trial, model, cnt, expect)
    print("prob: Lemma 1.1 exact in model U and model 1 on 12 random patterns:", "OK" if ok else "FAIL")


def test_lift(rng, N=6, m_field=8, k=32):
    F = gf.GF(m_field)
    basis = gf.independent_basis(F, N, rng)
    pts = gf.subspace(basis)
    n = len(pts)
    idx = {x: i for i, x in enumerate(pts)}
    print("lift: GF(2^%d), n = %d, k = %d; weight = max over words of u2 + 2 u3 for the triple (0, gL, t g (L + c1))" % (m_field, n, k))
    for tp, j, model in [(2, 2, "U"), (2, 3, "U"), (3, 4, "U"), (2, 4, "1"), (3, 3, "1"), (N, 4, "U")]:
        C = [0] + basis[:tp]
        windows = [[x ^ c for c in C] for x in pts]
        if model == "U":
            mu = [[rng.randrange(F.q) for _ in C] for _ in pts]
        else:
            mu = [[1] + [rng.randrange(F.q) for _ in C[1:]] for _ in pts]
        Wsub = gf.subspace(basis[:j])
        m = len(Wsub)
        L = gf.subspace_poly(F, Wsub)
        c1, c2 = F.ev(L, basis[j]), F.ev(L, basis[j + 1])
        t = F.mul(c2, F.inv(c1 ^ c2))
        cosets = set(Wsub) | {w ^ basis[j] for w in Wsub} | {w ^ basis[j + 1] for w in Wsub}
        S = [x for x in pts if x not in cosets][: k - m - 1]
        rows = []
        for x in S:
            i = idx[x]
            rows.append([_monomial_cw(F, windows[i], mu[i], e) for e in range(k - m)])
        g = F.nullspace(rows, k - m)[0]
        P1 = gf.poly_mul(F, g, L)
        Lc = L[:]
        Lc[0] ^= c1
        P2 = [F.mul(t, v) for v in gf.poly_mul(F, g, Lc)]
        assert len(P1) <= k and len(P2) <= k
        c0 = [0] * n
        cw1 = codeword(F, pts, windows, mu, P1)
        cw2 = codeword(F, pts, windows, mu, P2)
        w, u2, u3 = triple_weight(c0, cw1, cw2)
        # identity c(g Q(L)) = Q(L) c(g) with Q = L-linear form: check for Q(z) = z
        cg = codeword(F, pts, windows, mu, g)
        ident = all(cw1[i] == F.mul(F.ev(L, x), cg[i]) for i, x in enumerate(pts))
        name = "cube" if tp == N else "local t'=%d" % tp
        print("  %-11s model %s, m = |W''| = %2d: u2 = %2d, u3 = %2d, weight = %3d; 2k = %d, 2k + m - 2 = %d; c(gL) = L c(g): %s"
              % (name, model, m, u2, u3, w, 2 * k, 2 * k + m - 2, ident))


def _monomial_cw(F, window, mu_x, e):
    s = 0
    for l, y in enumerate(window):
        p = 1
        for _ in range(e):
            p = F.mul(p, y)
        s ^= F.mul(mu_x[l], p)
    return s


def test_pairs(rng, N=4, m_field=4, k=4):
    """Theorem A at toy size: largest number of zeros of a nonzero mixed codeword, all q^k codewords,
    against the first-moment bound k + e - 1 at failure probability 1/2 (crude form (i))."""
    import math
    F = gf.GF(m_field)
    q = F.q
    basis = gf.independent_basis(F, N, rng)
    pts = gf.subspace(basis)
    n = len(pts)
    e = 0
    while q ** (e + 1) < 2 * math.comb(n, k + e) * sum(math.comb(k + e, j) for j in range(k)):
        e += 1
    print("pairs: GF(%d), n = %d, k = %d: bound at failure 1/2 is k + e - 1 = %d; trivial lower bound k - 1 = %d" % (q, n, k, k + e - 1, k - 1))
    for name, tp in (("cube", N), ("local t'=2", 2), ("local t'=1", 1)):
        C = [0] + basis[:tp]
        windows = [[x ^ c for c in C] for x in pts]
        res = []
        for trial in range(3):
            mu = [[rng.randrange(q) for _ in C] for _ in pts]
            mono = [[_monomial_cw(F, windows[i], mu[i], ee) for i in range(n)] for ee in range(k)]
            best = 0
            for d_ in range(1, q ** k):
                co = [(d_ >> (m_field * ee)) & (q - 1) for ee in range(k)]
                z = 0
                for i in range(n):
                    v = 0
                    for ee in range(k):
                        if co[ee]:
                            v ^= F.mul(co[ee], mono[ee][i])
                    z += (v == 0)
                if z > best:
                    best = z
            res.append(best)
        print("  %-11s max zeros over all nonzero codewords, 3 samples of mu (model U): %s" % (name, res))


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = random.Random(62)
    if mode in ("prob", "all"):
        test_prob(rng)
    if mode in ("lift", "all"):
        test_lift(rng)
    if mode in ("pairs", "all"):
        test_pairs(rng)
