# Researcher 21 (referee). Independent checks for the real-domain notes (13, 19), the biased padding of note 01,
# the phantom-root congruence of note 04, and the constants of note 19 Theorem 3b.
# Usage: python3 21_real_checks.py padding | padfield | pair | sparse | curve | consts | phantom | all
import importlib
import itertools
import random
import sys
from fractions import Fraction
from math import floor

sys.dont_write_bytecode = True
gf = importlib.import_module("21_gf")
K = gf.K64


def par(x):
    return bin(x).count("1") & 1


def check_padding():
    # note 01, 3.4: labels (x, y) in GF(64)^2 with the two low bits of x*y equal to 11.
    F6 = gf.small_field(6)
    B = [0] * 4096
    for x in range(64):
        for y in range(64):
            if F6.mul(x, y) & 3 == 3:
                B[x | (y << 6)] = 1
    size = sum(B)
    w = B[:]
    h = 1
    while h < 4096:  # Walsh-Hadamard transform
        for i in range(0, 4096, 2 * h):
            for j in range(i, i + h):
                a, b = w[j], w[j + h]
                w[j], w[j + h] = a + b, a - b
        h *= 2
    hist = {}
    for a in range(1, 4096):
        hist[abs(w[a])] = hist.get(abs(w[a]), 0) + 1
    print(f"biased padding: |B| = {size} of 4096 labels (not n/4 = 1024), nonzero Walsh values by absolute value: {sorted(hist.items())}")
    big = max(hist)
    L = hist[big]
    # |H u B| = n/2 + |B| - |B n H|, |B n H| = (|B| - |hat B|)/2 for the better coset
    agree = Fraction(1, 2) + Fraction(size + big, 2 * 4096)
    degree = Fraction(1, 4) + Fraction(size, 4096)
    print(f"   {L} directions with |hat B| = {big}: agreement fraction {float(agree):.5f} = {agree}, degree of the codewords <= {float(degree):.5f} n"
          f" ({'genuine: below n/2' if degree < Fraction(1, 2) else 'degree n/2: slack 1'})")
    print(f"   Parseval cap of note 01 for L = {L} with |B| = n/4: 5/8 + sqrt(3/(64 L)) = {0.625 + (3 / (64 * L)) ** 0.5:.5f}")
    # the same construction over GF(2^m')^2 for other sizes: L = 4^(m'-1) - 2^(m'-2) members at 5/8 + 2^(-m'-2)
    for mp in (4, 5, 7, 8):
        Fm = gf.small_field(mp)
        q = 1 << mp
        M = q * q
        ww = [0] * M
        for x in range(q):
            for y in range(q):
                if Fm.mul(x, y) & 3 == 3:
                    ww[x | (y << mp)] = 1
        sz = sum(ww)
        h = 1
        while h < M:
            for i in range(0, M, 2 * h):
                for j in range(i, i + h):
                    a, b = ww[j], ww[j + h]
                    ww[j], ww[j + h] = a + b, a - b
            h *= 2
        bg = max(abs(v) for v in ww[1:])
        Lm = sum(1 for v in ww[1:] if abs(v) == bg)
        tau = Fraction(1, 2) + Fraction(sz + bg, 2 * M)
        eps = tau - Fraction(5, 8)
        assert Lm == sz == M // 4 - q // 4 and eps == Fraction(1, 4 * q)
        print(f"   m'={mp}: |B| = {sz} of {M}, L = {Lm} directions, tau = {tau} = 5/8 + {eps}, L eps^2 = {float(Lm * eps * eps):.5f}"
              f" (1/64 = {1 / 64:.5f}; Parseval cap 3/64 = {3 / 64:.5f}; Theorem A of note 12: 1/16)")
    # field check of the identity on a small instance: N = 8, random B of size n/4 and n/4 - 3, a few hyperplanes
    rng = random.Random(34)
    N, n = 8, 256
    D = gf.span(gf.power_basis(N))
    for bsize in (n // 4, n // 4 - 3):
        Bset = set(rng.sample(range(n), bsize))
        LB = gf.locator(K, [D[i] for i in Bset])
        for _ in range(3):
            phi = rng.randrange(1, n)
            c = rng.randrange(2)
            H = [i for i in range(n) if par(i & phi) == c]
            LH = gf.locator(K, [D[i] for i in H])
            LH[n // 2] ^= 1  # L_H - X^(n/2): degree <= n/4
            assert gf.deg(LH) <= n // 4
            cw = gf.poly_mul(K, LB, LH)
            word = [0] * (n // 2) + LB  # X^(n/2) L_B
            agree = sum(1 for i in range(n) if gf.poly_eval(K, cw, D[i]) == gf.poly_eval(K, word, D[i]))
            assert agree == len(Bset | set(H)) and gf.deg(cw) <= bsize + n // 4
        print(f"   identity checked at N=8, |B| = {bsize}: codeword degree <= |B| + n/4 = {bsize + n // 4}, agreement exactly |H u B|")


def check_padfield():
    # the closed-form padding family end to end at N = 8, m' = 4: D = span(1..x^7) in K, a point index i is the label
    # (x, y) = (i & 15, i >> 4) in GF(16)^2, B = {two low bits of x*y are 11}
    N, n, mp = 8, 256, 4
    Fm = gf.small_field(mp)
    D = gf.span(gf.power_basis(N))
    B = [i for i in range(n) if Fm.mul(i & 15, i >> 4) & 3 == 3]
    LB = gf.locator(K, [D[i] for i in B])
    word = [0] * (n // 2) + LB  # X^(n/2) L_B
    wv = [gf.poly_eval(K, word, x) for x in D]
    Bs = set(B)
    members = set()
    for phi in range(1, n):
        hatB = len(B) - 2 * sum(1 for i in B if par(i & phi))
        if abs(hatB) != 12:
            continue
        c = 1 if hatB > 0 else 0  # the coset of the hyperplane that contains fewer points of B
        H = [i for i in range(n) if par(i & phi) == c]
        LH = gf.locator(K, [D[i] for i in H])
        LH[n // 2] ^= 1
        cw = gf.poly_mul(K, LB, LH)
        agree = sum(1 for i in range(n) if gf.poly_eval(K, cw, D[i]) == wv[i])
        assert gf.deg(cw) <= n // 2 - n // 64 and agree == 41 * n // 64 == len(Bs | set(H))
        members.add(tuple(cw))
    assert len(members) == 60 == len(B)
    print(f"closed-form padding family, N=8, m'=4, leanVM shape in K: |B| = {len(B)}; {len(members)} distinct codewords of degree <= n/2 - n/64 = {n // 2 - n // 64}, "
          f"each agreeing with the one word X^(n/2) L_B on exactly 41n/64 = {41 * n // 64} points")


def kernel_basis(N, funcs):
    """Basis (bit masks) of the common kernel in F_2^N of the functionals given as callables on masks."""
    # Gaussian elimination on the matrix [f_j(e_i)]
    rows = [(sum(f(1 << i) << j for j, f in enumerate(funcs)), 1 << i) for i in range(N)]
    basis = []
    piv = {}
    for val, vec in rows:
        while val:
            h = val.bit_length()
            if h in piv:
                pv, pvec = piv[h]
                val ^= pv
                vec ^= pvec
            else:
                piv[h] = (val, vec)
                break
        if val == 0:
            basis.append(vec)
    return basis


def check_pair():
    # note 19, Proposition 5.1: V = {f : f(0) = f(1) = f_{N-1}}, V' = (x^2 + x + 1) F_2[x]_{<N-2} inside D = F_2[x]_{<N} in K.
    for N in (25, 26, 27, 28):
        f0 = lambda v: v & 1
        f1 = lambda v: par(v)
        ft = lambda v: (v >> (N - 1)) & 1
        V = kernel_basis(N, [lambda v: f0(v) ^ ft(v), lambda v: f1(v) ^ ft(v)])
        Vp = [7 << i for i in range(N - 2)]
        assert len(V) == N - 2
        # intersection dimension by rank
        def rank(vs):
            piv = {}
            r = 0
            for x in vs:
                while x:
                    h = x.bit_length()
                    if h in piv:
                        x ^= piv[h]
                    else:
                        piv[h] = x
                        r += 1
                        break
            return r
        inter = 2 * (N - 2) - rank(V + Vp)
        cV = gf.lin_poly(K, V)
        cVp = gf.lin_poly(K, Vp)
        # L_V = X^(n/4) + c1 X^(n/8) + c2 X^(n/16) + ...: c[j] is the coefficient of X^(2^j)
        c1, c1p = cV[N - 3], cVp[N - 3]
        c2, c2p = cV[N - 4], cVp[N - 4]
        print(f"N={N}: |V| = |V'| = n/4, dim(V n V') = {inter} (n/16 points: {inter == N - 4}); c1(V) = {c1:016x}, c1(V') = {c1p:016x}, equal: {c1 == c1p};"
              f" c2 equal: {c2 == c2p}")
        assert c1 == c1p and inter == N - 4 and c2 != c2p
    # small N: multiply out Z_A - Z_B (A = V \ V', B = V' \ V) and check it is a nonzero constant; also the dual statement
    for N in (6, 7, 8, 9):
        n = 1 << N
        ft = lambda v: (v >> (N - 1)) & 1
        V = set(gf.span(kernel_basis(N, [lambda v: (v & 1) ^ ft(v), lambda v: par(v) ^ ft(v)])))
        Vp = set(gf.span([7 << i for i in range(N - 2)]))
        A, B = sorted(V - Vp), sorted(Vp - V)
        ZA, ZB = gf.locator(K, A), gf.locator(K, B)
        diff = [a ^ b for a, b in zip(ZA, ZB)]
        assert len(A) == len(B) == 3 * n // 16 and gf.deg(diff) == 0
        # the six dual points: functionals vanishing on V or on V'
        D = list(range(n))
        tot = tot3 = 0
        cnt = 0
        for phi in range(1, n):
            ker = [x for x in D if par(x & phi) == 0]
            if V <= set(ker) or Vp <= set(ker):
                # delta_phi = product of the points outside the kernel
                d = 1
                for x in D:
                    if par(x & phi):
                        d = K.mul(d, x)
                tot ^= d
                tot3 ^= K.mul(d, K.sqr(d))
                cnt += 1
        assert cnt == 6 and tot == 0 and tot3 != 0
        print(f"N={N}: Z_A - Z_B is a nonzero constant (|A| = |B| = 3n/16 = {len(A)}); the six dual points have sum of 1/a = 0 and sum of 1/a^3 != 0")


def series_mul(F, a, b, prec):
    r = [0] * prec
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if i + j >= prec:
                    break
                if y:
                    r[i + j] ^= F.mul(x, y)
    return r


def series_inv(F, a, prec):
    assert a[0] == 1
    r = [1] + [0] * (prec - 1)
    for i in range(1, prec):
        s = 0
        for j in range(1, i + 1):
            if a[j] and r[i - j]:
                s ^= F.mul(a[j], r[i - j])
        r[i] = s
    return r


def lam(F, D, c, prec):
    """prod (1 + s X)^c(s) mod X^prec for an integer vector c on the points D."""
    num = [1] + [0] * (prec - 1)
    den = [1] + [0] * (prec - 1)
    for s, cs in zip(D, c):
        if s == 0 or cs == 0:
            continue
        fac = [1, s] + [0] * (prec - 2)
        for _ in range(abs(cs)):
            if cs > 0:
                num = series_mul(F, num, fac, prec)
            else:
                den = series_mul(F, den, fac, prec)
    return series_mul(F, num, series_inv(F, den, prec), prec)


def random_Le(N, e, rng, terms=6):
    n = 1 << N
    c = [0] * n
    for _ in range(terms):
        a = rng.randrange(1, N + 1)
        A = rng.sample(range(N), a)
        coef = rng.choice([-2, -1, 1, 2, 3]) * (1 << max(0, e + 1 - a))
        # eps_A = prod_{i in A} ([b_i] - [0])
        for sub in range(1 << a):
            x = 0
            for j in range(a):
                if sub >> j & 1:
                    x |= 1 << A[j]
            c[x] += coef * (-1) ** (a - bin(sub).count("1"))
    return c


def check_sparse():
    # note 13, Proposition 3.1: for c in L_e the series Lambda_c is 1 + sum_i theta_i X^(2^(e+1) - 2^(e-i)) mod X^(2^(e+1)).
    rng = random.Random(13)
    tot = 0
    for N in (5, 6):
        n = 1 << N
        for name, F, basis in (("leanVM shape in K", K, gf.power_basis(N)), ("random basis in K", K, gf.random_basis(K, N, rng)),
                               ("GF(2^8)", gf.small_field(8), gf.random_basis(gf.small_field(8), N, rng))):
            D = gf.span(basis)
            for e in range(1, N - 1):
                prec = 1 << (e + 1)
                allowed = {0} | {prec - (1 << (e - i)) for i in range(e + 1)}
                for _ in range(4 if N == 5 else 2):
                    c1, c2 = random_Le(N, e, rng), random_Le(N, e, rng)
                    # membership in L_e: sum zero and Walsh transform divisible by 2^(e+1)
                    for c in (c1, c2):
                        assert sum(c) == 0
                        for phi in range(n):
                            assert sum(cx * (-1) ** par(x & phi) for x, cx in enumerate(c)) % (1 << (e + 1)) == 0
                    l1, l2 = lam(F, D, c1, prec), lam(F, D, c2, prec)
                    l12 = lam(F, D, [a + b for a, b in zip(c1, c2)], prec)
                    for l in (l1, l2, l12):
                        assert all(v == 0 for j, v in enumerate(l) if j not in allowed), (N, e)
                        assert l[0] == 1
                    assert all(l12[j] == l1[j] ^ l2[j] for j in allowed if j)
                    tot += 1
            print(f"sparse keys N={N}, {name}: levels e=1..{N - 2}: support and additivity as stated")
    print(f"   {tot} pairs of lattice elements checked")


def check_curve():
    # note 13, section 2 and Proposition 4.1.
    # (i) the masks: labels a = (a0; a1, a2, a3) in F_2^4, label value eta*(a0 + a1 t1 + a2 t2 + a3 t3); Y: 10-sets with sum eta.
    labels = list(range(16))  # bit 0 = a0 (the eta coordinate), bits 1..3 = a1..a3
    cls = {}
    for Y in itertools.combinations(labels, 10):
        sx = 0
        for y in Y:
            sx ^= y
        if sx != 1:
            continue
        nn = [sum(y >> i & 1 for y in Y) for i in range(4)]
        mask = []
        for i in range(4):
            mask.append((nn[i] * (nn[i] - 1) // 2) & 1)
        for i in range(4):
            for j in range(i + 1, 4):
                nij = sum((y >> i & 1) & (y >> j & 1) for y in Y)
                mask.append((nn[i] * nn[j] - nij) & 1)
        cls.setdefault(tuple(mask), []).append(Y)
    sizes = sorted(len(v) for v in cls.values())
    nsets = sum(sizes)
    # vanishing masks: c00 = 0, c_ij = 0 for 1 <= i < j, c_0i = c_ii.  mask order: c00,c11,c22,c33,c01,c02,c03,c12,c13,c23
    van = [m for m in cls if m[0] == 0 and m[7] == m[8] == m[9] == 0 and m[4] == m[1] and m[5] == m[2] and m[6] == m[3]]
    inv = lambda Y: all((y ^ 1) in Y for y in Y)
    van_ok = all(all(inv(Y) for Y in cls[m]) for m in van)
    inv_sets = sum(1 for v in cls.values() for Y in v if inv(Y))
    print(f"5n/8 class, label sets per hyperplane: {nsets} sets in {len(cls)} masks; class sizes {sorted(set(sizes))} "
          f"({sizes.count(7)} of 7, {sizes.count(2)} of 2); masks on which Q_c - v*alpha can vanish identically: {len(van)}, "
          f"all their sets invariant under eta: {van_ok}; invariant sets in all: {inv_sets}")
    assert nsets == 504 and len(cls) == 232 and sizes.count(7) == 8 and sizes.count(2) == 224 and len(van) == 8 and van_ok and inv_sets == 56
    assert all(len(cls[m]) == 7 for m in van)
    bound = 7 + 16 * 224
    print(f"   so the bound is 7 + 224 * 8 hyperplanes * 2 sets = {bound}")
    # (ii) field check of Lemma 2.1 and of e_(n/8) = eta^2 Q_c(1, t), and the curve equations, N = 6, 7
    rng = random.Random(41)
    for N, F, name in ((6, K, "K, leanVM shape"), (7, K, "K, leanVM shape"), (7, gf.small_field(10), "GF(2^10), leanVM shape")):
        n = 1 << N
        D = gf.span(gf.power_basis(N))
        # U = span of N-3 random independent points; v1..v3 complete to a basis of D
        while True:
            vecs = [rng.randrange(1, n) for _ in range(N)]
            if len(set(gf.span(vecs))) == n:
                break
        Ub, vs = vecs[:N - 3], vecs[N - 3:]
        LU = gf.lin_poly(F, Ub)
        lam_i = [gf.lin_eval(F, LU, v) for v in vs]
        checked = 0
        for hyp in range(1, 1 << (N - 3)):  # functional on U (coordinates w.r.t. Ub) defining W
            # basis of W = kernel of hyp
            Wb = kernel_basis(N - 3, [lambda v, h=hyp: par(v & h)])
            Wpts = []
            for wv in Wb:
                x = 0
                for j in range(N - 3):
                    if wv >> j & 1:
                        x ^= Ub[j]
                Wpts.append(x)
            LW = gf.lin_poly(F, Wpts)
            # eta = L_W(u) for u in U \ W
            u = next(Ub[j] for j in range(N - 3) if hyp >> j & 1)
            eta = gf.lin_eval(F, LW, u)
            alpha = F.inv(F.sqr(eta))
            ts = [F.mul(gf.lin_eval(F, LW, v), F.inv(eta)) for v in vs]
            for t, l in zip(ts, lam_i):
                assert F.sqr(t) ^ t == F.mul(l, alpha)  # the curve
            if checked >= 12:
                continue
            # one label set per mask sample: label value of a = eta*(a0 + sum a_i t_i); points S = L_W^{-1}(Y)
            labval = {}
            for a in range(16):
                v = a & 1
                for i in range(3):
                    if a >> (i + 1) & 1:
                        v ^= ts[i]
                labval[a] = F.mul(eta, v)
            lw_of = {x: gf.lin_eval(F, LW, x) for x in D}
            m = rng.choice(list(cls))
            Y = rng.choice(cls[m])
            Yv = {labval[a] for a in Y}
            S = [x for x in D if lw_of[x] in Yv]
            assert len(S) == 5 * n // 8
            e = gf.top_coeffs(F, S, n // 8)
            e2 = 0
            Yl = [labval[a] for a in Y]
            for i in range(10):
                for j in range(i + 1, 10):
                    e2 ^= F.mul(Yl[i], Yl[j])
            assert e[n // 8] == e2  # Lemma 2.1
            tt = [1] + ts
            q = 0
            idx = 4
            for i in range(4):
                if m[i]:
                    q ^= F.sqr(tt[i])
            for i in range(4):
                for j in range(i + 1, 4):
                    if m[idx]:
                        q ^= F.mul(tt[i], tt[j])
                    idx += 1
            assert e2 == F.mul(F.sqr(eta), q)  # e_(n/8) = eta^2 Q_c(1, t)
            checked += 1
        print(f"   N={N}, {name}: all {(1 << (N - 3)) - 1} hyperplanes lie on the curve t_i^2 + t_i = lambda_i alpha; Lemma 2.1 and the Q_c formula on {checked} random (W, Y)")
    # (iii) fibres in a field where coincidences abound: D = GF(2^m) itself, N = m
    for m_ in (9, 10, 12):
        F = gf.small_field(m_)
        N = m_
        n = 1 << N
        while True:
            vecs = [rng.randrange(1, n) for _ in range(N)]
            if len(set(gf.span(vecs))) == n:
                break
        Ub, vs = vecs[:N - 3], vecs[N - 3:]
        LU = gf.lin_poly(F, Ub)
        lam_i = [gf.lin_eval(F, LU, v) for v in vs]
        assert len(set(gf.span(lam_i))) == 8
        per_mask = {}
        fibre = {}
        masks = [mm for mm in cls if mm not in van]
        for hyp in range(1, 1 << (N - 3)):
            Wb = kernel_basis(N - 3, [lambda v, h=hyp: par(v & h)])
            Wpts = []
            for wv in Wb:
                x = 0
                for j in range(N - 3):
                    if wv >> j & 1:
                        x ^= Ub[j]
                Wpts.append(x)
            LW = gf.lin_poly(F, Wpts)
            u = next(Ub[j] for j in range(N - 3) if hyp >> j & 1)
            eta = gf.lin_eval(F, LW, u)
            ie = F.inv(eta)
            tt = [1] + [F.mul(gf.lin_eval(F, LW, v), ie) for v in vs]
            sq = [F.sqr(x) for x in tt]
            pr = {}
            for i in range(4):
                for j in range(i + 1, 4):
                    pr[(i, j)] = F.mul(tt[i], tt[j])
            e2 = F.sqr(eta)
            for mm in masks:
                q = 0
                for i in range(4):
                    if mm[i]:
                        q ^= sq[i]
                idx = 4
                for i in range(4):
                    for j in range(i + 1, 4):
                        if mm[idx]:
                            q ^= pr[(i, j)]
                        idx += 1
                v = F.mul(e2, q)
                per_mask[(mm, v)] = per_mask.get((mm, v), 0) + 1
                fibre[v] = fibre.get(v, 0) + 2
        # invariant classes: value sum c_ii lambda_i (independent of W), 7 sets each
        for mm in van:
            v = 0
            for i in range(1, 4):
                if mm[i]:
                    v ^= lam_i[i - 1]
            fibre[v] = fibre.get(v, 0) + 7
        print(f"   D = GF(2^{m_}): {(1 << (N - 3)) - 1} hyperplanes; most hyperplanes on one (mask, value): {max(per_mask.values())} (Bezout bound 8);"
              f" largest fibre of e_(n/8) on the class: {max(fibre.values())} sets (bound {bound})")
        assert max(per_mask.values()) <= 8 and max(fibre.values()) <= bound


def check_consts():
    # note 19, Theorem 3b: L <= J (min(J, 32) Q + 1) with the four factors of Q bounded separately over each range (in units u = n/16).
    def bound(lo, hi, lo_open, hi_open):
        # sup over s in the range of each factor, then floors; rho^2 = s(16 - s)/16, m1 = s/4, kappa = min(s-4, 8-s)/4
        import math
        xs = [Fraction(lo) + Fraction(hi - lo) * Fraction(i, 20000) for i in range(20001)]
        if lo_open:
            xs = xs[1:]
        if hi_open:
            xs = xs[:-1]
        rho2 = [x * (16 - x) / 16 for x in xs]
        J = max(floor(1 / (1 - x / 8) ** 2) for x in xs)
        f1 = max(floor(4 * r) for r in rho2)
        f2 = max(floor(25 * r / (3 - x / 4) ** 2) for x, r in zip(xs, rho2))
        f3 = max(floor(16 * r) for r in rho2)
        f4sep = max(rho2) * 9 / min(min(x - 4, 8 - x) / 4 for x in xs) ** 2
        f4 = max(floor(9 * r / (min(x - 4, 8 - x) / 4) ** 2) for x, r in zip(xs, rho2))
        return J, f1, f2, f3, f4, f4sep
    for name, lo, hi, lo_open, hi_open, claimed in (("rate 1/2, T in (5n/8, 11n/16): s in (5u, 6u)", 5, 6, True, True, 4107099165),
                                                    ("rate 1/4, T in [3n/8, 7n/16): s in [6u, 7u)", 6, 7, False, True, 65793289023)):
        J, f1, f2, f3, f4, f4sep = bound(lo, hi, lo_open, hi_open)
        L_point = J * (min(J, 32) * f1 * f2 * f3 * f4 + 1)
        print(f"Theorem 3b constants, {name}: J <= {J}, factors <= {f1}, {f2}, {f3}, pointwise fourth factor <= {f4} (separate sup of rho^2 and inf of kappa: < {float(f4sep):.1f})")
        print(f"   bound with the pointwise fourth factor: {L_point} = 2^{__import__('math').log2(L_point):.2f}; note 19 claims {claimed} = 2^{__import__('math').log2(claimed):.2f}")
    s = 6
    r = Fraction(s * (16 - s), 16)
    Q = floor(4 * r) * floor(25 * r / (3 - Fraction(s, 4)) ** 2) * floor(16 * r) * floor(9 * r / Fraction(1, 4))
    print(f"   at s = 6u exactly (T = 5n/8, degree < n/2): J = 16, Q = {Q}, bound {16 * (16 * Q + 1)}")
    # Theorem 3a and 3c values
    print(f"   Theorem 3a: 1/(1-2s/n)^2 at s = 5n/16: {float(1 / (1 - Fraction(5, 8)) ** 2):.3f}; at tau = 0.3536 (rate 1/8): {1 / (1 - 2 * 0.35355) ** 2:.3f}")
    print(f"   Theorem 3c: 3/(16(3/4-tau)(1/4-tau)) at tau = 3/16: {float(Fraction(3) / (16 * Fraction(9, 16) * Fraction(1, 16))):.3f}; at 7/32: {float(Fraction(3) / (16 * Fraction(17, 32) * Fraction(1, 32))):.3f}")
    # Theorem I special values of N_{L,g}: [g,2g) -> 1, [2g,3g) -> L, [3g,4g) -> 2L-1, [4g,5g) -> L^2+L-1
    def Nrec(phi, g, L, memo={}):
        if phi < 2 * g:
            return 1
        key = (phi, g, L)
        if key not in memo:
            memo[key] = Nrec(phi - g, g, L) + (L - 1) * Nrec(phi // 2, g, L)
        return memo[key]
    g = 100
    for L in (2, 5, 17):
        assert all(Nrec(p, g, L) == 1 for p in range(g, 2 * g))
        assert all(Nrec(p, g, L) == L for p in range(2 * g, 3 * g))
        assert all(Nrec(p, g, L) == 2 * L - 1 for p in range(3 * g, 4 * g))
        assert all(Nrec(p, g, L) == L * L + L - 1 for p in range(4 * g, 5 * g))
    print("   note 14 Theorem I: recursion values 1, L, 2L-1, L^2+L-1 on [g,2g), [2g,3g), [3g,4g), [4g,5g) confirmed")


def check_phantom():
    # note 04, Theorem 2.4 with one phantom root (r = 1), n = 16, random domain: pairs of T-sets S1, S2 with
    # deg((X - z1) Z_S1 - (X - z2) Z_S2) < k for some z1, z2 in K. Then d = n_phi(S1) - n_phi(S2) mod 2^(a+1) lies in [-1, 1].
    rng = random.Random(4)
    N, n = 4, 16
    F = K
    D = gf.span(gf.random_basis(F, N, rng))
    for T, k in ((12, 10), (12, 9), (5, 3), (4, 2)):
        m = T - k
        r = 1
        a = m.bit_length() - 1
        # part 2 of the theorem (modulus 2^(a+1)) when m + r < 2^(a+1), otherwise part 3 (largest power of two <= m + 1)
        mod = 1 << (a + 1) if m + r < 1 << (a + 1) else 1 << ((m + 1).bit_length() - 1)
        sets = list(itertools.combinations(range(n), T))
        es = [gf.top_coeffs(F, [D[i] for i in S], m + 1) for S in sets]
        nphi = [[sum(1 for i in S if par(i & phi)) for phi in range(1, n)] for S in sets]
        pairs = strict = bad = 0
        maxabs = 0
        for i in range(len(sets)):
            e = es[i]
            for j in range(i + 1, len(sets)):
                f = es[j]
                # (1 + z1 Z)(1 + e1 Z + ...) = (1 + z2 Z)(1 + f1 Z + ...) mod Z^(m+2): coefficients 1..m+1
                # j=1: z1 + e1 = z2 + f1.  j=2: e2 + z1 e1 = f2 + z2 f1  => z1 (e1 + f1) = e2 + f2 + f1 (e1 + f1)
                d1 = e[1] ^ f[1]
                if d1 == 0:
                    # then z1 = z2 =: z and z (e_{j-1} + f_{j-1}) = e_j + f_j for all j: strict pair if all e_j = f_j
                    if e[2] != f[2]:
                        continue
                    # e_1 = f_1, e_2 = f_2: either strict to depth m+1 (any z), or find z from the first difference
                    jj = next((x for x in range(3, m + 2) if e[x] != f[x]), None)
                    if jj is None:
                        ok = True
                        strict += 1
                    else:
                        continue  # e_{jj-1} = f_{jj-1} but e_jj != f_jj: no solution
                else:
                    # z1 d1 = num; the remaining equations e_x + z1 e_{x-1} = f_x + (z1 + d1) f_{x-1}, multiplied by d1 (no inversion)
                    num = e[2] ^ f[2] ^ F.mul(f[1], d1)
                    ok = True
                    for x in range(3, m + 2):
                        if F.mul(d1, e[x] ^ f[x] ^ F.mul(d1, f[x - 1])) != F.mul(num, e[x - 1] ^ f[x - 1]):
                            ok = False
                            break
                if not ok:
                    continue
                pairs += 1
                for u, v in zip(nphi[i], nphi[j]):
                    dd = (u - v) % mod
                    dd = min(dd, mod - dd)
                    maxabs = max(maxabs, dd)
                    if dd > r:
                        bad += 1
        print(f"phantom congruence n=16 (T,k)=({T},{k}): {pairs} pairs joined by at most one phantom root each ({strict} strict), "
              f"max |d mod {mod}| = {maxabs}, violations {bad}")
        assert bad == 0


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    for name, fn in (("padding", check_padding), ("padfield", check_padfield), ("pair", check_pair), ("sparse", check_sparse), ("curve", check_curve),
                     ("consts", check_consts), ("phantom", check_phantom)):
        if what in (name, "all"):
            fn()
