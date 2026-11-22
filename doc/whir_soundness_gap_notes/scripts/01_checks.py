#!/usr/bin/env python3
"""Numerical checks for 01-literature-attacks.md, on a small analogue of the leanVM domain.

Field GF(2^16) = F2[x]/(x^16+x^12+x^3+x+1), domain D_d = F2-span of 1, x, ..., x^(d-1)
(the integers 0 .. 2^d - 1 in the polynomial basis). No proper subfield contains D_d for d >= 2,
as for the leanVM domain in GF(2^64).

Run: python3 01_checks.py [A] [B] [C] [D] [E]   (no argument runs all)
"""
import sys
import random
from itertools import combinations

M = 16
MOD = 0x1100B
ORDER = (1 << M) - 1
EXP = [0] * (2 * ORDER)
LOG = [0] * (1 << M)
_v = 1
for _i in range(ORDER):
    EXP[_i] = _v
    LOG[_v] = _i
    _v <<= 1
    if _v >> M:
        _v ^= MOD
assert _v == 1 and len(set(EXP[:ORDER])) == ORDER, "x is not primitive"
for _i in range(ORDER, 2 * ORDER):
    EXP[_i] = EXP[_i - ORDER]


def mul(a, b):
    if a == 0 or b == 0:
        return 0
    return EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[ORDER - LOG[a]]


def sqrt(a):
    # Frobenius inverse: a^(2^(M-1))
    if a == 0:
        return 0
    return EXP[(LOG[a] * (1 << (M - 1))) % ORDER]


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            la = LOG[a]
            for j, b in enumerate(q):
                if b:
                    r[i + j] ^= EXP[la + LOG[b]]
    return r


def padd(p, q):
    if len(p) < len(q):
        p, q = q, p
    r = list(p)
    for i, b in enumerate(q):
        r[i] ^= b
    return r


def deg(p):
    for i in range(len(p) - 1, -1, -1):
        if p[i]:
            return i
    return -1


def peval(p, x):
    acc = 0
    for c in reversed(p):
        acc = mul(acc, x) ^ c
    return acc


def locator(points):
    """prod (X - s), coefficients low to high, by a product tree."""
    polys = [[s, 1] for s in points]
    if not polys:
        return [1]
    while len(polys) > 1:
        nxt = []
        for i in range(0, len(polys) - 1, 2):
            nxt.append(pmul(polys[i], polys[i + 1]))
        if len(polys) % 2:
            nxt.append(polys[-1])
        polys = nxt
    return polys[0]


def pdivlin(p, b):
    """(p(X) - p(b)) / (X - b), synthetic division."""
    out = [0] * (len(p) - 1)
    acc = 0
    for i in range(len(p) - 1, 0, -1):
        acc = mul(acc, b) ^ p[i]
        out[i - 1] = acc
    return out


def par(v):
    return bin(v).count("1") & 1


# ---------------------------------------------------------------------------------------------
# A. Height-two decision trees at rate 1/2 (DKTZ26, Lemma 6.9 and Theorem 6.10 at h = 2):
#    count and the locator identity L_W L_A = X^(N/2) L_W + C_A, deg C_A <= N/2.
# ---------------------------------------------------------------------------------------------
def check_A(d=7, samples=40):
    N = 1 << d
    # functionals on D_d = F2^d are bit masks; value par(mask & x)
    W = list(range(1 << (d - 3)))  # span of 1..x^(d-4): codimension 3, size N/8
    Wperp = [m for m in range(1, 1 << d) if all(par(m & w) == 0 for w in W)]
    assert len(Wperp) == 7
    # planes E = <a, b> of functionals, one basis each
    seen_planes = set()
    supports = set()
    total_fn = 0
    for a in range(1, 1 << d):
        for b in range(a + 1, 1 << d):
            key = frozenset((a, b, a ^ b))
            if key in seen_planes:
                continue
            seen_planes.add(key)
            # a b restricted to W must be affine and the function must vanish on W:
            # quick filter on W
            abW = [par(a & w) & par(b & w) for w in W]
            for e in range(1, 1 << d):
                if e in key:
                    continue
                for c in (0, 1):
                    total_fn += 1
                    if any(abW[i] ^ par(e & w) ^ c for i, w in enumerate(W)):
                        continue
                    supp = frozenset(x for x in range(N) if (par(a & x) & par(b & x)) ^ par(e & x) ^ c)
                    supports.add(supp)
    planes = (N - 1) * (N - 2) // 6
    assert len(seen_planes) == planes
    # every function is counted twice per plane basis orbit? e and e^a etc. give different functions,
    # but ab + e + c with e ranging over all of U* \ E counts each function exactly once per plane.
    expected = 28 * (6 * (1 << (d - 3)) - 5)
    print(f"[A] d={d} N={N}: W-avoiding height-2 tree supports found {len(supports)}, DKTZ26 M_2(d) = {expected}")
    assert len(supports) == expected
    assert all(len(s) == N // 2 for s in supports)
    LW = locator(W)
    LWs = locator(W[1:])  # W without 0
    rng = random.Random(1)
    sample = rng.sample(sorted(supports, key=sorted), samples)
    beta0 = EXP[12345]
    assert beta0 >= N
    tops = set()
    for A in sample:
        LA = locator(sorted(A))
        assert deg(LA) == N // 2
        GA = LA[: N // 2]  # L_A - X^(N/2)
        assert deg(GA) <= 3 * N // 8, deg(GA)
        CA = pmul(LW, GA)
        assert deg(CA) == N // 2  # degree exactly K: not a genuine codeword
        CAg = pmul(LWs, GA)
        assert deg(CAg) == N // 2 - 1  # with W \ {0}: genuine, one agreement fewer
        # one word R = X^(N/2) L_W agrees with C_A exactly on W u A
        R = [0] * (N // 2) + LW
        agree = sum(1 for x in range(N) if peval(R, x) == peval(CA, x))
        assert agree == 5 * N // 8, agree
        Rg = [0] * (N // 2) + LWs
        agree_g = sum(1 for x in range(N) if peval(Rg, x) == peval(CAg, x))
        assert agree_g == 5 * N // 8 - 1
        tops.add(tuple(CA))
        # pole pair and the affine combiner: for every beta, alpha = C_A(beta0) + beta*beta0
        gam = peval(CA, beta0)
        H = pdivlin(CA, beta0)  # (C_A - C_A(beta0)) / (X - beta0), degree < N/2
        assert deg(H) <= N // 2 - 1
        for _ in range(2):
            bet = rng.randrange(1 << M)
            alp = gam ^ mul(bet, beta0)
            P = list(H)
            P[0] ^= bet  # witness P = beta + H
            cnt = 0
            for x in range(N):
                i0 = inv(x ^ beta0)
                f0 = i0
                f1 = mul(peval(R, x), i0)
                if f1 ^ mul(alp ^ mul(bet, x), f0) == peval(P, x):
                    cnt += 1
            assert cnt == 5 * N // 8, cnt
    assert len(tops) == len(sample)
    print(f"[A] {samples} sampled members: deg(L_W L_A - X^(N/2) L_W) = N/2, agreement 5N/8 = {5*N//8} with one word;")
    print("    genuine variant (W without 0): degree N/2 - 1, agreement 5N/8 - 1; pole pair: every (alpha, beta) on the")
    print("    line alpha + beta*beta0 = C_A(beta0) folds to agreement 5N/8 with a polynomial of degree < N/2.")


# ---------------------------------------------------------------------------------------------
# B. Flats (lead notes) and the BKR pigeonhole statistic on a sparse domain.
# ---------------------------------------------------------------------------------------------
def subspace_poly(basis):
    L = [0, 1]
    for v in basis:
        Lv = peval(L, v)
        assert Lv != 0
        L2 = [0] * (2 * len(L) - 1)
        for i, c in enumerate(L):
            L2[2 * i] = mul(c, c)
        L = padd(L2, [mul(Lv, c) for c in L])
    return L


def check_B(d=10):
    N = 1 << d
    # hyperplanes ker(mask): coefficient a_H of X^(N/4) in L_H; distinct for distinct H (rate 1/4, T = N/2)
    def kernel_basis(masks):
        # basis of the common kernel of the functionals in masks, by brute force over a spanning sweep
        vecs = []
        span = {0}
        for x in range(1, N):
            if x in span:
                continue
            if all(par(m & x) == 0 for m in masks):
                vecs.append(x)
                span |= {s ^ x for s in span}
        return vecs

    coeffs = {}
    for m in range(1, N):
        L = subspace_poly(kernel_basis([m]))
        assert deg(L) == N // 2 and all(L[i] == 0 for i in range(len(L)) if i & (i - 1))
        coeffs[m] = L[N // 4]
    print(f"[B] d={d}: {N-1} hyperplanes, {len(set(coeffs.values()))} distinct coefficients a_H of X^(N/4)")
    # codimension-2 subspaces: statistic of the coefficient a_W of X^(N/8) (the BKR pigeonhole key)
    from collections import Counter

    cnt = Counter()
    seen = set()
    rng = random.Random(7)
    target = 6000
    while len(seen) < target:
        a = rng.randrange(1, N)
        b = rng.randrange(1, N)
        if a == b:
            continue
        key = frozenset((a, b, a ^ b))
        if key in seen:
            continue
        seen.add(key)
        L = subspace_poly(kernel_basis([a, b]))
        cnt[L[N // 8]] += 1
    mult = Counter(cnt.values())
    pairs = sum(v * (v - 1) // 2 for v in cnt.values())
    print(f"[B] {target} random codim-2 subspaces: multiplicity histogram of a_W {dict(sorted(mult.items()))},")
    print(f"    colliding pairs {pairs}, expected for uniform values in GF(2^16): {target*(target-1)/2/65536:.1f}")


# ---------------------------------------------------------------------------------------------
# C. Hyperplanes with a biased padding set at rate 1/2: T = N/2 + |B \ H|.
# ---------------------------------------------------------------------------------------------
def walsh(f):
    f = list(f)
    n = len(f)
    h = 1
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                u, v = f[j], f[j + h]
                f[j], f[j + h] = u + v, u - v
        h *= 2
    return f


def check_C():
    # identity check at d = 8 with an arbitrary B of size N/4
    d = 8
    N = 1 << d
    rng = random.Random(3)
    B = rng.sample(range(N), N // 4)
    LB = locator(B)
    R = [0] * (N // 2) + LB
    for m in rng.sample(range(1, N), 5):
        for c in (0, 1):
            H = [x for x in range(N) if par(m & x) == c]
            LH = locator(H)
            C = pmul(LB, LH[: N // 2])
            assert deg(C) <= N // 2
            agree = sum(1 for x in range(N) if peval(R, x) == peval(C, x))
            assert agree == len(set(H) | set(B))
    print("[C] d=8: word X^(N/2) L_B agrees with L_B (L_H - X^(N/2)), of degree <= N/2, exactly on H u B (10 cases)")
    # bias statistics on the quotient F2^m: B = union of cosets of a codimension-m subspace
    for m in (10, 12, 14, 16):
        n = 1 << m
        best = None
        for seed in range(3):
            rng = random.Random(100 + seed)
            f = [0] * n
            for i in rng.sample(range(n), n // 4):
                f[i] = 1
            spec = walsh(f)
            mags = sorted((abs(v) for v in spec[1:]), reverse=True)
            if best is None or mags[len(mags) // 4] > best[len(best) // 4]:
                best = mags
        out = []
        for logL in (10, 12, 14):
            if (1 << logL) <= len(best):
                eps = best[(1 << logL) - 1] / (2 * n)
                out.append(f"L>=2^{logL}: T/N >= 5/8 + {eps:.5f} = {0.625+eps:.5f}")
        print(f"[C] quotient dim m={m}, random B of density 1/4: " + "; ".join(out))
    # Maiorana-McFarland style B on F2^12: bits 0,1 of the GF(2^6) product equal to (1,1)
    def gf64mul(a, b):
        r = 0
        for i in range(6):
            if (b >> i) & 1:
                r ^= a << i
        for i in range(10, 5, -1):
            if (r >> i) & 1:
                r ^= 0b1000011 << (i - 6)
        return r

    n = 1 << 12
    f = [1 if (gf64mul(i >> 6, i & 63) & 3) == 3 else 0 for i in range(n)]
    spec = walsh(f)
    from collections import Counter

    hist = Counter(abs(v) for v in spec[1:])
    print(f"[C] m=12 Maiorana-McFarland B: |B|/n = {sum(f)}/{n}, |Walsh| histogram {dict(sorted(hist.items()))}")
    big = sum(c for v, c in hist.items() if v >= 48)
    print(f"    {big} hyperplane directions with |B^(a)| >= 48: T/N >= 1/2 + |B|/N/2 + 48/(2*4096) = {0.5 + sum(f)/n/2 + 48/8192:.5f}")


# ---------------------------------------------------------------------------------------------
# D. Gold sets on a sparse domain (DKTZ26, Section 5.3, t = 2): rank-4 quadratic functions with M_1(A) = 0.
# ---------------------------------------------------------------------------------------------
def solve(Mx, rhs):
    n = len(Mx)
    A = [row[:] + [rhs[i]] for i, row in enumerate(Mx)]
    for col in range(n):
        piv = next(r for r in range(col, n) if A[r][col])
        A[col], A[piv] = A[piv], A[col]
        iv = inv(A[col][col])
        A[col] = [mul(iv, v) for v in A[col]]
        for r in range(n):
            if r != col and A[r][col]:
                fct = A[r][col]
                A[r] = [v ^ mul(fct, w) for v, w in zip(A[r], A[col])]
    return [A[i][n] for i in range(n)]


def check_D(d=8):
    N = 1 << d
    basis = [1 << j for j in range(d)]
    moore = []
    for bj in basis:
        row = []
        v = bj
        for i in range(d):
            row.append(v)
            v = mul(v, v)
        moore.append(row)
    # label of the k-th coordinate functional: sqrt of the X-coefficient of its linearized polynomial
    omega = []
    for k in range(d):
        c = solve(moore, [1 if j == k else 0 for j in range(d)])
        # sanity: the polynomial sum c_i X^(2^i) is the k-th coordinate on D
        for x in (3, 77 % N, N - 1):
            v, acc = x, 0
            for i in range(d):
                acc ^= mul(c[i], v)
                v = mul(v, v)
            assert acc == (x >> k) & 1
        omega.append(sqrt(c[0]))

    def label(a):
        r = 0
        for k in range(d):
            if (a >> k) & 1:
                r ^= omega[k]
        return r

    lab = [label(a) for a in range(N)]
    planes = {}
    for a in range(1, N):
        for b in range(a + 1, N):
            key = (a, b, a ^ b)
            if a ^ b < b:
                continue
            pi = mul(mul(lab[a], lab[b]), lab[a] ^ lab[b])
            planes.setdefault(pi, []).append((a, b))
    nplanes = sum(len(v) for v in planes.values())
    assert nplanes == (N - 1) * (N - 2) // 6
    sols = set()
    example = None
    for pi, lst in planes.items():
        if len(lst) < 2:
            continue
        for (a, b), (a2, b2) in combinations(lst, 2):
            # rank 4 iff a, b, a2, b2 independent
            span = {0, a, b, a ^ b}
            if a2 in span or b2 in span or (a2 ^ b2) in span:
                continue
            span2 = span | {s ^ a2 for s in span}
            if b2 in span2:
                continue
            # alternating matrix as the set of unordered index pairs
            mat = 0
            for (u, v) in ((a, b), (a2, b2)):
                for i in range(d):
                    for j in range(i + 1, d):
                        if (((u >> i) & (v >> j)) ^ ((u >> j) & (v >> i))) & 1:
                            mat ^= 1 << (i * d + j)
            sols.add(mat)
            if example is None:
                example = (a, b, a2, b2)
    npairs = nplanes * (nplanes - 1) // 2
    # number of rank-4 alternating d x d matrices over F2
    rank4 = 1
    for i in range(4):
        rank4 *= (1 << (d - i)) - 1
    rank4 = rank4 * 4 // 45
    print(f"[D] d={d}: {nplanes} planes of labels, {len(sols)} rank-4 alternating matrices with M_1(A) = 0;")
    print(f"    heuristic (rank-4 count)/|field| = {rank4}/65536 = {rank4/65536:.1f}")
    if example is None:
        print("[D] no solution found")
        return
    a, b, a2, b2 = example
    E = [x for x in range(N) if (par(a & x) & par(b & x)) ^ (par(a2 & x) & par(b2 & x))]
    T = len(E)
    assert T == 3 * N // 8, T
    LE = locator(E)
    odd = [i for i in range(len(LE)) if i % 2 == 1 and LE[i]]
    assert odd == [1], odd  # L_E = U^2 + c X
    c = LE[1]
    LD = subspace_poly(basis)
    lam = LD[1]
    # codeword C_E = sqrt(lam / c) * U, U = sqrt(L_E - c X) coefficientwise
    s = sqrt(mul(lam, inv(c)))
    C = [mul(s, sqrt(LE[2 * i])) for i in range(T // 2 + 1)]
    assert deg(C) == T // 2 and T // 2 < N // 4
    agree = sum(1 for x in range(N) if peval(C, x) == sqrt(mul(lam, x)))
    assert agree == T, agree
    print(f"[D] example {example}: level set of size 3N/8 = {T}, L_E = U^2 + cX; the codeword of degree {T//2} < N/4")
    print(f"    agrees with the word sqrt(lambda x) on exactly {agree} points (rate 1/4).")


# ---------------------------------------------------------------------------------------------
# E. Family sizes used in the table (log2), for N = log2 n.
# ---------------------------------------------------------------------------------------------
def gauss_binom(a, b):
    if b < 0 or b > a:
        return 0
    num = den = 1
    for i in range(b):
        num *= (1 << (a - i)) - 1
        den *= (1 << (b - i)) - 1
    return num // den


def C_h(h):
    if h == 2:
        return 56
    t, tp = (1 << h) - 1, (1 << (h - 1)) - 1
    return ((1 << t) - 1) * gauss_binom(2 * tp, tp) * (1 << (tp * tp)) * C_h(h - 1) ** 2


def M_h(h, d):
    if h == 2:
        return 28 * (6 * (1 << (d - 3)) - 5)
    tp = (1 << (h - 1)) - 1
    return ((1 << (h + 1)) - 1) * M_h(h - 1, d - 1) * (1 << (tp * tp)) * gauss_binom(d - 1 - tp, tp) * C_h(h - 1)


def check_E():
    from math import log2, comb, lgamma, log

    assert M_h(3, 22) == 71680 * (6 * 2**18 - 5) * (2**18 - 1) * (2**18 - 2) * (2**18 - 4)
    print("[E] DKTZ26 tree counts M_h(d) (rate 1/2, agreement 1/2 + 2^-(h+1)), log2:")
    for d in (22, 25, 26):
        print(f"    d={d}: " + ", ".join(f"h={h}: {log2(M_h(h, d)):.1f}" for h in (2, 3, 4)))
    print("[E] flats at rate 2^-R (agreement 2 rho n, affine count 2^(R-1) [N; R-1]_2) and BKR pigeonhole")
    print("    (agreement 2^(u+1) rho n, count >= 2^(R-u-1) [N; R-u-1]_2 / 2^(64u)), log2:")
    for N in (25, 26, 27, 28):
        row = []
        for R in (2, 3, 4, 5, 6, 7):
            ent = []
            for u in (0, 1, 2):
                c = R - u - 1
                if c < 1:
                    continue
                val = (1 << c) * gauss_binom(N, c)
                ent.append(f"u={u}:{log2(val) - 64*u:.1f}")
            row.append(f"R={R} [" + " ".join(ent) + "]")
        print(f"    N={N}: " + "  ".join(row))
    print("[E] flat-in-coset family (agreement rho n (1 + 2^-j), affine flats of size 2^(1-j) rho n in one coset")
    print("    of a hyperplane), log2 count:")
    for N in (25,):
        for R in (1, 2, 3, 4, 5, 7):
            ent = []
            for j in (1, 2, 3, 4):
                k = N - R + 1 - j  # dimension of the flats
                val = (1 << (N - 1 - k)) * gauss_binom(N - 1, k)
                ent.append(f"j={j}:{log2(val):.1f}")
            print(f"    N={N} R={R}: " + " ".join(ent))
    print("[E] generic counting bound over K = GF(2^64): largest r with log2 C(n, rho n + r) >= 64 r + b")

    def lg2comb(n, k):
        return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / log(2)

    N = 25
    n = 1 << N
    for R in (1, 2, 3, 4, 5, 7):
        k = n >> R
        res = []
        for b in (10, 26, 40):
            lo, hi = 0, n - k
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if lg2comb(n, k + mid) >= 64 * mid + b:
                    lo = mid
                else:
                    hi = mid - 1
            res.append(f"b={b}: r/n={lo/n:.5f} (T/n={(k+lo)/n:.5f})")
        print(f"    N={N} rho=2^-{R}: " + "; ".join(res))
    print("[E] heuristic Gold counts on the sparse domain (rank-2t alternating matrices / 2^(64 (t-1))), log2:")

    def rank_count(d, t):
        v = 1
        for i in range(2 * t):
            v *= (1 << (d - i)) - 1
        num = den = 1
        for i in range(1, t + 1):
            num *= 1 << (2 * i - 2)
            den *= (1 << (2 * i)) - 1
        return v * num // den

    for d in (25, 26, 27, 28):
        print(f"    d={d}: " + ", ".join(f"t={t}: {log2(rank_count(d, t)) - 64*(t-1) + 2*t:.1f}" for t in (2, 3, 4)))


if __name__ == "__main__":
    which = [a.upper() for a in sys.argv[1:]] or ["A", "B", "C", "D", "E"]
    if "A" in which:
        check_A()
    if "B" in which:
        check_B()
    if "C" in which:
        check_C()
    if "D" in which:
        check_D()
    if "E" in which:
        check_E()
