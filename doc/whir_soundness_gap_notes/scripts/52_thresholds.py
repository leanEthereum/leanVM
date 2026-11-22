#!/usr/bin/env python3
# Referee 52. Exact integer recomputation of the counts of notes 48 and 50. No code of 41/48/50 is imported.
#
#   N0(Z)      = #{(x, a) >= 0 : x + Delta*a < Z}
#   even certificate (q, k=1; m) at A:   N0(mA) + N0(mA - q*Delta) > n * rho1(q, m),   m >= 2q - 1
#   even certificate (q, k=2; m) at A:   sum_{i<=2} N0(mA - i*q*Delta) > n * rho2(q, m), m >= 4q - 1
#   full certificate (m, B) at A:        N(B, mA) > n * R(m, B)
#   d = floor((mA - 1)/Delta)
# Parts: A thresholds of Theorem 1.3 (four sizes, four rates); B certificates at the agreements quoted in note 50
#        and Corollary 1.4; C note 48 (closed forms, B = 1, thresholds, explicit certificates); D the constants of
#        Theorem 8'' (Lemma C through the convexity argument, written independently); E the obstruction table.
import sys
from math import isqrt, log2, ceil, sqrt
from fractions import Fraction as Fr


def N0(Z, Delta):
    if Z <= 0:
        return 0
    t = (Z - 1) // Delta
    return (t + 1) * Z - Delta * t * (t + 1) // 2


def N0_direct(Z, Delta):
    s = 0
    a = 0
    while Z - Delta * a > 0:
        s += Z - Delta * a
        a += 1
    return s


def NB(B, Z, Delta):
    # sum_t (min(t, B) + 1) (Z - Delta t)_+
    if Z <= 0 or B < 0:
        return 0
    s = 0
    for t in range(0, B):
        v = Z - Delta * t
        if v <= 0:
            return s
        s += (t + 1) * v
    # t >= B : (B+1) * sum_{t>=B} (Z - Delta t)_+ = (B+1) * N0(Z - Delta*B)
    return s + (B + 1) * N0(Z - Delta * B, Delta)


def rho1(q, m):
    return m * m - (q - 1) * m + q * (3 * q - 1) // 2


def rho2(q, m):
    return (3 * m * m - (6 * q - 3) * m + 13 * q * q - 3 * q) // 2


def Rloc(m, B):
    if m <= 0:
        return 0
    return sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))


def even_margin(n, Delta, A, q, m, k=1):
    lhs = sum(N0(m * A - i * q * Delta, Delta) for i in range(k + 1))
    return lhs - n * (rho1(q, m) if k == 1 else rho2(q, m))


def smallest_A(n, pred):
    lo, hi = 0, n
    if not pred(hi):
        return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if pred(mid):
            hi = mid
        else:
            lo = mid
    return hi


def even_threshold(n, Delta, q, k=1, mmax=4000):
    # smallest A with an even certificate, over m in [2kq - 1, mmax]; the margin is nondecreasing in A.
    best = None
    m0 = 2 * k * q - 1
    # coarse-to-fine: the minimising m is found by scanning all m, with a binary search in A for each
    for m in range(m0, mmax + 1):
        if best is not None and even_margin(n, Delta, best[0] - 1, q, m, k) <= 0:
            continue
        A = smallest_A(n, lambda A: even_margin(n, Delta, A, q, m, k) > 0)
        if A is not None and (best is None or A < best[0]):
            best = (A, m)
    return best


def queries(a):
    return ceil(108 / log2(1 / a))


def lead_even(rho, q):
    # leading order: eps = 1 - a^2/rho < (q-1)^2 (1-a)^2 / (2q((3-rho)q - (1-rho)))  (q = inf: (1-a)^2/(2(3-rho)))
    lo, hi = 0.0, sqrt(rho)
    for _ in range(80):
        a = (lo + hi) / 2
        c = (1 - a) ** 2 / (2 * (3 - rho)) if q is None else (q - 1) ** 2 * (1 - a) ** 2 / (2 * q * ((3 - rho) * q - (1 - rho)))
        if 1 - a * a / rho < c:
            hi = a
        else:
            lo = a
    return hi


A1 = {2: 0.689898, 4: 0.468792, 8: 0.319059, 16: 0.218108}  # a_1(rho), values of note 41 Section 6 (refereed there)


def a1(rho):
    return A1[round(1 / rho)]


RATES = ((2, "1/2"), (4, "1/4"), (8, "1/8"), (16, "1/16"))


def partA(sizes=(25, 26, 27, 28)):
    print("== A. Smallest A/n with an even certificate (q, k; m), m <= 4000, Delta = rho*n + 5; entries: A/n (m, d)")
    # self-test of N0
    for Z, D in ((1, 7), (7, 7), (8, 7), (100, 7), (12345, 100), (5, 9)):
        assert N0(Z, D) == N0_direct(Z, D)
    for den, name in RATES:
        print("  rate %s: Johnson sqrt(Delta/n) = %.6f at n=2^25, a_1 = %.6f, leading-order even thresholds q=2: %.6f, q=inf: %.6f" % (
            name, sqrt((2 ** 25 // den + 5) / 2 ** 25), a1(1 / den), lead_even(1 / den, 2), lead_even(1 / den, None)))
        for k in (1, 2):
            qs = (2, 4, 8, 16, 32, 64, 128) if k == 1 else (2, 4, 8, 16, 32, 64)
            for q in qs:
                cells = []
                for lg in sizes:
                    n = 1 << lg
                    Delta = n // den + 5
                    mmax = 4000 if lg == sizes[0] else None
                    if lg == sizes[0]:
                        A, m = even_threshold(n, Delta, q, k)
                        mref = m
                    else:
                        # the minimising m is stable across sizes: scan a window around it
                        best = None
                        for mm in range(max(2 * k * q - 1, mref - 40), mref + 41):
                            Ac = smallest_A(n, lambda A: even_margin(n, Delta, A, q, mm, k) > 0)
                            if Ac is not None and (best is None or Ac < best[0]):
                                best = (Ac, mm)
                        A, m = best
                    d = (m * A - 1) // Delta
                    cells.append("%.6f (m=%d, d=%d)" % (A / n, m, d))
                a = float(cells[0].split()[0])
                print("    k=%d q=%3d: " % (k, q) + " | ".join(cells) + " | queries just above: %d" % queries(a + 1e-6))


def best_d(n, Delta, A, k=1, qmax=512, mmax=4000):
    # over all q = 2..qmax: smallest m with a certificate; returns list of (q, m, d)
    out = []
    q = 2
    while q <= qmax:
        for m in range(2 * k * q - 1, mmax + 1):
            if even_margin(n, Delta, A, q, m, k) > 0:
                out.append((q, m, (m * A - 1) // Delta))
                break
        q *= 2
    return out


def partB():
    print("== B. Even certificates at the agreements quoted in note 50, rate 1/2, Delta = n/2 + 5, A = ceil(a n)")
    quoted = ((0.7065, 2, 17, 24), (0.7055, 2, 24, 33), (0.705, 4, 26, 36), (0.7045, 4, 28, 39), (0.703, 8, 54, 75), (0.7009, 128, 983, 1377))
    for a, q, m, dq in quoted:
        res = []
        for lg in (25, 26, 27, 28):
            n = 1 << lg
            Delta = n // 2 + 5
            A = -((-int(a * 10000) * n) // 10000)
            mg = even_margin(n, Delta, A, q, m)
            d = (m * A - 1) // Delta
            res.append((mg > 0, d, "%.4f" % (mg / n)))
        print("  a=%.4f (q, m) = (%d, %d): certificate at the four sizes: %s, d = %s (note: %d), margin/n = %s" % (
            a, q, m, [r[0] for r in res], sorted(set(r[1] for r in res)), dq, [r[2] for r in res]))
    print("  the certificate of smallest d at each agreement (n = 2^25; all q <= 512, smallest m per q), and Corollary 1.4:")
    n = 1 << 25
    Delta = n // 2 + 5
    for a in (0.7065, 0.706, 0.7055, 0.705, 0.7045, 0.704, 0.703, 0.702, 0.701, 0.7009):
        A = -((-int(round(a * 10000)) * n) // 10000)
        lst = best_d(n, Delta, A)
        if not lst:
            print("   a=%.4f: none" % a)
            continue
        qd = min(lst, key=lambda t: t[2])
        Wb = min(Fr(m * A - 1, q) for q, m, d in lst)
        db = min(d // q for q, m, d in lst)
        dmax = max(d for q, m, d in lst)
        print("   a=%.4f: smallest d = %d at (q, m) = (%d, %d), d^2 = %d; survivor: W <= %.4f n, delta <= %d, d_max = %d; [q: m, d] = %s" % (
            a, qd[2], qd[0], qd[1], qd[2] ** 2, float(Wb) / n, db, dmax, ["%d: %d, %d" % t for t in lst]))
    print("  k = 2 at a = 0.70: range of m with a certificate for q = 4, and Corollary 1.4 for a b = 2 survivor")
    A = -((-7000 * n) // 10000)
    ms = [m for m in range(15, 200) if even_margin(n, Delta, A, 4, m, 2) > 0]
    print("   q=4: m in [%d, %d], d at m=%d: %d" % (ms[0], ms[-1], ms[0], (ms[0] * A - 1) // Delta))
    lst = best_d(n, Delta, A, k=2, mmax=6000)
    print("   survivor b=2: W <= %.4f n, delta <= %d, d_max = %d" % (float(min(Fr(m * A - 1, q) for q, m, d in lst)) / n, min(d // q for q, m, d in lst), max(d for q, m, d in lst)))


def partC():
    print("== C. Note 48: closed forms, B = 1, thresholds, explicit certificates")
    # closed forms
    bad = 0
    for Delta in (7, 16, 1 << 10 | 5):
        for B in range(0, 8):
            for Z in range((B - 1) * Delta if B > 0 else 0, 40 * Delta, max(1, Delta // 3)):
                if Z < 0:
                    continue
                qq, r = divmod(Z, Delta)
                S = (qq + 1) * (qq * Delta + 2 * r)  # 2*S(Z)
                closed6 = 3 * (B + 1) * S - 3 * Z * B * (B + 1) + Delta * (B - 1) * B * (B + 1)
                direct = sum((min(t, B) + 1) * max(Z - Delta * t, 0) for t in range(0, Z // Delta + 2))
                assert direct == NB(B, Z, Delta)
                if closed6 != 6 * direct:
                    bad += 1
    print("  N(B, Z) closed form of note 48 (Z >= (B-1)Delta): mismatches %d" % bad)
    bad = 0
    for B in range(1, 8):
        for m in range(2 * B - 1, 60):
            v = (B + 1) * (3 * m * (m + 1) - 3 * m * B + B * (2 * B + 1))
            if v != 6 * Rloc(m, B):
                bad += 1
    print("  R(m, B) closed form for m >= 2B - 1, B <= 7, m < 60: mismatches %d" % bad)
    # B = 1: no certificate with A^2 <= n Delta, brute force at small sizes and exact at real sizes
    viol = 0
    for n in (16, 32, 64, 128):
        for Delta in range(1, n):
            for A in range(1, n + 1):
                if A * A <= n * Delta:
                    for m in range(1, 80):
                        if NB(1, m * A, Delta) > n * Rloc(m, 1):
                            viol += 1
    print("  B = 1: certificates (m, 1), m < 80, with A^2 <= n*Delta, n in {16, 32, 64, 128}, every Delta < n: %d" % viol)
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        Delta = n // 2 + 5
        J = isqrt(n * Delta)
        best = None
        for m in range(1, 3001):
            A = smallest_A(n, lambda A: NB(1, m * A, Delta) > n * Rloc(m, 1))
            if A is not None and (best is None or A < best[0]):
                best = (A, m)
        print("   n=2^%d: floor(sqrt(n Delta)) = %d; smallest A with a certificate (m, 1), m <= 3000: sqrt + %d (m = %d)" % (lg, J, best[0] - J, best[1]))
    print("  thresholds a^(B): smallest A/n with a certificate (m, B), m <= 400")
    for B in range(2, 7):
        cells = []
        for lg in (25, 26, 27, 28):
            n = 1 << lg
            Delta = n // 2 + 5
            best = None
            for m in range(1, 401):
                if best is not None and NB(B, m * (best[0] - 1), Delta) <= n * Rloc(m, B):
                    continue
                A = smallest_A(n, lambda A: NB(B, m * A, Delta) > n * Rloc(m, B))
                if A is not None and (best is None or A < best[0]):
                    best = (A, m)
            cells.append("%.6f (m=%d)" % (best[0] / n, best[1]))
        print("   B=%d: %s; queries just above: %d" % (B, " | ".join(cells), queries(float(cells[0].split()[0]) + 1e-6)))
    print("  explicit certificates of note 48 (n = 2^25): a, A, (m, B), N, nR, B_jet, range of m")
    n = 1 << 25
    Delta = n // 2 + 5
    for a10k, m, B in ((7050, 14, 2), (7055, 13, 2), (7060, 12, 2), (7065, 11, 2), (7020, 17, 3), (7030, 14, 3)):
        A = -((-a10k * n) // 10000)
        Nn = NB(B, m * A, Delta)
        nR = n * Rloc(m, B)
        rng = [mm for mm in range(1, 400) if NB(B, mm * A, Delta) > n * Rloc(mm, B)]
        print("   a=%.4f A=%d (%d, %d): N=%d nR=%d ok=%s B_jet=%d, m in [%d, %d] (contiguous: %s)" % (
            a10k / 10000, A, m, B, Nn, nR, Nn > nR, (m * A - 1) // Delta, rng[0], rng[-1], rng == list(range(rng[0], rng[-1] + 1))))
    for lg in (26, 27, 28):
        n = 1 << lg
        Delta = n // 2 + 5
        print("   n=2^%d: (14,2) at 0.705: %s; (11,2) at 0.7065: %s; B=2 at 0.704: %s; B=2 at 0.7045: m in %s" % (
            lg,
            NB(2, 14 * -((-7050 * n) // 10000), Delta) > n * Rloc(14, 2),
            NB(2, 11 * -((-7065 * n) // 10000), Delta) > n * Rloc(11, 2),
            any(NB(2, mm * -((-7040 * n) // 10000), Delta) > n * Rloc(mm, 2) for mm in range(1, 400)),
            (lambda r: (r[0], r[-1]))([mm for mm in range(1, 400) if NB(2, mm * -((-7045 * n) // 10000), Delta) > n * Rloc(mm, 2)])))


def partD():
    # Theorem 8'' of note 48: the two uniform applications of Lemma C, re-derived.
    # A factor with Y1-degree b, weighted degree W, contact 2 j_alpha is cut by (m, B) if
    #   Delta (m + B) <= mA - W   and   N(B, mA) - N(B - b, mA - W) > sum_alpha [R(m, B) - R(m - 2 j_alpha, B - b)].
    # Case I (leading coefficient in F[X]): W >= b Delta + sum max(j, 2j - b) (Lemma L). The left side is
    # nondecreasing in W, so it is enough to take W equal to this lower bound. With s_j = #{alpha : j_alpha = j},
    # F(s) = sum_j s_j psi(j) + Ntilde(mA - b Delta - sum_j s_j phi(j)) is convex (Ntilde: the piecewise linear
    # interpolation of the convex integer function N(B - b, .)), so its maximum over the polytope
    # {s >= 0, sum s_j <= n, sum s_j phi(j) <= Wmax - b Delta} is at a vertex: at most two nonzero s_j.
    # psi is constant for 2j >= m, phi increasing: only j <= ceil(m/2) matter.
    print("== D. Theorem 8'' of note 48: the constants, with an independent implementation of the uniform Lemma C checks")

    def Ntil(Bp, Z, Delta):
        # piecewise linear interpolation at a rational Z
        f = Z.numerator // Z.denominator
        lo = NB(Bp, f, Delta)
        if Z == f:
            return Fr(lo)
        hi = NB(Bp, f + 1, Delta)
        return lo + (Z - f) * (hi - lo)

    for a10k, m0, pairs, mcap in ((7065, 11, {1: (41, 1), 2: (43, 2)}, 960), (7050, 14, {1: (51, 1), 2: (54, 2)}, 960)):
        for lg in (25, 26, 27, 28):
            n = 1 << lg
            Delta = n // 2 + 5
            A = -((-a10k * n) // 10000)
            Wmax = m0 * A - 1
            Bjet = Wmax // Delta
            percut = (mcap * A - 1) // Delta
            line = "  a=%.4f n=2^%d: B_jet=%d, floor((960A-1)/Delta)=%d, C=%d;" % (a10k / 10000, lg, Bjet, percut, percut * Bjet)
            for b, (m, B) in pairs.items():
                side = Delta * (m + B) <= m * A - Wmax
                # convexity of j -> R(m - 2j, B - b) (here B - b = 0)
                conv = all(Rloc(m - 2 * (j + 1), B - b) - 2 * Rloc(m - 2 * j, B - b) + Rloc(m - 2 * (j - 1), B - b) >= 0 for j in range(1, m))
                psi = lambda j: Rloc(m, B) - Rloc(m - 2 * j, B - b)
                phi = lambda j: max(j, 2 * j - b)
                lhs0 = NB(B, m * A, Delta)
                cap = Wmax - b * Delta
                jmax = (m + 1) // 2 + 1
                worst = None

                def Fval(svec):
                    tot = sum(s * psi(j) for j, s in svec)
                    Z = Fr(m * A - b * Delta) - sum(s * phi(j) for j, s in svec)
                    return tot + Ntil(B - b, Z, Delta)
                verts = [[]]
                for j in range(1, jmax + 1):
                    # single j: s_j = n, or s_j phi(j) = cap
                    if n * phi(j) <= cap:
                        verts.append([(j, Fr(n))])
                    else:
                        verts.append([(j, Fr(cap, phi(j)))])
                    for j2 in range(0, j):
                        # s_j + s_j2 = n and s_j phi(j) + s_j2 phi(j2) = cap
                        den = phi(j) - phi(j2)
                        if den == 0:
                            continue
                        sj = Fr(cap - n * phi(j2), den)
                        sj2 = n - sj
                        if sj >= 0 and sj2 >= 0:
                            verts.append([(j, sj), (j2, sj2)])
                ok = True
                for v in verts:
                    if not (lhs0 > Fval(v)):
                        ok = False
                        worst = v
                # Case II with total contact <= 2n: W >= (b + 2) Delta, sum psi(j_alpha) <= n psi(1) (psi concave, nondecreasing)
                conc = all(psi(j + 1) - psi(j) <= psi(j) - psi(j - 1) for j in range(1, m)) and all(psi(j + 1) >= psi(j) for j in range(0, m))
                ok2 = lhs0 - NB(B - b, m * A - (b + 2) * Delta, Delta) > n * psi(1)
                line += " b=%d (m,B)=(%d,%d): side %s, convex %s, case I all profiles %s, case II total contact<=2n %s (concave %s);" % (b, m, B, side, conv, ok, ok2, conc)
            print(line)


def partE():
    print("== E. Thresholds of Theorem 1.3 against the known large lists (n = 2^28 unless said)")
    n = 1 << 28
    for den, name in RATES:
        Delta = n // den + 5
        row = []
        for q in (2, 8, 128):
            A, m = even_threshold(n, Delta, q, 1) if q < 128 else even_threshold(n, Delta, q, 1, mmax=3000)
            row.append("q=%d: %.6f" % (q, A / n))
        print("  rate %s: thresholds %s; a_1 = %.6f; Johnson %.6f" % (name, ", ".join(row), a1(1 / den), sqrt(Delta / n)))
    print("  rate 1/2: known families at 0.6250 (5n/8), 0.5625 (9n/16), padding below 0.6875: all below 0.7008")
    print("  rate 1/4: flats at 1/2 - 1/n (n - 1 members), slack-1 flats at 1/2 (2(n-1)), Gold level t at 1/2 - 2^-(t+1) - 1/n:",
          ["t=%d: %.6f" % (t, 0.5 - 2.0 ** -(t + 1)) for t in (4, 5, 6, 7, 8, 9)])
    print("  rate 1/16: F_4-hyperplanes at 1/4 - 1/n ((n-1)/3 members); Proposition 6.4 of note 43 at 1/4 - 3/(4 sqrt n): n=2^12: %.6f, n=2^16: %.6f, n=2^20: %.6f, n=2^28: %.6f" % (
        0.25 - 0.75 / 2 ** 6, 0.25 - 0.75 / 2 ** 8, 0.25 - 0.75 / 2 ** 10, 0.25 - 0.75 / 2 ** 14))
    # the Gold lists of the flat word on F_(2^N) (rate 1/4, Delta = n/4 - 1): level t has agreement n/2 - n/2^(t+1) - 1
    def gbin4(a, b):
        num = den = 1
        for i in range(b):
            num *= 4 ** (a - i) - 1
            den *= 4 ** (i + 1) - 1
        return num // den
    for lg in (14, 20, 28):
        nn = 1 << lg
        Delta = nn // 4 - 1
        for tl in (5, 6, 7, 8):
            T = nn // 2 - nn // 2 ** (tl + 1)
            A = T - 1
            found = None
            q = 2
            while q <= 256 and found is None:
                for m in range(2 * q - 1, 3000):
                    if even_margin(nn, Delta, A, q, m) > 0:
                        found = (q, m, (m * A - 1) // Delta)
                        break
                q *= 2
            cnt = 4 ** tl * (nn - 1) * gbin4(lg // 2, tl) * T // nn
            print("   rate 1/4, D = F_(2^%d), Gold level t=%d, A/n = %.6f: first even certificate (q, m, d) = %s; Gold count (formula quoted in note 43): %s; d^2 = %s" % (
                lg, tl, A / nn, found, ("about 2^%d" % (cnt.bit_length() - 1)) if cnt else "none (t > N/2)", found[2] ** 2 if found else None))
    # the same thresholds at the sizes where the rate 1/16 family lives (degree bound n/16 - 1, no slack, as in note 43)
    for lg in (12, 16, 20, 24, 28):
        nn = 1 << lg
        Delta = nn // 16 - 1
        A = nn // 4 - 3 * (1 << (lg // 2)) // 4
        found = None
        q = 2
        while q <= 256 and found is None:
            for m in range(2 * q - 1, 3000):
                if even_margin(nn, Delta, A, q, m) > 0:
                    found = (q, m, (m * A - 1) // Delta)
                    break
            q *= 2
        members = ((1 << (lg // 2)) - 1) * nn // 3
        print("   n=2^%d, Delta=n/16-1, A=n/4-3sqrt(n)/4=%d: first even certificate (q, m, d) = %s; family size %d, d^2 = %s" % (
            lg, A, found, members, found[2] ** 2 if found else None))


if __name__ == "__main__":
    parts = sys.argv[1:] or ["A", "B", "C", "D", "E"]
    for pname, fn in (("A", partA), ("B", partB), ("C", partC), ("D", partD), ("E", partE)):
        if pname in parts:
            fn()
