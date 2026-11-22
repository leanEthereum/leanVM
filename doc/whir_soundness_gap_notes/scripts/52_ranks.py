#!/usr/bin/env python3
# Referee 52. Exact local ranks of the contact conditions, from the definition of the contact ideal.
#
# c_m is spanned by T^i w^l Y1^e with i + 2l >= m, w = S - T*Y1. It is homogeneous for the (T, S)-degree.
# A form Phi of (T, S)-degree N is rewritten in the basis T^i' w^l Y1^e (substitute S = w + T*Y1):
#   T^i S^j Y1^c = sum_p C(j, p) T^(i+p) w^(j-p) Y1^(c+p),
# and Phi lies in c_m iff every coefficient with i' + 2l < m vanishes (i' + l = N, so: l < m - N).
# So the image of a graded space V in F[T,S,Y1]/c_m has dimension sum_{N<m} rank(M_N), M_N the matrix
# (monomials of V_N) x (pairs (l, e) with l < m - N). The entries are binomial coefficients, so the rank is
# the rank over the prime field. No formula of notes 35, 48, 50 is used to build the matrices.
#
# Parts: A  Lemma 1.2 of note 50 (supports {1, Y1^q}, {1, Y1^q, Y1^2q}), p = 2, and p = 3, 5 for comparison
#        B  R(m, B) of notes 35/48 (support Y1-degree <= B), p = 2, 3, 5, against the sum and the closed form
#        C  Lemma F of note 48 and Lemma 2.1 of note 50: supports of the Y1-coefficients, p = 2, 3, 5
#        D  Lemma 1.1 of note 50 on random examples over GF(2)
import sys, random
from math import comb


def row_entries(N, i, c, m, p):
    # row of T^i S^(N-i) Y1^c : dict {(l, e): binom mod p}, l < m - N
    j = N - i
    out = {}
    for pp in range(0, j + 1):
        l = j - pp
        if l < m - N:
            v = comb(j, pp) % p
            if v:
                out[(l, c + pp)] = v
    return out


def rank_mod_p(rows, p):
    # rows: list of dicts col -> value. Gaussian elimination mod p.
    cols = {}
    for r in rows:
        for k in r:
            if k not in cols:
                cols[k] = len(cols)
    if p == 2:
        vecs = []
        for r in rows:
            v = 0
            for k in r:
                v |= 1 << cols[k]
            vecs.append(v)
        piv = {}
        rk = 0
        for v in vecs:
            while v:
                h = v.bit_length() - 1
                if h in piv:
                    v ^= piv[h]
                else:
                    piv[h] = v
                    rk += 1
                    break
        return rk
    nc = len(cols)
    mat = []
    for r in rows:
        v = [0] * nc
        for k, x in r.items():
            v[cols[k]] = x
        mat.append(v)
    rk = 0
    col = 0
    nr = len(mat)
    while rk < nr and col < nc:
        piv = None
        for i in range(rk, nr):
            if mat[i][col]:
                piv = i
                break
        if piv is None:
            col += 1
            continue
        mat[rk], mat[piv] = mat[piv], mat[rk]
        inv = pow(mat[rk][col], p - 2, p)
        mat[rk] = [(x * inv) % p for x in mat[rk]]
        for i in range(nr):
            if i != rk and mat[i][col]:
                f = mat[i][col]
                mat[i] = [(a - f * b) % p for a, b in zip(mat[i], mat[rk])]
        rk += 1
        col += 1
    return rk


def local_rank(m, cset, p):
    tot = 0
    for N in range(m):
        rows = [row_entries(N, i, c, m, p) for c in cset for i in range(N + 1)]
        tot += rank_mod_p(rows, p)
    return tot


def rho1(q, m):
    return m * m - (q - 1) * m + q * (3 * q - 1) // 2


def rho2(q, m):
    return (3 * m * m - (6 * q - 3) * m + 13 * q * q - 3 * q) // 2


def R_sum(m, B):
    return sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))


def R_closed(m, B):
    # (B+1)[m(m+1)/2 - mB/2 + B(2B+1)/6], times 6 to stay in integers
    v = (B + 1) * (3 * m * (m + 1) - 3 * m * B + B * (2 * B + 1))
    assert v % 6 == 0
    return v // 6


def partA():
    print("== A. Lemma 1.2 of note 50: local rank on {1, Y1^q} (k = 1) and {1, Y1^q, Y1^2q} (k = 2), GF(2)")
    for q, mmax in ((2, 64), (4, 64), (8, 64), (16, 64), (32, 72)):
        bad = []
        first_ok = None
        for m in range(1, mmax + 1):
            r = local_rank(m, (0, q), 2)
            ok = (r == rho1(q, m))
            if ok and first_ok is None:
                first_ok = m
            if not ok and first_ok is not None:
                bad.append(m)
            if not ok and m >= 2 * q - 1:
                bad.append(m)
        print("  k=1 q=%2d: rank == m^2-(q-1)m+q(3q-1)/2 for all m in [%d, %d]: %s (first m where it holds: %d; mismatches %s)" % (
            q, 2 * q - 1, mmax, not bad, first_ok, sorted(set(bad))))
        # values below the range
        low = [(m, local_rank(m, (0, q), 2), rho1(q, m), m * (m + 1)) for m in range(1, 2 * q - 1)]
        print("     below the range (m, rank, formula, 2*binom(m+1,2)):", low[:6])
    for q, mmax in ((2, 30), (4, 30), (8, 40)):
        bad = [m for m in range(4 * q - 1, mmax + 1) if local_rank(m, (0, q, 2 * q), 2) != rho2(q, m)]
        lowbad = [m for m in range(1, 4 * q - 1) if local_rank(m, (0, q, 2 * q), 2) != rho2(q, m)]
        print("  k=2 q=%2d: rank == rho_2 for all m in [%d, %d]: %s; mismatching m below: %s" % (q, 4 * q - 1, mmax, not bad, lowbad))
    print("  other characteristics, support {1, Y1^2}: rank - m^2 for m = 4..14")
    for p in (3, 5):
        print("    p=%d:" % p, [local_rank(m, (0, 2), p) - m * m for m in range(4, 15)])
    print("  p=3, support {1, Y1^3}: rank - (m^2 - 2m) for m = 6..14 (the analogue of the saving, w^3 = S^3 - T^3 Y1^3):",
          [local_rank(m, (0, 3), 3) - (m * m - 2 * m) for m in range(6, 15)])
    print("  p=2, support {1, Y1^3} (not a power of 2): rank - m^2 for m = 6..14:",
          [local_rank(m, (0, 3), 2) - m * m for m in range(6, 15)])
    print("  p=2, full support Y1-degree <= 2 against {1, Y1^2}: (m, R(m,2), rho_1(2,m)):",
          [(m, local_rank(m, (0, 1, 2), 2), local_rank(m, (0, 2), 2)) for m in (4, 8, 12)])


def partB():
    print("== B. R(m, B): exact local rank (support Y1-degree <= B) against the sum of note 35 and the closed form of note 48")
    for p in (2, 3, 5):
        mism_sum = []
        mism_closed = []
        mmax = 30 if p == 2 else 20
        for B in range(1, 6):
            for m in range(1, mmax + 1):
                r = local_rank(m, tuple(range(B + 1)), p)
                if r != R_sum(m, B):
                    mism_sum.append((m, B, r, R_sum(m, B)))
                if m >= 2 * B - 1 and r != R_closed(m, B):
                    mism_closed.append((m, B, r, R_closed(m, B)))
        print("  p=%d, B=1..5, m=1..%d: mismatches with the sum: %s; with the closed form (m >= 2B-1): %s" % (p, mmax, mism_sum, mism_closed))
    print("  closed form outside m >= 2B-1 (expected to fail):", [(m, B, R_sum(m, B), R_closed(m, B)) for B in (3, 4, 5) for m in range(1, 2 * B - 1) if R_sum(m, B) != R_closed(m, B)][:6])
    print("  R(18,5) =", R_sum(18, 5), " R(11,2) =", R_sum(11, 2), " R(14,2) =", R_sum(14, 2), " R(m,1)-m^2 for m<=10:", [R_sum(m, 1) - m * m for m in range(1, 11)])


def left_kernel_mod_p(rows, p):
    # rows: list of dicts; returns basis of {x : sum x_i rows_i = 0} as lists over F_p
    cols = {}
    for r in rows:
        for k in r:
            if k not in cols:
                cols[k] = len(cols)
    nc = len(cols)
    nr = len(rows)
    mat = []
    for i, r in enumerate(rows):
        v = [0] * (nc + nr)
        for k, x in r.items():
            v[cols[k]] = x
        v[nc + i] = 1
        mat.append(v)
    rk = 0
    for col in range(nc):
        piv = None
        for i in range(rk, nr):
            if mat[i][col]:
                piv = i
                break
        if piv is None:
            continue
        mat[rk], mat[piv] = mat[piv], mat[rk]
        inv = pow(mat[rk][col], p - 2, p)
        mat[rk] = [(x * inv) % p for x in mat[rk]]
        for i in range(nr):
            if i != rk and mat[i][col]:
                f = mat[i][col]
                mat[i] = [(a - f * b) % p for a, b in zip(mat[i], mat[rk])]
        rk += 1
    return [v[nc:] for v in mat[rk:]]


def partC():
    print("== C. Supports of the Y1-coefficients of Q in c_m with Y1-degree <= b (Lemma F of note 48, Lemma 2.1 of note 50)")
    for p in (2, 3, 5):
        viol = 0
        spaces = 0
        attained_all = True
        not_attained = []
        mmax = 12 if p == 2 else 10
        for m in range(1, mmax + 1):
            for b in range(0, 6):
                occ = {}  # (c, r, q) occurring for N < m
                for N in range(m):
                    idx = [(c, i) for c in range(b + 1) for i in range(N + 1)]
                    rows = [row_entries(N, i, c, m, p) for (c, i) in idx]
                    ker = left_kernel_mod_p(rows, p)
                    spaces += 1
                    for v in ker:
                        for t, x in enumerate(v):
                            if x:
                                c, r = idx[t]
                                occ[(c, r, N - r)] = 1
                for (c, r, qq) in occ:
                    e = b - c
                    if not (2 * r + qq >= m - e and r + qq >= m - b and r + 2 * qq >= m - c):
                        viol += 1
                # sharpness for the leading coefficient: every T^r S^q with r+q < m, r+q >= m-b, 2r+q >= m occurs
                for N in range(max(0, m - b), m):
                    for r in range(N + 1):
                        qq = N - r
                        if 2 * r + qq >= m and (b, r, qq) not in occ:
                            attained_all = False
                            not_attained.append((m, b, r, qq))
        print("  p=%d, m<=%d, b<=5: %d graded pieces; violations of (i) r+q>=m-b, (ii) 2r+q>=m-(b-c), (iii) r+2q>=m-c: %d; support of Q_b attained everywhere: %s %s" % (
            p, mmax, spaces, viol, attained_all, not_attained[:5]))


def partD():
    # Lemma 1.1 of note 50, test over GF(2) in two variables (Y0, Y1) (X specialised away is not allowed for an
    # irreducibility statement, so this is a test of the divisibility mechanism only): for a random G with
    # dG/dY1 != 0 and squarefree-coprime to its derivative, the R' with G*R' in F[Y0][Y1^q] are exactly the
    # multiples of G^(q-1) by elements of F[Y0][Y1^q].
    print("== D. Lemma 1.1 of note 50: random tests over GF(2)[Y0, Y1]")
    rng = random.Random(52)

    def pmul(a, b):
        out = {}
        for (i, j), x in a.items():
            for (k, l), y in b.items():
                key = (i + k, j + l)
                out[key] = out.get(key, 0) ^ (x & y)
        return {k: 1 for k, v in out.items() if v}

    def pgcd_nontrivial_y1(G):
        # crude irreducibility filter is not needed: we only use G with gcd(G, dG/dY1) = 1 tested by resultant-free
        # linear algebra below (the linear system decides the statement directly).
        return False

    tested = 0
    fails = 0
    for trial in range(60):
        q = rng.choice((2, 4))
        bdeg = rng.choice((1, 2, 3))
        ddeg = rng.choice((1, 2, 3))
        G = {}
        for i in range(ddeg + 1):
            for j in range(bdeg + 1):
                if rng.random() < 0.6:
                    G[(i, j)] = 1
        if not any(j % 2 == 1 for (_, j) in G) or not any(j == bdeg for (_, j) in G):
            continue
        # skip G with a repeated factor or a factor in F[Y0][Y1^2]: test irreducibility by brute force over GF(2)
        def irreducible(G):
            dy0 = max(i for i, _ in G)
            dy1 = max(j for _, j in G)
            for a0 in range(dy0 + 1):
                for a1 in range(dy1 + 1):
                    if (a0, a1) == (0, 0) or (a0, a1) == (dy0, dy1):
                        continue
                    if 2 * (a0 * (dy1 + 1) + a1) > dy0 * (dy1 + 1) + dy1 + (dy1 + 1) * dy0:
                        pass
                    mons = [(i, j) for i in range(a0 + 1) for j in range(a1 + 1)]
                    for mask in range(1, 1 << len(mons)):
                        Hh = {mons[t]: 1 for t in range(len(mons)) if mask >> t & 1}
                        if max(i for i, _ in Hh) != a0 or max(j for _, j in Hh) != a1:
                            continue
                        # trial division G / Hh by solving G = Hh * C with C of complementary degrees
                        b0, b1 = dy0 - a0, dy1 - a1
                        cm = [(i, j) for i in range(b0 + 1) for j in range(b1 + 1)]
                        # brute force only when small
                        if len(cm) > 12:
                            return None
                        for cmask in range(1, 1 << len(cm)):
                            Cc = {cm[t]: 1 for t in range(len(cm)) if cmask >> t & 1}
                            if pmul(Hh, Cc) == G:
                                return False
            return True
        irr = irreducible(G)
        if irr is not True:
            continue
        # unknown R' with deg_Y0 <= e0, deg_Y1 <= e1 ; constraint: coefficients of Y1^c, q not dividing c, of G*R' vanish
        e0, e1 = ddeg * (q - 1) + 2, bdeg * (q - 1) + q
        mons = [(i, j) for i in range(e0 + 1) for j in range(e1 + 1)]
        rows = []
        for (i, j) in mons:
            prod = pmul(G, {(i, j): 1})
            rows.append({k: 1 for k in prod if k[1] % q != 0})
        ker = left_kernel_mod_p(rows, 2)
        # the multiples of G^(q-1) by F[Y0][Y1^q] inside the box
        Gp = {(0, 0): 1}
        for _ in range(q - 1):
            Gp = pmul(Gp, G)
        g0 = max(i for i, _ in Gp)
        g1 = max(j for _, j in Gp)
        expect = sum(1 for i in range(e0 - g0 + 1) for j in range(0, e1 - g1 + 1, q))
        tested += 1
        if len(ker) != expect:
            fails += 1
            print("   MISMATCH q=%d G=%s kernel %d expected %d" % (q, sorted(G), len(ker), expect))
    print("  %d irreducible G (Y1-degree 1..3, with an odd power of Y1), q in {2, 4}: the R' with G*R' in F[Y0][Y1^q] are exactly G^(q-1)*F[Y0][Y1^q] in the box: failures %d" % (tested, fails))


if __name__ == "__main__":
    parts = sys.argv[1:] or ["A", "B", "C", "D"]
    if "A" in parts:
        partA()
    if "B" in parts:
        partB()
    if "C" in parts:
        partC()
    if "D" in parts:
        partD()
