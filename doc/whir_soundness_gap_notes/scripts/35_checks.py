#!/usr/bin/env python3
"""Numerical checks for 35-large-characteristic-transfer.md (pure Python, about 15 s in total).

  A  local rank of the first-order hidden-derivative (contact) conditions on the full rectangle,
     over F2, F3 and a large prime, against the closed sum R_loc(m, B) of [DKT26, (24)].
  B  a complete first-order explainer space in characteristic 2: GF(2^8), n = 16, k = 4, A = 8,
     multiplicity 4, Y1-degree <= 2. Checks that every explainer Q vanishes on the jet (P, P') of every
     list member, that Q(X, u + X v, v) = Q0(X^2, u, v) + X Q1(X^2, u, v) with Q0 and Q1 vanishing
     separately on the sections (g, h) of P = g(X^2) + X h(X^2), and that a random polynomial is not killed.
  C  the flat word at rate 1/4, n = 32: the polynomials of the DKT support (m = 4, B = 2, A = 15) that
     vanish on the jets of all 31 flats are exactly the multiples of the flat cubic (dimension 208).
Run: python3 35_checks.py [A] [B] [C]
"""
import sys
import random
from itertools import combinations
from math import comb

M = 8
MOD = 0x11D
ORDER = (1 << M) - 1
EXP = [0] * (2 * ORDER + 2)
LOG = [0] * (1 << M)
_v = 1
for _i in range(ORDER):
    EXP[_i] = _v
    LOG[_v] = _i
    _v <<= 1
    if _v >> M:
        _v ^= MOD
assert _v == 1
for _i in range(ORDER, 2 * ORDER):
    EXP[_i] = EXP[_i - ORDER]


def mul(a, b):
    if a == 0 or b == 0:
        return 0
    return EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[ORDER - LOG[a]]


def fpow(a, e):
    if e == 0:
        return 1
    if a == 0:
        return 0
    return EXP[(LOG[a] * e) % ORDER]


MULT = [[mul(a, b) for b in range(1 << M)] for a in range(1 << M)]
TR = [bytes(MULT[a]) for a in range(1 << M)]


def bxor(a, b):
    return (int.from_bytes(a, "little") ^ int.from_bytes(b, "little")).to_bytes(len(a), "little")


def rref_bytes(rows, ncols):
    rows = list(rows)
    piv = []
    r0 = 0
    nr = len(rows)
    for c in range(ncols):
        p = None
        for i in range(r0, nr):
            if rows[i][c]:
                p = i
                break
        if p is None:
            continue
        rows[r0], rows[p] = rows[p], rows[r0]
        pr = rows[r0].translate(TR[inv(rows[r0][c])])
        rows[r0] = pr
        for i in range(nr):
            if i != r0 and rows[i][c]:
                rows[i] = bxor(rows[i], pr.translate(TR[rows[i][c]]))
        piv.append(c)
        r0 += 1
        if r0 == nr:
            break
    return rows[:r0], piv


def nullspace_bytes(rows, ncols):
    R, piv = rref_bytes(rows, ncols)
    ps = set(piv)
    out = []
    for f in (c for c in range(ncols) if c not in ps):
        v = [0] * ncols
        v[f] = 1
        for r, pc in zip(R, piv):
            v[pc] = r[f]
        out.append(v)
    return out


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            t = MULT[a]
            for j, b in enumerate(q):
                if b:
                    r[i + j] ^= t[b]
    return r


def peval(p, x):
    r = 0
    for a in reversed(p):
        r = mul(r, x) ^ a
    return r


def deriv(P):
    return [P[i] if i % 2 == 1 else 0 for i in range(1, len(P))] + [0]


def subspace_poly(basis):
    L = [0, 1]
    for b in basis:
        lb = peval(L, b)
        sq = [0] * (2 * len(L) - 1)
        for i, a in enumerate(L):
            sq[2 * i] = mul(a, a)
        for i, a in enumerate(L):
            sq[i] ^= mul(a, lb)
        L = sq
    return L


def span(bs):
    S = [0]
    for b in bs:
        S = S + [s ^ b for s in S]
    return S


def binom2(a, b):
    return 1 if 0 <= b <= a and (b & ~a) == 0 else 0


# ---------------------------------------------------------------- A
def rank_mod(vecs, p):
    piv = {}
    rk = 0
    for v in vecs:
        r = {c: x % p for c, x in v.items() if x % p}
        while r:
            c = min(r)
            if c in piv:
                pr = piv[c]
                f = r[c]
                for cc, vv in pr.items():
                    nv = (r.get(cc, 0) - f * vv) % p
                    if nv:
                        r[cc] = nv
                    else:
                        r.pop(cc, None)
            else:
                iv = pow(r[c], p - 2, p)
                piv[c] = {cc: (vv * iv) % p for cc, vv in r.items()}
                rk += 1
                break
    return rk


def local_rank(m, B, p):
    """image of X^x Y0^a Y1^c (x + a < m, c <= B) under X = T, Y0 = T U, U = Y1 + E, mod T^m and,
    at T-degree s, mod E^(m-s): coordinates (s, e, l) for T^s E^e Y1^l."""
    vecs = []
    for a in range(m):
        for c in range(B + 1):
            for x in range(m - a):
                s = x + a
                vecs.append({(s, e, a + c - e): comb(a, e) for e in range(min(a, m - s - 1) + 1)})
    return rank_mod(vecs, p)


def Rloc(m, B):
    return sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))


def check_A():
    ok = True
    for (m, B) in [(2, 1), (3, 1), (4, 2), (5, 2), (6, 3), (8, 3), (8, 4), (10, 4), (12, 5), (12, 6), (16, 6), (16, 8), (16, 12), (24, 10)]:
        r = [local_rank(m, B, p) for p in (2, 3, 2147483647)]
        ok &= r == [Rloc(m, B)] * 3
        print(f"A  m={m:2d} B={B:2d}: R_loc={Rloc(m, B):5d}  rank over F2, F3, F_p = {r}")
    print("A  local rank equals R_loc in every characteristic tested:", ok)


# ---------------------------------------------------------------- B
def check_B():
    random.seed(7)
    N, n, k, A, m, B = 4, 16, 4, 8, 4, 2
    Dg, Z = k - 1, m * A
    Dom = span([fpow(2, i) for i in range(N)])
    P1 = [random.randrange(256) for _ in range(k)]
    P2 = [random.randrange(256) for _ in range(k)]
    perm = Dom[:]
    random.shuffle(perm)
    y = {a: peval(P1, a) for a in perm[:8]}
    y.update({a: peval(P2, a) for a in perm[8:]})
    mons = [(x, a, c) for c in range(B + 1) for a in range(Z // Dg + 2) for x in range(Z) if x + Dg * (a + c) < Z]
    rows = []
    for al in Dom:
        b = y[al]
        rowd = {}
        for col, (x, a, c) in enumerate(mons):
            for i in range(min(x, m - 1) + 1):
                if not binom2(x, i):
                    continue
                for j in range(min(a, m - 1 - i) + 1):
                    if not binom2(a, j):
                        continue
                    s = i + j
                    co = mul(fpow(al, x - i), fpow(b, a - j))
                    if co == 0:
                        continue
                    for e in range(min(j, m - s - 1) + 1):
                        if binom2(j, e):
                            rowd.setdefault((s, e, j - e + c), bytearray(len(mons)))[col] ^= co
        rows += [bytes(r) for r in rowd.values()]
    NS = nullspace_bytes(rows, len(mons))
    print(f"B  n={n} k={k} A={A} m={m} B={B}: {len(mons)} coefficients, explainer space of dimension {len(NS)} "
          f"(count N_coef - n R_loc = {len(mons) - n * Rloc(m, B)})")

    def evalQ(Q, P, x0):
        p, dp = peval(P, x0), peval(deriv(P), x0)
        r = 0
        for co, (x, a, c) in zip(Q, mons):
            if co:
                r ^= mul(co, mul(fpow(x0, x), mul(fpow(p, a), fpow(dp, c))))
        return r

    def interp(pts):
        res = [0] * len(pts)
        for i, (xi, yi) in enumerate(pts):
            num, den = [1], 1
            for j, (xj, _) in enumerate(pts):
                if j != i:
                    num = pmul(num, [xj, 1])
                    den = mul(den, xi ^ xj)
            cc = mul(yi, inv(den))
            for t, e in enumerate(num):
                res[t] ^= mul(cc, e)
        return res

    lst = set()
    for S in combinations(Dom, k):
        P = interp([(a, y[a]) for a in S])
        if sum(1 for a in Dom if peval(P, a) == y[a]) >= A:
            lst.add(tuple(P))
    ok1 = all(evalQ(Q, list(P), x0) == 0 for P in lst for Q in NS for x0 in range(256))
    Pr = [random.randrange(256) for _ in range(k)]
    ok2 = not all(evalQ(Q, Pr, x0) == 0 for Q in NS for x0 in range(256))

    def split(Q):
        Q0, Q1 = {}, {}
        for co, (x, a, c) in zip(Q, mons):
            if co:
                for j in range(a + 1):
                    if binom2(a, j):
                        d = Q0 if (x + j) % 2 == 0 else Q1
                        key = ((x + j) // 2, a - j, j + c)
                        d[key] = d.get(key, 0) ^ co
        return Q0, Q1

    def evalR(R, g, h, t0):
        gv, hv, r = peval(g, t0), peval(h, t0), 0
        for (t, i, j), co in R.items():
            if co:
                r ^= mul(co, mul(fpow(t0, t), mul(fpow(gv, i), fpow(hv, j))))
        return r

    ok3 = True
    for Q in NS[:25]:
        Q0, Q1 = split(Q)
        for P in lst:
            g, h = list(P[0::2]), list(P[1::2])
            ok3 &= all(evalR(Q0, g, h, t0) == 0 and evalR(Q1, g, h, t0) == 0 for t0 in range(256))
    print(f"B  list at agreement >= {A}: {len(lst)} polynomials; every explainer vanishes on every list jet: {ok1}; "
          f"a random polynomial is not killed: {ok2}; Q0 and Q1 vanish separately on the sections: {ok3}")


# ---------------------------------------------------------------- C
def check_C():
    N, m, B = 5, 4, 2
    n = 1 << N
    k = n // 4
    Dg, A = k - 1, n // 2 - 1
    Z = m * A
    basisD = [fpow(2, i) for i in range(N)]
    LD = subspace_poly(basisD)
    e0 = LD[1]
    flats = []
    for f in range(1, 1 << N):
        ker = [x for x in range(1 << N) if bin(x & f).count("1") % 2 == 0]
        bs, sp = [], {0}
        for x in ker:
            if x not in sp:
                bs.append(x)
                sp |= {s ^ x for s in sp}
        fb = []
        for x in bs:
            e = 0
            for i in range(N):
                if x >> i & 1:
                    e ^= basisD[i]
            fb.append(e)
        LV = subspace_poly(fb)
        assert all(c == 0 for c in LV[k + 1:n // 2])
        flats.append(LV[1:k + 1])
    mons = [(x, a, c) for c in range(B + 1) for a in range(Z // Dg + 2) for x in range(Z) if x + Dg * (a + c) < Z]
    idx = {mo: i for i, mo in enumerate(mons)}
    maxa = max(a for _, a, _ in mons)
    rows = []
    for P in flats:
        dP = deriv(P)
        Pp = [[1]]
        for _ in range(maxa):
            Pp.append(pmul(Pp[-1], P))
        dPp = [[1]]
        for _ in range(B):
            dPp.append(pmul(dPp[-1], dP))
        Mx = [bytearray(len(mons)) for _ in range(Z)]
        cache = {}
        for col, (x, a, c) in enumerate(mons):
            if (a, c) not in cache:
                cache[(a, c)] = pmul(Pp[a], dPp[c])
            for i, e in enumerate(cache[(a, c)]):
                if e:
                    Mx[x + i][col] = e
        rows += [bytes(r) for r in Mx]
    NS = nullspace_bytes(rows, len(mons))
    # the flat cubic in jet coordinates:
    # Ghat = Y0^3 + X Y0^2 Y1 + e0 Y1 + (Y0 + X Y1) gam(X^2) + e0 X^(n/2-2),  gam(X^2) = (L_D(X) - X^n - e0 X)/X^2
    Gh = {}

    def addm(key, c):
        if c:
            Gh[key] = Gh.get(key, 0) ^ c
            if Gh[key] == 0:
                del Gh[key]

    addm((0, 3, 0), 1)
    addm((1, 2, 1), 1)
    addm((0, 0, 1), e0)
    for j in range(1, N):
        addm(((1 << j) - 2, 1, 0), LD[1 << j])
        addm(((1 << j) - 1, 0, 1), LD[1 << j])
    addm((n // 2 - 2, 0, 0), e0)
    W = max(x + Dg * (a + c) for (x, a, c) in Gh)
    mult = []
    for c in range(B):
        for a in range(Z // Dg + 2):
            for x in range(Z):
                if x + Dg * (a + c) < Z - W:
                    v = bytearray(len(mons))
                    for (gx, ga, gc), co in Gh.items():
                        v[idx[(x + gx, a + ga, c + gc)]] ^= co
                    mult.append(bytes(v))
    _, piv = rref_bytes(mult, len(mons))
    _, piv2 = rref_bytes(mult + [bytes(v) for v in NS], len(mons))
    print(f"C  n={n} k={k}: weighted degree of the flat cubic = {W} (3k-2 = {3*k-2}); support of dimension {len(mons)}; "
          f"polynomials vanishing on all {len(flats)} flat jets: dimension {len(NS)}; multiples of the cubic in the support: "
          f"{len(piv)}; span of both: {len(piv2)}")
    print("C  the annihilator of the flats in the support is exactly the multiples of the cubic:",
          len(NS) == len(piv) == len(piv2))


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C"]
    for w in which:
        {"A": check_A, "B": check_B, "C": check_C}[w]()
