#!/usr/bin/env python3
"""Independent verification of a first integral dE found by 40_scale (dump file), over GF(2^16).

  1. E has the 7 vanishing Taylor coefficients of contact order 4 at every point of the word.
  2. a = E_Y and c = E_X: a lies in F[X, Y^2], c in F[X^2, Y], a_X = c_Y, and a_X is a square.
  3. Both a and c have multiplicity >= 3 at every received point (Lemma N of note 40, b = 1, o = 4).
  4. Bezout lemma of note 40: the resultant Res_Y(a, c) in F[X] is nonzero, its degree is at most
     W (W - D) / D (and 9 W - 25 D for a quintic), and X = alpha is a root of multiplicity >= 11 for every
     alpha of the domain (>= 29 when the dump was made with contact order 6, J=3 in 40_scale).
Run: python3 40_bezout.py dumpfile
"""
import sys

Q = 1 << 16
EXP = [0] * (2 * Q)
LOG = [0] * Q
v = 1
for i in range(Q - 1):
    EXP[i] = v
    LOG[v] = i
    v <<= 1
    if v & Q:
        v ^= 0x1002D
assert v == 1
for i in range(Q - 1, 2 * Q):
    EXP[i] = EXP[i - (Q - 1)]


def mul(a, b):
    return EXP[LOG[a] + LOG[b]] if a and b else 0


def inv(a):
    return EXP[Q - 1 - LOG[a]]


def fpow(a, e):
    if e == 0:
        return 1
    if a == 0:
        return 0
    return EXP[(LOG[a] * e) % (Q - 1)]


def binom2(a, b):
    return 1 if b <= a and (b & ~a) == 0 else 0


def padd(p, q):
    r = [0] * max(len(p), len(q))
    for i, x in enumerate(p):
        r[i] ^= x
    for i, x in enumerate(q):
        r[i] ^= x
    while r and r[-1] == 0:
        r.pop()
    return r


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        if x:
            lx = LOG[x]
            for j, y in enumerate(q):
                if y:
                    r[i + j] ^= EXP[lx + LOG[y]]
    while r and r[-1] == 0:
        r.pop()
    return r


def peval(p, x):
    r = 0
    for c in reversed(p):
        r = mul(r, x) ^ c
    return r


def det_poly(Mx):
    """determinant of a square matrix of polynomials in X, by cofactor-free fraction-free elimination
    replaced with evaluation and interpolation (the entries are small)."""
    n = len(Mx)
    dmax = sum(max((len(e) - 1 for e in row if e), default=0) for row in Mx)
    xs = list(range(1, dmax + 2))
    vals = []
    for x in xs:
        A = [[peval(e, x) for e in row] for row in Mx]
        d = 1
        for col in range(n):
            p = None
            for r in range(col, n):
                if A[r][col]:
                    p = r
                    break
            if p is None:
                d = 0
                break
            A[col], A[p] = A[p], A[col]
            d = mul(d, A[col][col])
            ic = inv(A[col][col])
            for r in range(col + 1, n):
                if A[r][col]:
                    f = mul(A[r][col], ic)
                    for cc in range(col, n):
                        if A[col][cc]:
                            A[r][cc] ^= mul(f, A[col][cc])
        vals.append(d)
    # Newton interpolation
    coef = list(vals)
    m = len(xs)
    for j in range(1, m):
        for i in range(m - 1, j - 1, -1):
            coef[i] = mul(coef[i] ^ coef[i - 1], inv(xs[i] ^ xs[i - j]))
    poly = []
    for i in range(m - 1, -1, -1):
        poly = padd(pmul(poly, [xs[i], 1]), [coef[i]])
    return poly


def main():
    pts, monos = [], {}
    for line in open(sys.argv[1]):
        t = line.split()
        if t[0] == "n":
            n, Dc, W = int(t[1]), int(t[3]), int(t[5])
        elif t[0] == "pt":
            pts.append((int(t[1]), int(t[2])))
        elif t[0] == "mono":
            monos[(int(t[1]), int(t[2]))] = int(t[3])
    print(f"n = {n}, D = {Dc}, W = {W}, {len(monos)} monomials, deg_Y E = {max(k for (_, k) in monos)}")
    # 1. Taylor conditions
    conds = [(1, 0), (0, 1), (1, 1), (3, 0), (2, 1), (1, 2), (0, 3)]
    bad = 0
    for (al, be) in pts:
        for (r, q) in conds:
            s = 0
            for (i, k), e in monos.items():
                if binom2(i, r) and binom2(k, q):
                    s ^= mul(e, mul(fpow(al, i - r), fpow(be, k - q)))
            bad += s != 0
    print(f"1. contact order 4: {bad} violated conditions out of {7 * len(pts)}")
    # 2. a and c as polynomials in Y with coefficients in F[X]
    ky = max(k for (_, k) in monos)
    a = [[] for _ in range(ky + 1)]
    c = [[] for _ in range(ky + 1)]
    wmax = 0
    for (i, k), e in monos.items():
        if k & 1:
            a[k - 1] = padd(a[k - 1], [0] * i + [e])
            wmax = max(wmax, i + Dc * k)
        if i & 1:
            c[k] = padd(c[k], [0] * (i - 1) + [e])
            wmax = max(wmax, i - 1 + Dc * k)
    print(f"2. weighted degree of dE recomputed: {wmax}; a has Y-degree {max(j for j in range(ky + 1) if a[j])}, "
          f"c has Y-degree {max(j for j in range(ky + 1) if c[j])}; odd Y-coefficients of a: "
          f"{sum(1 for j in range(1, ky + 1, 2) if a[j])}")
    # 3. multiplicity >= 3 of a and c at the received points
    bad = 0
    for (al, be) in pts:
        for poly in (a, c):
            for r in range(3):
                for q in range(3 - r):
                    s = 0
                    for k in range(ky + 1):
                        if binom2(k, q):
                            for i, e in enumerate(poly[k]):
                                if e and binom2(i, r):
                                    s ^= mul(e, mul(fpow(al, i - r), fpow(be, k - q)))
                    bad += s != 0
    print(f"3. multiplicity >= 3 of E_Y and E_X at the received points: {bad} violations")
    # 4. resultant
    da = max(j for j in range(ky + 1) if a[j])
    dc = max(j for j in range(ky + 1) if c[j])
    size = da + dc
    Mx = [[[] for _ in range(size)] for _ in range(size)]
    for r in range(dc):
        for j in range(da + 1):
            Mx[r][r + j] = a[da - j]
    for r in range(da):
        for j in range(dc + 1):
            Mx[dc + r][r + j] = c[dc - j]
    res = det_poly(Mx)
    if not res:
        print("4. resultant is zero: E_Y and E_X have a common factor")
        return
    deg = len(res) - 1
    mults = []
    for (al, _) in pts:
        p = list(res)
        m = 0
        while p and peval(p, al) == 0:
            # divide by (X - al)
            q = [0] * (len(p) - 1)
            carry = 0
            for i in range(len(p) - 1, 0, -1):
                carry = p[i] ^ mul(carry, al)
                q[i - 1] = carry
            p = q
            m += 1
        mults.append(m)
    b1 = W * (W - Dc) // Dc
    b2 = f", 9W - 25D = {9 * W - 25 * Dc}" if ky <= 5 else ""
    print(f"4. Res_Y(E_Y, E_X): degree {deg} (bounds: W(W - D)/D = {b1}{b2}); multiplicity at the domain "
          f"points: min {min(mults)}, max {max(mults)}, sum {sum(mults)} (11 n = {11 * n}, 29 n = {29 * n}); "
          f"other roots: degree {deg - sum(mults)}"
          + ("" if max(mults) == min(mults) else f"; the largest is at alpha = {pts[mults.index(max(mults))][0]}"))


if __name__ == "__main__":
    main()
