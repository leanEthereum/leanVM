#!/usr/bin/env python3
"""Check of Proposition 5 of 35-large-characteristic-transfer.md (the flat cubic).

Field GF(2^16) = F2[x]/(x^16+x^12+x^3+x+1), domain D = F2-span of 1, x, ..., x^(N-1), n = 2^N,
rate 1/4 (k = n/4), word y(a) = a^(n/2-1). For every hyperplane V of D the script checks
  (a) L_V = X^(n/2) + X*P_V with deg P_V < n/4, and P_V = y exactly on V \\ {0};
  (b) L_D = L_V^2 + theta*L_V and the even part of P_V is the constant c0 = e0/theta;
  (c) the section (u, v) = (g_V, h_V) of P_V = g_V(X^2) + X*h_V(X^2) lies on the cubic
      G(t,u,v) = u(u^2 + t v^2) + e0 v + u*gamma_D(t) + e0 t^(n/4-1), where
      gamma_D(t) = t^(n/2-1) + Lam(t)/t (the two top terms cancel) and Lam(X^2) = L_D(X) - e0 X;
  (d) G(a^2, y(a) + a v, v) = 0 identically in v for every a in D \\ {0} (the line of a lies on the cubic);
      for a = 0, G(0, 0, v) = e0 v is not zero;
  (e) for t0 outside D^2 the fibre cubic is irreducible (Artin-Schreier criterion L_D(sqrt t0) != 0).
Run: python3 35_flat_cubic.py [Nmax]   (default 8; about 20 s)
"""
import sys

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


def padd(p, q):
    if len(p) < len(q):
        p, q = q, p
    r = list(p)
    for i, b in enumerate(q):
        r[i] ^= b
    return r


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            la = LOG[a]
            for j, b in enumerate(q):
                if b:
                    r[i + j] ^= EXP[la + LOG[b]]
    return r


def pscale(p, c):
    return [mul(a, c) for a in p]


def peval(p, x):
    r = 0
    for a in reversed(p):
        r = mul(r, x) ^ a
    return r


def trim(p):
    while p and p[-1] == 0:
        p = p[:-1]
    return p


def subspace_poly(basis):
    """L_V for V = span(basis): iterate L <- L^2 + L(b) L."""
    L = [0, 1]
    for b in basis:
        lb = peval(L, b)
        if lb == 0:
            raise ValueError("dependent basis")
        sq = [0] * (2 * len(L) - 1)
        for i, a in enumerate(L):
            sq[2 * i] = mul(a, a)
        L = padd(sq, pscale(L, lb))
    return L


def span(basis):
    S = [0]
    for b in basis:
        S = S + [s ^ b for s in S]
    return S


def hyperplanes(N):
    """All hyperplanes of F2^N as kernels of nonzero functionals; returns bases as field elements."""
    out = []
    for f in range(1, 1 << N):
        # kernel of x -> parity(x & f) inside D = integers < 2^N
        ker = [x for x in range(1 << N) if bin(x & f).count("1") % 2 == 0]
        basis = []
        sp = {0}
        for x in ker:
            if x not in sp:
                basis.append(x)
                sp |= {s ^ x for s in sp}
        out.append((basis, set(ker)))
    return out


def check(N):
    n = 1 << N
    k = n // 4
    D = list(range(n))
    LD = subspace_poly([1 << i for i in range(N)])
    assert len(LD) == n + 1 and all(peval(LD, a) == 0 for a in D)
    e0 = LD[1]
    assert e0 != 0
    # Lam(t) with Lam(X^2) = L_D(X) - e0 X ; Lam/t
    Lam = [0] * (n // 2 + 1)
    for j in range(1, N + 1):
        Lam[1 << (j - 1)] = LD[1 << j]
    Lam_over_t = Lam[1:]
    y = [0] + [fpow(a, n // 2 - 1) for a in D[1:]]
    tpow = lambda e: [0] * e + [1]
    coefU = padd(tpow(n // 2 - 1), Lam_over_t)  # t^(n/2-1) + Lam/t
    const = pscale(tpow(n // 4 - 1), e0)

    def G(u, v):
        """G(t, u(t), v(t)) as a polynomial in t."""
        uu = pmul(u, u)
        vv = pmul(v, v)
        r = pmul(u, padd(uu, [0] + vv))
        r = padd(r, pscale(v, e0))
        r = padd(r, pmul(u, coefU))
        r = padd(r, const)
        return trim(r)

    nh = 0
    for basis, ker in hyperplanes(N):
        LV = subspace_poly(basis)
        assert len(LV) == n // 2 + 1 and LV[0] == 0
        P = trim(LV[1:n // 2])  # (L_V - X^(n/2))/X
        assert all(c == 0 for c in LV[k + 1:n // 2]) and len(P) <= k
        agree = [a for a in D if peval(P, a) == y[a]]
        assert set(agree) == ker - {0}, (N, basis)
        lam = next(a for a in D if a not in ker)
        theta = peval(LV, lam)
        sq = [0] * (n + 1)
        for i, a in enumerate(LV):
            sq[2 * i] = mul(a, a)
        assert trim(padd(sq, pscale(LV, theta))) == trim(LD)
        g = P[0::2]
        h = P[1::2]
        assert trim(g) == [mul(e0, inv(theta))], "even part is not the constant e0/theta"
        assert G(g, h) == [], "flat section not on the cubic"
        nh += 1
    # lines
    for a in D[1:]:
        t0 = mul(a, a)
        # u = y(a) + a v : G(t0, y + a v, v) as polynomial in v
        u = [y[a], a]
        v = [0, 1]
        cu = peval(coefU, t0)
        c0 = peval(const, t0)
        uu = pmul(u, u)
        r = pmul(u, padd(uu, pscale(pmul(v, v), t0)))
        r = padd(r, pscale(v, e0))
        r = padd(r, pscale(u, cu))
        r = padd(r, [c0])
        assert trim(r) == [], ("line not on cubic", a)
    # irreducibility of the generic fibre: reducible iff L_D(sqrt t0) = 0
    red = sum(1 for t0 in range(1, 1 << M) if peval(LD, fpow(t0, 1 << (M - 1))) == 0)
    assert red == n - 1
    print(f"N={N} n={n} k={k}: {nh} hyperplane flats on the cubic, agreement {n//2-1} each; "
          f"{n-1} of the {n} lines lie on it; fibre reducible only over D^2")


if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 8
    for N in range(4, nmax + 1):
        check(N)
