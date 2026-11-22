#!/usr/bin/env python3
"""53_lib.py: helpers for 53-goppa-structure-degenerate.md, on top of 43_gf.py (GF(2^m), m <= 16).

Polynomials are coefficient lists, low degree first. A subset of the domain D (a list of field elements) is a
Python int, bit i = D[i]. Everything is exact.
"""
import importlib
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
gfm = importlib.import_module("43_gf")
GF = gfm.GF


def odd_part(F, f):
    """monic squarefree polynomial whose roots (in the algebraic closure) are the roots of f of odd multiplicity.
    f = g h^2 with g squarefree gives f' = g' h^2 and gcd(f, f') = h^2 (F perfect)."""
    f = F.trim(f)
    assert f
    d = F.pderiv(f)
    if not d:
        return [1]
    q, r = F.pdivmod(f, F.pgcd(f, d))
    assert not r
    return F.pscale(q, F.inv(q[-1]))


def is_square(F, f):
    """f in F[X^2] (= squares of F[X], F perfect)."""
    return F.is_even(F.trim(f))


def locator(F, pts):
    L = [1]
    for a in pts:
        L = F.pmul(L, [a, 1])
    return L


def mult_at(F, f, beta):
    """multiplicity of beta as a root of the nonzero polynomial f."""
    f = F.trim(f)
    assert f
    k = 0
    while True:
        q, r = F.pdivmod(f, [beta, 1])
        if r:
            return k
        f = q
        k += 1


def val_rat(F, num, den, beta):
    """valuation at beta of num/den."""
    return mult_at(F, num, beta) - mult_at(F, den, beta)


def deg(F, p):
    return F.deg(F.trim(p)) if F.trim(p) else -1


def subset_mask(D, pts):
    idx = {a: i for i, a in enumerate(D)}
    m = 0
    for a in pts:
        m |= 1 << idx[a]
    return m


def mask_pts(D, mask):
    return [D[i] for i in range(len(D)) if mask >> i & 1]


# ---------------- F_2-linear algebra on rows given as Python ints ----------------

def f2_kernel(rows):
    """rows[i] = int (the column of the parity check at domain point i). Returns a basis of
    {T : xor of rows[i], i in T, = 0} as ints (bit i = point i)."""
    piv = {}
    ker = []
    for i, v in enumerate(rows):
        comb = 1 << i
        while v:
            h = v.bit_length() - 1
            if h in piv:
                pv, pc = piv[h]
                v ^= pv
                comb ^= pc
            else:
                piv[h] = (v, comb)
                break
        if v == 0:
            ker.append(comb)
    return ker


def syndrome(rows, mask):
    s = 0
    i = 0
    while mask:
        if mask & 1:
            s ^= rows[i]
        mask >>= 1
        i += 1
    return s


def rows_inf(F, D, g, parity=True):
    """parity check of Gamma_inf(g) = {T subset D : p_k(T) = 0 for 0 <= k <= g}: rows[i] packs 1 (if parity) and
    D[i]^k for the odd k <= g (the even k follow, p_2k = p_k^2)."""
    m = F.m
    rows = []
    for a in D:
        v = 1 if parity else 0
        sh = 1
        a2 = F.mul(a, a)
        pw = a
        for k in range(1, g + 1, 2):
            v |= pw << sh
            sh += m
            pw = F.mul(pw, a2)
        rows.append(v)
    return rows


def rows_goppa(F, D, G2, g_inf=None, parity=True):
    """parity check of {T subset D : sum_{alpha in T} 1/(X - alpha) = 0 modulo G2, and p_k(T) = 0 for k <= g_inf}.
    A point alpha with gcd(X - alpha, G2) != 1 is excluded by a private bit."""
    m = F.m
    t = F.deg(G2)
    base = rows_inf(F, D, g_inf, parity) if g_inf is not None else [0] * len(D)
    off = (1 + ((g_inf + 1) // 2 if g_inf is not None else 0)) * m + 1
    rows = []
    nbad = 0
    for i, a in enumerate(D):
        v = base[i]
        if t > 0:
            if F.peval(G2, a) == 0:
                v |= 1 << (off + t * m + nbad)
                nbad += 1
            else:
                # inverse of (X - a) modulo G2: (G2(X) - G2(a)) / ((X - a) G2(a))
                q, r = F.pdivmod(F.padd(G2, [F.peval(G2, a)]), [a, 1])
                assert not r
                inv = F.pscale(q, F.inv(F.peval(G2, a)))
                for j, c in enumerate(inv):
                    v |= c << (off + j * m)
        rows.append(v)
    return rows


def weight(mask):
    return bin(mask).count("1")


# ---------------- domains ----------------

def domain(F, N, kind, seed=3):
    """basis of an N-dimensional F_2-subspace: 'field' (m = N), 'span' (1, x, .., x^(N-1)), 'rand'."""
    if kind in ("field", "span"):
        if kind == "field":
            assert F.m == N
        return [1 << i for i in range(N)]
    rnd = random.Random(seed)
    while True:
        basis = [rnd.randrange(1, F.q) for _ in range(N)]
        if len(set(F.span(basis))) == 1 << N:
            return basis


def rm_dim(r, N):
    from math import comb
    return sum(comb(N, i) for i in range(0, r + 1)) if r >= 0 else 0
