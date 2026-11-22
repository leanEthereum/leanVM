#!/usr/bin/env python3
"""The sections of the flat cubic with polynomial lambda, on a subspace domain D (Section 4 of
43-low-rate-residuals.md).

E = X Y^3 + (X gamma_D(X^2) + e0) Y + e0 X^(n/2-1), word y = x^(n/2-1), rate 1/4.  A section P has
lambda_P = g = even part of P, and the sections with g in F[t], deg g <= j, are the pairs (g, z) with
    z^2 + z = L_D(X) g(X^2)^2 / e0^2,   z in F[X],       P = (e0 z/g(X^2) + X^(n/2)) / X.
The g form an F_2-vector space Lam_j, computed here as the kernel of an F_2-linear map (reduction of
L_D g^2/e0^2 modulo {z^2 + z}: c X^(2^v o) ~ c^(2^-v) X^o, o odd).  The script prints dim Lam_j and, when the
space is small enough, enumerates it and counts the polynomial sections of degree < n/4 by agreement.

Run: python3 43_flat_sections.py            (default battery, about 2 minutes)
     python3 43_flat_sections.py m N kind j (kind: field | span | rand)
"""
import random
import sys
import importlib

sys.path.insert(0, sys.path[0] or ".")
gfm = importlib.import_module("43_gf")


def domain(F, N, kind, seed=3):
    if kind in ("field", "span"):
        basis = [1 << i for i in range(N)]
        if kind == "field":
            assert F.m == N
    else:
        rnd = random.Random(seed)
        while True:
            basis = [rnd.randrange(1, F.q) for _ in range(N)]
            if len(set(F.span(basis))) == 1 << N:
                break
    return basis


def lam_space(F, LD, N, j):
    """Basis of Lam_j = {g in F[t], deg <= j : L_D g(X^2)^2/e0^2 in {z^2+z}} as lists of coefficients."""
    m = F.m
    n = 1 << N
    e0 = LD[1]
    ie02 = F.inv(F.mul(e0, e0))
    es = [LD[1 << s] for s in range(N + 1)]
    half = F.q >> 1  # exponent of the inverse Frobenius
    # classes: odd o -> list of (i, c, v): contributes (c * g_i^2)^(2^-v)
    classes = {}
    for s in range(N + 1):
        if es[s] == 0:
            continue
        c = F.mul(es[s], ie02)
        for i in range(j + 1):
            e = (1 << s) + 4 * i
            v = (e & -e).bit_length() - 1
            classes.setdefault(e >> v, []).append((i, c, v))
    keys = sorted(classes)
    nvar = (j + 1) * m
    # image of each unknown bit (i, b): concatenation over classes of an m-bit field element
    img = [0] * nvar
    for ki, o in enumerate(keys):
        for (i, c, v) in classes[o]:
            for b in range(m):
                x = F.mul(c, F.mul(1 << b, 1 << b))
                for _ in range(v):
                    x = F.sqrt(x)
                img[i * m + b] ^= x << (ki * m)
    # kernel by elimination with combination tracking
    piv = {}
    ker = []
    for t in range(nvar):
        vec, comb = img[t], 1 << t
        while vec:
            h = vec.bit_length() - 1
            if h in piv:
                pv, pc = piv[h]
                vec ^= pv
                comb ^= pc
            else:
                piv[h] = (vec, comb)
                break
        if vec == 0:
            ker.append(comb)
    out = []
    for comb in ker:
        g = [(comb >> (i * m)) & (F.q - 1) for i in range(j + 1)]
        out.append(g)
    return out


def solve_z(F, f):
    """polynomial z with z^2 + z = f (f(0) = 0 assumed), or None."""
    d = F.deg(f)
    z = [0] * (d + 1)
    for e in range(1, d + 1):
        z[e] = f[e] ^ (F.mul(z[e >> 1], z[e >> 1]) if e % 2 == 0 else 0)
    z = F.trim(z)
    if F.padd(F.psq(z), z) != F.trim(f):
        return None
    return z


def sections_of(F, LD, N, D, y, g):
    """polynomial sections of degree < n/4 with even part g (as a polynomial in t); returns list of (P, agreement)."""
    n = 1 << N
    e0 = LD[1]
    gX = F.subst_sq(F.trim(g))
    if not gX:
        return []
    f = F.pscale(F.pmul(LD, F.psq(gX)), F.inv(F.mul(e0, e0)))
    z = solve_z(F, f)
    assert z is not None, "g is not in Lam"
    res = []
    for zz in (z, F.padd(z, [1])):
        q, r = F.pdivmod(F.pscale(zz, e0), gX)
        if r or not q or q[0] != 0:
            continue
        # q = calL = X^(n/2) + X P
        if F.deg(q) != n // 2 or q[n // 2] != 1:
            continue
        P = F.trim(q[1:n // 2])
        if any(q[i] for i in range(n // 4 + 1, n // 2)):
            continue
        ag = sum(1 for a in D if a and F.peval(P, a) == y[a])
        assert F.even_odd(P)[0] == F.trim(g)
        assert ag == n // 2 - 1 - 2 * F.deg(F.trim(g)), "agreement = n/2 - 1 - 2 deg(lambda)"
        res.append((P, ag))
    return res


def run(m, N, kind, j, enum_limit=16, verbose=True):
    F = gfm.GF(m)
    n = 1 << N
    basis = domain(F, N, kind)
    D = F.span(basis)
    LD = F.subspace_poly(basis)
    y = {a: F.pow(a, n // 2 - 1) for a in D if a}
    ker = lam_space(F, LD, N, j)
    dim = len(ker)
    line = f"{kind:5s} GF(2^{m}) N={N} n={n} j<={j}: dim_F2 Lam_j = {dim}"
    hist = None
    if dim <= enum_limit:
        hist = {}
        total = 0
        for mask in range(1, 1 << dim):
            g = [0] * (j + 1)
            for t in range(dim):
                if mask >> t & 1:
                    g = [a ^ b for a, b in zip(g, ker[t])]
            for (P, ag) in sections_of(F, LD, N, D, y, g):
                hist[ag] = hist.get(ag, 0) + 1
                total += 1
        line += f"; polynomial sections of degree < n/4 by agreement: {dict(sorted(hist.items(), reverse=True))}"
    if verbose:
        print(line, flush=True)
    return dim, hist


if __name__ == "__main__":
    if len(sys.argv) >= 5:
        run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]),
            enum_limit=int(sys.argv[5]) if len(sys.argv) > 5 else 16)
    else:
        print("# D = F_{2^N}: the dimension is a necklace count, the sections include the BCH (Gold) words")
        for N in (4, 5, 6, 7):
            n = 1 << N
            run(N, N, "field", n // 16 if N > 4 else 1)
        print("# leanVM shape span(1..x^(N-1)) and random subspaces in a larger field")
        for (m, N, kind) in ((8, 4, "span"), (8, 5, "span"), (16, 5, "span"), (16, 6, "span"), (16, 7, "span"),
                             (16, 8, "span"), (12, 6, "rand"), (16, 7, "rand"), (16, 8, "rand")):
            n = 1 << N
            run(m, N, kind, max(n // 16, 1))
