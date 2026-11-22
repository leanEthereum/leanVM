#!/usr/bin/env python3
"""dim_F2 of Lam_j (sections of the flat cubic with polynomial lambda of degree <= j, see 43_flat_sections.py)
on the leanVM shape D = span(1, x, ..., x^(N-1)) inside K = GF(2^64) = F2[x]/(x^64 + x^4 + x^3 + x + 1).

Only Frobenius powers and multiplications by constants are needed.  The condition for g = sum g_i t^i is, for every
odd o:   sum over (s, i) with 2^s + 4i = 2^v o   of   (e_s g_i^2 / e0^2)^(2^-v)  =  0,
raised here to the power 2^vmax(o) so that no square root is taken.
Run: python3 43_flat_K.py [Nmax]     (default 14: N = 5..14, j = 0, n/64 (the window) and, while it fits, n/16
     (agreement 3n/8 - 1); about 1 minute)
"""
import sys

MOD = (1 << 64) | 0x1B
MASK = (1 << 64) - 1


def mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> 64:
            a ^= MOD
    return r


def sq(a):
    return mul(a, a)


def inv(a):
    r, e, b = 1, (1 << 64) - 2, a
    while e:
        if e & 1:
            r = mul(r, b)
        b = sq(b)
        e >>= 1
    return r


def subspace_coeffs(N):
    """coefficients e_s of X^(2^s) in L_D, D = span(1, x, ..., x^(N-1))."""
    L = [1]  # L = sum L[s] X^(2^s)
    for i in range(N):
        b = 1 << i
        # L(b)
        val, p = 0, b
        for s in range(len(L)):
            val ^= mul(L[s], p)
            p = sq(p)
        assert val
        new = [0] * (len(L) + 1)
        for s in range(len(L)):
            new[s + 1] ^= sq(L[s])
            new[s] ^= mul(L[s], val)
        L = new
    return L


def lam_dim(N, j):
    es = subspace_coeffs(N)
    e0 = es[0]
    ie02 = inv(sq(e0))
    classes = {}
    for s in range(N + 1):
        if es[s] == 0:
            continue
        c = mul(es[s], ie02)
        for i in range(j + 1):
            e = (1 << s) + 4 * i
            v = (e & -e).bit_length() - 1
            classes.setdefault(e >> v, []).append((i, c, v))
    keys = sorted(classes)
    nvar = (j + 1) * 64
    img = [0] * nvar
    bsq = [sq(1 << b) for b in range(64)]
    for ki, o in enumerate(keys):
        vmax = max(v for (_, _, v) in classes[o])
        for (i, c, v) in classes[o]:
            for b in range(64):
                x = mul(c, bsq[b])
                for _ in range(vmax - v):
                    x = sq(x)
                img[i * 64 + b] ^= x << (ki * 64)
    piv = {}
    dim = 0
    for t in range(nvar):
        vec = img[t]
        while vec:
            h = vec.bit_length() - 1
            if h in piv:
                vec ^= piv[h]
            else:
                piv[h] = vec
                break
        if vec == 0:
            dim += 1
    return dim, es


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 14
    for N in range(5, Nmax + 1):
        n = 1 << N
        out = []
        for j in sorted(set([0, max(n // 64, 1), n // 16])):
            if (j + 1) * 64 > 17000:
                continue
            d, es = lam_dim(N, j)
            out.append(f"j<={j}: {d}")
        nz = all(e != 0 for e in es)
        print(f"K = GF(2^64), D = span(1..x^{N - 1}), n = {n}: dim_F2 Lam_j  " + ", ".join(out)
              + f"   (all e_s nonzero: {nz}; e_(N-1) = {es[N - 1]:#018x})", flush=True)
