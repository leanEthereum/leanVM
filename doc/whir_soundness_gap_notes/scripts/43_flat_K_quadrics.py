#!/usr/bin/env python3
"""Sections of the flat cubic on the leanVM shape D = span(1, x, ..., x^(N-1)) in K = GF(2^64) whose lambda = g has
g(X^2) affine linearized in X (Section 4.4 of 43-low-rate-residuals.md).

For such g the solution z of z^2 + z = L_D g(X^2)^2/e0^2 is a quadratic Boolean function on D (checked at N = 12:
Walsh spectra of the 7 nonconstant classes are flat, ranks 10 and 12), and the conditions are the Gold moment
equations of note 01, Section 3.5.  The script computes, for g(X^2) of X-degree <= 2^top (tau-degree 2^(top-1)),
    extra(N, top) = dim_F2 {such g in Lam} - N,
which is 0 on a generic domain.  Observed: extra = max(0, C(N,2) - 64 (t - 1)) with top = N - 1 - t, up to a
deficiency of at most 3 (N = 12, t = 2: 3; N = 20, t = 4: 1), that is one 64-bit condition per moment equation.
A polynomial section built on such a g would have agreement n/2 - 1 - 2^top; it needs z of rank exactly 2t.
Run: python3 43_flat_K_quadrics.py [Nmin Nmax]   (default 12 28; about 6 minutes)
"""
import sys
import importlib

sys.path.insert(0, sys.path[0] or ".")
k = importlib.import_module("43_flat_K")
mul, sq, inv = k.mul, k.sq, k.inv


def lam_dim_support(N, supp):
    es = k.subspace_coeffs(N)
    e0 = es[0]
    ie02 = inv(sq(e0))
    classes = {}
    for s in range(N + 1):
        c = mul(es[s], ie02)
        for idx, i in enumerate(supp):
            e = (1 << s) + 4 * i
            v = (e & -e).bit_length() - 1
            classes.setdefault(e >> v, []).append((idx, c, v))
    keys = sorted(classes)
    nvar = len(supp) * 64
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
    return dim


if __name__ == "__main__":
    Nmin = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    Nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 28
    print("N: for t = 2..8 (agreement of a tight section n/2 - 1 - n/2^(t+1)): extra dimension, [C(N,2) - 64(t-1)]")
    for N in range(Nmin, Nmax + 1):
        cells = []
        for t in range(2, 9):
            top = N - 1 - t
            if top < 1:
                continue
            supp = [0] + [1 << u for u in range(top)]
            d = lam_dim_support(N, supp) - N
            cells.append(f"t={t}: {d} [{N * (N - 1) // 2 - 64 * (t - 1)}]")
        print(f"N = {N}: " + "; ".join(cells), flush=True)
