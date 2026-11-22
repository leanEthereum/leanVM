#!/usr/bin/env python3
"""Search for first integrals dE (Y1-degree b = 1) with contact order 2j along the lines of a word,
by linear algebra over GF(2^8), for 40-rate-half-residual.md.

For a word y on an F2-subspace D of GF(2^8) (n = 2^N points) and the code of degree <= D_code,
E = sum e_ik X^i Y^k (not both exponents even) has contact order >= 2j at (alpha, y_alpha) iff the Taylor
coefficients of E at that point with r + q < 2j, (r, q) not both even, vanish (checked in 40_checks.py B).
For each word the script finds the smallest weighted degree W of dE for which such an E exists on all
points of S (S = D or D minus 0), the dimension of the solution space, and whether E_Y and E_X are coprime
at random X (so that dE has no factor involving Y0).

The agreement A used for the window tests is the largest integer with A^2 <= n * D_code (the last agreement
not above the Johnson bound), because 0.7 n is above Johnson at these sizes; override with the third argument.

Run: python3 40_search.py N [j] [A]       N = 4, 5, 6;  j = 2 by default
"""
import sys
import random
from math import ceil, isqrt
from importlib import import_module

lib = import_module("40_lib")
mul, inv, fpow, peval = lib.mul, lib.inv, lib.fpow, lib.peval


def build_rows(monos, pts, j):
    conds = lib.contact_conditions(j)
    return [lib.taylor_row(monos, al, be, r, q) for (al, be) in pts for (r, q) in conds]


def min_W(pts, Dc, j, W_lo, W_hi):
    """smallest W in [W_lo, W_hi] with a nonzero solution; None if none. Monotone in W."""
    monos_hi = lib.support_b1(W_hi, Dc)
    rows_hi = build_rows(monos_hi, pts, j)

    def nullity(W):
        keep = set(lib.support_b1(W, Dc))
        cols = [i for i, mo in enumerate(monos_hi) if mo in keep]
        sub = [bytes(r[c] for c in cols) for r in rows_hi]
        return len(cols) - lib.rank(sub, len(cols)), cols

    if nullity(W_hi)[0] == 0:
        return None
    lo, hi = W_lo, W_hi
    while lo < hi:
        mid = (lo + hi) // 2
        if nullity(mid)[0] > 0:
            hi = mid
        else:
            lo = mid + 1
    nl, cols = nullity(lo)
    sub = [bytes(r[c] for c in cols) for r in rows_hi]
    basis = lib.nullspace(sub, len(cols))
    monos = [monos_hi[c] for c in cols]
    return lo, nl, monos, basis


def pgcd(p, q):
    def trim(a):
        while a and a[-1] == 0:
            a = a[:-1]
        return a
    p, q = trim(list(p)), trim(list(q))
    while q:
        # p mod q
        p = list(p)
        iq = inv(q[-1])
        while len(p) >= len(q):
            c = mul(p[-1], iq)
            s = len(p) - len(q)
            for i, qc in enumerate(q):
                p[s + i] ^= mul(c, qc)
            p = trim(p)
            if not p:
                break
        p, q = q, p
    return p


def coprime_test(monos, vec, D, rng):
    """gcd of E_Y(x0, Y) and E_X(x0, Y) at three random x0 outside D: degrees of the gcds."""
    degs = []
    dset = set(D)
    kmax = max(k for (_, k) in monos)
    for _ in range(3):
        x0 = rng.choice([x for x in range(1, 256) if x not in dset])
        a = [0] * (kmax + 1)
        c = [0] * (kmax + 1)
        for (i, k), e in zip(monos, vec):
            if not e:
                continue
            if k & 1:
                a[k - 1] ^= mul(e, fpow(x0, i))
            if i & 1:
                c[k] ^= mul(e, fpow(x0, i - 1))
        g = pgcd(a, c)
        degs.append(len(g) - 1)
    return degs


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    j = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    n = 1 << N
    k = n // 2
    Dc = k - 1
    D = lib.subspace_domain(N, seed=3)
    A = int(sys.argv[3]) if len(sys.argv) > 3 else isqrt(n * Dc)
    rng = random.Random(11)
    o = 2 * j
    print(f"n = {n}, code degree <= {Dc}, contact order {o}, A = {A} (A^2 = {A*A}, n D = {n*Dc})")
    print(f"thresholds: a list member with agreement t is a section automatically if W < {o} t "
          f"({o * A} at t = A); it is a root of E_Y unless W >= {o - 1} t + {Dc} ({(o - 1) * A + Dc} at t = A)")
    words = []
    for e in range(k, n):
        words.append((f"X^{e}", [fpow(al, e) for al in D]))
    for s in range(3):
        words.append((f"random{s}", [rng.randrange(256) for _ in D]))
    W_hi = int(3.4 * n) if j == 2 else int(1.8 * n * j)
    for name, y in words:
        for label, pts in (("D", list(zip(D, y))), ("D-0", [(al, be) for al, be in zip(D, y) if al])):
            res = min_W(pts, Dc, j, Dc, W_hi)
            if res is None:
                print(f"  {name:9s} on {label:3s}: none with W <= {W_hi}")
                continue
            W, nl, monos, basis = res
            vec = basis[0]
            ky = max(kk for (ii, kk), e in zip(monos, vec) if e)
            degs = coprime_test(monos, vec, D, rng)
            ns = len(pts)
            prof = [(ns, o), (n - ns, 0)]
            cut = lib.lemmaC_cut(n, Dc, A, 1, W, prof, (20, 40, 80))
            flag = ""
            if (o - 1) * (A - (n - ns)) + Dc <= W and cut is None:
                flag = "  <-- in the window at agreement A"
            print(f"  {name:9s} on {label:3s}: W_min = {W} ({W / n:.3f} n), nullity {nl}, deg_Y E = {ky}, "
                  f"gcd degrees {degs}, Lemma C at W_min: {'cut ' + str(cut) if cut else 'not cut'}{flag}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()
