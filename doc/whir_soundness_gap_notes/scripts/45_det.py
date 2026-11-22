#!/usr/bin/env python3
"""45_det.py: the determinant of a quintic potential, for 45-rate-half-second-attempt.md, Theorem 4.

E = Y A^2 + X C^2 + X Y B^2 (mod squares), A = A_2 Y^2 + A_1 Y + A_0 etc.  det(E) := det [A_k; B_k; C_k] in F[X].
Claims checked:
  (1) if dE has contact order >= 4 on the line of alpha then (X - alpha)^2 divides det(E);
  (2) deg det(E) <= (3 W - 8 D - 1) / 2, W the weighted degree of dE;
  so det(E) != 0 and contact 4 on all n lines force  W >= (4 n + 8 D + 1) / 3;
  (3) det(E) = 0 iff E = (Y - psi) a mod squares over F(X) for a rational function psi and a = E_Y
      (checked: det = 0 for the closed form of the 11/16 family and for the F_n family).
For every element of a basis of the solution space at W_1 and at W_1 + 4 (and for random combinations) the script
prints deg det, the bound, and the multiplicity of det at every alpha (minimum over alpha).

Run: python3 45_det.py [N]      N = 4, 5 (default 5)
"""
import sys
import random
from importlib import import_module

lib = import_module("40_lib")
lat = import_module("45_lattice")
fam = import_module("45_family")
mul, inv, fpow = lib.mul, lib.inv, lib.fpow
padd, pmul, trim = fam.padd, fam.pmul, fam.trim


def conics(monos, vec):
    A, B, C = lat.split_sqrt(monos, vec)
    out = []
    for P in (A, B, C):
        row = []
        for k in range(3):
            co = [0] * (1 + max([i for (i, kk) in P if kk == k], default=-1))
            for (i, kk), c in P.items():
                if kk == k:
                    co[i] = c
            row.append(co)
        out.append(row)
    return out


def det3(Mx):
    def d2(a, b, c, d):
        return padd(pmul(a, d), pmul(b, c))
    (a0, a1, a2), (b0, b1, b2), (c0, c1, c2) = Mx
    t = pmul(a0, d2(b1, b2, c1, c2))
    t = padd(t, pmul(a1, d2(b0, b2, c0, c2)))
    t = padd(t, pmul(a2, d2(b0, b1, c0, c1)))
    return trim(t)


def mult_at(p, al):
    """multiplicity of the root al of p (0 if not a root)."""
    m = 0
    p = list(p)
    while p:
        # synthetic division by (X - al)
        q = [0] * (len(p) - 1)
        r = 0
        for i in range(len(p) - 1, -1, -1):
            r = mul(r, al) ^ p[i]
            if i > 0:
                q[i - 1] = r
        if r:
            break
        m += 1
        p = trim(q)
    return m


def report(tag, monos, vec, D, Dc, n):
    W = max((i + Dc * k if (k & 1) else i - 1 + Dc * k) for (i, k), c in zip(monos, vec) if c)
    d = det3(conics(monos, vec))
    bound = (3 * W - 8 * Dc - 1) // 2
    if not d:
        print(f"    {tag}: W = {W}: det = 0 (degenerate)")
        return
    mm = min(mult_at(d, al) for al in D)
    print(f"    {tag}: W = {W}: deg det = {len(d) - 1} <= {bound}; min multiplicity over D = {mm}; "
          f"2n = {2 * n}; W >= (4n + 8D + 1)/3 = {(4 * n + 8 * Dc + 1) / 3:.1f}")


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    n = 1 << N
    Dc = n // 2 - 1
    D = lib.subspace_domain(N, seed=3)
    rng = random.Random(3)
    print(f"n = {n}, D = {Dc}")
    words = [("random0", [rng.randrange(256) for _ in D]), ("random1", [rng.randrange(256) for _ in D]),
             (f"X^{3 * n // 4 - 1}", [fpow(al, 3 * n // 4 - 1) for al in D]),
             (f"X^{n // 2 + 3}", [fpow(al, n // 2 + 3) for al in D])]
    for name, y in words:
        pts = list(zip(D, y))
        mins = lat.minima(pts, Dc, n)
        print(f"  {name}: W_1 = {mins[0]}")
        for W in (mins[0], mins[0] + 4):
            monos = lat.support(W, Dc)
            basis = lib.nullspace(lat.rows_for(monos, pts), len(monos))
            report(f"basis[0] at W <= {W} (nullity {len(basis)})", monos, basis[0], D, Dc, n)
            if len(basis) > 1:
                vec = [0] * len(monos)
                for b in basis:
                    c = rng.randrange(1, 256)
                    vec = [x ^ mul(c, yv) for x, yv in zip(vec, b)]
                report("random combination", monos, vec, D, Dc, n)
        sys.stdout.flush()
    # contact order 6 on all lines (15 conditions per point): multiplicity >= 5 of det at every alpha
    if N == 4:
        y = [rng.randrange(256) for _ in D]
        pts = list(zip(D, y))
        conds = lib.contact_conditions(3)
        for W in range(4 * n, 6 * n):
            monos = lat.support(W, Dc)
            rows = [lib.taylor_row(monos, al, be, r, q) for (al, be) in pts for (r, q) in conds]
            basis = lib.nullspace(rows, len(monos))
            if basis:
                vec = [0] * len(monos)
                for bv in basis:
                    cf = rng.randrange(1, 256)
                    vec = [x ^ mul(cf, yv) for x, yv in zip(vec, bv)]
                d = det3(conics(monos, vec))
                if not d:
                    continue      # only degenerate solutions so far
                mm = min(mult_at(d, al) for al in D)
                print(f"  contact 6 on all lines, random word: random combination of the {len(basis)} solutions at W <= {W}: "
                      f"deg det = {len(d) - 1} <= {(3 * W - 8 * Dc - 1) // 2}, min multiplicity over D = {mm} (Theorem 4: >= 5), "
                      f"bound (10 n + 8 D + 1) / 3 = {(10 * n + 8 * Dc + 1) / 3:.1f}")
                break
    # the closed form of the family (45_family) is degenerate
    E, a, LD = fam.closed_form(D, n)
    Er = fam.reduce_mod_squares(E)
    monos = sorted(Er)
    report("closed form of the 11/16 family", monos, [Er[m] for m in monos], D, Dc, n)


if __name__ == "__main__":
    main()
