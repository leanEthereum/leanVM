#!/usr/bin/env python3
"""51_profiles.py: ALL contact profiles for the b = 1 survivor, for 51-degenerate-quintics.md.

Setting (notes 35, 41, 40, 45, 48, 50): n = 2^lg, Delta = n/2 + 5, A = ceil(a n).  G = dE = E_X + Y_1 E_Y is an
absolutely irreducible first integral with b = 1; a = E_Y has Y-degree 2K, c = E_X has Y-degree Dc, delta = max(2K+1, Dc).
Profile: n_j = number of lines of contact order 2j (j = 0..J, J = delta by Lemma M of note 40).

Linear lower bounds on W (each is  W >= const + sum_j n_j w_j):
  floor   W >= max(2K+1, Dc) Delta
  L1      W >= (2K+1) Delta + sum rho_K(j_alpha)                      (Corollary F part 1, note 48)
  L2(l)   W >= Delta + l A + sum_j n_j (rho_K(j) - (l - c_K(j))_+)     (Corollary F part 2 + LP duality; one list
                                                                        member that is not a root of E_Y)
  B       (Da + Dc) W >= Delta Dc (1 + Da) + sum (4j^2 - 2j - 1)       (Lemma B of note 40, Da = 2K)
  T       3 W >= 8 Delta + 1 + 2 sum_{j >= 2} n_j (3j - 4)             (Theorem 4 of note 45 for j = 2, 3, extended to all j
                                                                        in note 51, Section 1: K = 2, Dc <= 5, det E != 0)
  D(l)    W >= 3 Delta + l A - sum_j n_j (l - j)_+                     (Lemma 3.1 of note 51: K = 2, A and B dependent)
Cut: Lemma C of note 35 with (m, B):  Phi(W) = N(B, mA) - N(B-1, mA - W) > sum_j n_j psi(j),
  psi(j) = R(m, B) - R(m - 2j, B - 1), valid for W <= mA - Delta (m + B).
Phi is concave and nondecreasing in W, so  g(x) = sum_j n_j psi(j) - Phi(l(x))  is CONVEX in the profile for each
linear lower bound l; hence g < 0 on a polytope iff g < 0 at its vertices (the argument of Lemma U of note 41).
The script covers the profile simplex by dyadic boxes (intersected with the simplex), and for each cell finds one
(m, B) and one lower bound with g < 0 at every vertex, with exact integer / rational arithmetic.  Cells that cannot
be covered down to the minimal size are reported: they are an outer approximation of the open region.

Run:  python3 51_profiles.py [a=0.7065] [lg=25] [case=all] [depth=7]
"""
import sys
import itertools
from fractions import Fraction as Fr
from functools import lru_cache
from math import floor


@lru_cache(maxsize=None)
def R(m, B):
    if m <= 0 or B < 0:
        return 0
    tot = 0
    for s in range(m):
        tot += (s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0)
    return tot


def N(B, Z, D):
    """sum_{t >= 0} (min(t, B) + 1) (Z - D t)_+ , Z an int or a Fraction."""
    if B < 0 or Z <= 0:
        return 0
    q = floor(Fr(Z) / D)
    if q >= B:
        return (B + 1) * ((q + 1) * Z - D * q * (q + 1) // 2) - (Z * B * (B + 1) / 2 if isinstance(Z, Fr) else Z * B * (B + 1) // 2) + D * (B - 1) * B * (B + 1) // 6
    return sum((min(t, B) + 1) * (Z - D * t) for t in range(q + 1))


def N_loop(B, Z, D):
    tot, t = 0, 0
    while Z - D * t > 0:
        tot += (min(t, B) + 1) * (Z - D * t)
        t += 1
    return tot


def selfcheck():
    import random
    from importlib import import_module
    ref = import_module("41_counts")
    rnd = random.Random(51)
    for _ in range(3000):
        m, B = rnd.randint(1, 80), rnd.randint(0, 40)
        assert R(m, B) == ref.R(m, B) == ref.R_sum(m, B)
        D = rnd.randint(3, 50)
        Z = rnd.randint(1, 60 * D)
        assert N(B, Z, D) == N_loop(B, Z, D) == ref.N(B, Z, D), (B, Z, D)
        Zf = Fr(rnd.randint(1, 600 * D), 7)
        v = sum((min(t, B) + 1) * max(Zf - D * t, 0) for t in range(700))
        assert N(B, Zf, D) == v, (B, Zf, D)
    print("selfcheck: R and N agree with 41_counts.py and with the defining sums (3000 random arguments)")


# ---------------------------------------------------------------- even certificates (note 50, Theorem 1.3)

def even_certificates(n, D, A, qs=(2, 4, 8, 16, 32, 64, 128, 256, 512)):
    out = []
    for q in qs:
        for m in range(2 * q, 12 * q + 40):
            rho1 = m * m - (q - 1) * m + q * (3 * q - 1) // 2
            if N(0, m * A, D) + N(0, m * A - q * D, D) > n * rho1:
                out.append((q, m, (m * A - 1) // D, (m * A - 1) // q))
                break
    return out


# ---------------------------------------------------------------- lower bounds

def rhoK(K, j):
    return max(j - K, 2 * j - 1 - 2 * K, 0)


def nu(j):
    return max(2 * j - 1, 0)


def bounds_for(case, n, D, A):
    """list of (name, const (Fraction), weights w_0..w_J (Fractions))."""
    K, Dc, kind = case["K"], case["Dc"], case["kind"]
    J = max(2 * K + 1, Dc)
    Da = 2 * K
    out = [("floor", Fr(max(2 * K + 1, Dc) * D), [Fr(0)] * (J + 1))]
    out.append(("L1", Fr((2 * K + 1) * D), [Fr(rhoK(K, j)) for j in range(J + 1)]))
    cK = [nu(j) - rhoK(K, j) for j in range(J + 1)]
    for lam in sorted(set(cK) - {0}):
        out.append(("L2(%d)" % lam, Fr(D + lam * A), [Fr(rhoK(K, j) - max(lam - cK[j], 0)) for j in range(J + 1)]))
    if Da + Dc > 0:
        out.append(("B", Fr(D * Dc * (1 + Da), Da + Dc), [Fr(max(4 * j * j - 2 * j - 1, 0), Da + Dc) for j in range(J + 1)]))
    if kind == "nondeg":
        out.append(("T", Fr(8 * D + 1, 3), [Fr(2 * (3 * j - 4), 3) if j >= 2 else Fr(0) for j in range(J + 1)]))
    if kind == "dep":
        for lam in range(1, J + 1):
            out.append(("D(%d)" % lam, Fr(3 * D + lam * A), [Fr(-max(lam - j, 0)) for j in range(J + 1)]))
    return J, out


# ---------------------------------------------------------------- the covering

class Cover:
    def __init__(self, n, D, A, Wmax, case, depth, ms):
        self.n, self.D, self.A, self.Wmax, self.case, self.depth = n, D, A, Wmax, case, depth
        self.J, self.bounds = bounds_for(case, n, D, A)
        self.cands = []
        for m in ms:
            Bs = range(1, m // 2 + 1) if m <= 80 else range(2, m // 2 + 1, max(1, m // 60))
            for B in Bs:
                if D * (m + B) <= m * A - Wmax:
                    psi = [R(m, B) - R(m - 2 * j, B - 1) for j in range(self.J + 1)]
                    self.cands.append((m, B, psi, N(B, m * A, D)))
        self.nev = 0
        self.used = {}
        self.open = []
        self.cells = 0

    def g(self, cand, bound, prof):
        """sum n_j psi(j) - Phi(lower bound), exact; prof = integer profile (n_0..n_J)."""
        m, B, psi, NB = cand
        _, const, w = bound
        Wl = const + sum(wj * nj for wj, nj in zip(w, prof))
        if Wl.denominator == 1:
            Wl = Wl.numerator
        self.nev += 1
        return sum(p * nj for p, nj in zip(psi, prof)) - (NB - N(B - 1, m * self.A - Wl, self.D))

    def vertices(self, lo, hi, unit):
        """vertices of box prod [lo_i, hi_i] (units of n / unit, coordinates j = 1..J) intersected with sum <= unit."""
        J = self.J
        vs = set()
        for corner in itertools.product(*[(l, h) for l, h in zip(lo, hi)]):
            s = sum(corner)
            if s <= unit:
                vs.add(corner)
            else:
                for i in range(J):
                    if corner[i] == hi[i]:
                        xi = unit - (s - corner[i])
                        if lo[i] <= xi < hi[i]:
                            vs.add(corner[:i] + (xi,) + corner[i + 1:])
        return vs

    def try_cell(self, lo, hi, unit):
        vs = self.vertices(lo, hi, unit)
        if not vs:
            return True
        sc = self.n // unit
        profs = [[(unit - sum(v)) * sc] + [x * sc for x in v] for v in vs]
        ctr = [sum(p[j] for p in profs) // len(profs) for j in range(self.J + 1)]
        ctr[0] += self.n - sum(ctr)
        # rank (candidate, bound) pairs by the value at the centre, then verify the best ones at all vertices
        scored = []
        for bi, bd in enumerate(self.bounds):
            best = None
            for ci, cand in enumerate(self.cands):
                val = self.g(cand, bd, ctr)
                if val < 0:
                    scored.append((Fr(val, cand[0] ** 2), ci, bi))
        scored.sort()
        for _, ci, bi in scored[:12]:
            if all(self.g(self.cands[ci], self.bounds[bi], p) < 0 for p in profs):
                key = (self.cands[ci][0], self.cands[ci][1], self.bounds[bi][0])
                self.used[key] = self.used.get(key, 0) + 1
                return True
        return False

    def window(self, opened, unit):
        """rigorous outer window over the open cells: smallest lower bound, and the largest W not cut by the
        candidates when the credit is taken at the upper corner of the cell (credit is nondecreasing in n_j, j >= 1)."""
        sc = self.n // unit
        lo_all, hi_all = None, 0
        best = [c for c in self.cands if c[0] == max(cc[0] for cc in self.cands)]
        for lo, hi in opened:
            wl = 0
            for _, const, w in self.bounds:
                v = const + self.n * w[0]
                for j in range(1, self.J + 1):
                    d = w[j] - w[0]
                    v += d * sc * (lo[j - 1] if d >= 0 else hi[j - 1])
                wl = max(wl, v)
            wl = -((-wl.numerator) // wl.denominator)
            cred_hi = [None] * len(best)
            wh = self.Wmax + 1
            for m, B, psi, NB in best:
                cred = self.n * psi[0] + sum((psi[j] - psi[0]) * sc * hi[j - 1] for j in range(1, self.J + 1))
                a_, b_ = wl, self.Wmax + 1
                if NB - N(B - 1, m * self.A - a_, self.D) > cred:
                    b_ = a_
                while a_ < b_:
                    mid = (a_ + b_) // 2
                    if NB - N(B - 1, m * self.A - mid, self.D) > cred:
                        b_ = mid
                    else:
                        a_ = mid + 1
                wh = min(wh, b_)
            lo_all = wl if lo_all is None else min(lo_all, wl)
            hi_all = max(hi_all, wh)
        return lo_all, hi_all

    def run(self):
        unit = 1 << self.depth
        stack = [((0,) * self.J, (unit,) * self.J, 0)]
        while stack:
            lo, hi, lev = stack.pop()
            if sum(lo) > unit:
                continue
            self.cells += 1
            if self.try_cell(lo, hi, unit):
                continue
            widths = [h - l for l, h in zip(lo, hi)]
            wmax = max(widths)
            if wmax <= 1:
                self.open.append((lo, hi))
                continue
            i = widths.index(wmax)
            mid = (lo[i] + hi[i]) // 2
            stack.append((lo, hi[:i] + (mid,) + hi[i + 1:], lev + 1))
            stack.append((lo[:i] + (mid,) + lo[i + 1:], hi, lev + 1))
        return self.open


CASES = {
    "K0": [dict(K=0, Dc=Dc, kind="gen") for Dc in (1, 2, 3, 4, 5, 6)],
    "K1": [dict(K=1, Dc=Dc, kind="gen") for Dc in (3, 4, 5, 6)],
    "K2nondeg": [dict(K=2, Dc=5, kind="nondeg")],
    "K2dep": [dict(K=2, Dc=5, kind="dep"), dict(K=2, Dc=6, kind="dep")],
    "K2sextic": [dict(K=2, Dc=6, kind="gen")],
    "K2deg": [dict(K=2, Dc=5, kind="gen")],
}


def main():
    a, lg, which, depth = Fr("0.7065"), 25, "all", 7
    for arg in sys.argv[1:]:
        if arg.startswith("a="):
            a = Fr(arg[2:])
        elif arg.startswith("lg="):
            lg = int(arg[3:])
        elif arg.startswith("case="):
            which = arg[5:]
        elif arg.startswith("depth="):
            depth = int(arg[6:])
    selfcheck()
    n = 1 << lg
    D = n // 2 + 5
    A = -((-a.numerator * n) // a.denominator)
    print("n = 2^%d, Delta = %d, a = %s, A = %d" % (lg, D, a, A))
    certs = even_certificates(n, D, A)
    if not certs:
        print("no even certificate (q, 1; m) at this agreement")
        return
    for q, m, d, wq in certs:
        print("  even certificate (q, m) = (%d, %d): d = %d, delta <= %d, W <= %d = %.4f n" % (q, m, d, d // q, wq, wq / n))
    Wmax = min(c[3] for c in certs)
    dmax = max(c[2] for c in certs)
    delta_max = min(c[2] // c[0] for c in certs)
    print("survivor with more than delta * %d members: W <= %d = %.4f n, delta <= %d" % (dmax, Wmax, Wmax / n, delta_max))
    ms = (24, 32, 40, 60, 80, 120, 240, 480, 960)
    names = list(CASES) if which == "all" else which.split(",")
    for name in names:
        for case in CASES[name]:
            if max(2 * case["K"] + 1, case["Dc"]) > delta_max:
                print("case %s %s: delta > %d, excluded by the even certificates" % (name, case, delta_max))
                continue
            if max(2 * case["K"] + 1, case["Dc"]) * D > Wmax:
                print("case %s %s: floor above Wmax, excluded" % (name, case))
                continue
            cv = Cover(n, D, A, Wmax, case, depth, ms)
            opened = cv.run()
            mm = max((k[0] for k in cv.used), default=0)
            print("case %s K=%d Dc=%d kind=%s: J = %d, %d cells, %d evaluations, largest m used %d, open minimal cells: %d"
                  % (name, case["K"], case["Dc"], case["kind"], cv.J, cv.cells, cv.nev, mm, len(opened)))
            top = sorted(cv.used.items(), key=lambda kv: -kv[1])[:6]
            print("    most used (m, B, bound): " + ", ".join("%s x%d" % (k, v) for k, v in top))
            if opened:
                unit = 1 << depth
                for j in range(1, cv.J + 1):
                    print("    open region: x_%d in [%.4f, %.4f]" % (j, min(o[0][j - 1] for o in opened) / unit, max(o[1][j - 1] for o in opened) / unit))
                x0 = [unit - sum(o[1]) for o in opened] + [unit - sum(o[0]) for o in opened]
                print("    open region: x_0 in [%.4f, %.4f]" % (max(min(x0), 0) / unit, max(x0) / unit))
                lo_all, hi_all = cv.window(opened, unit)
                print("    open region: W in [%d, %d) = [%.4f, %.4f) n   (rigorous outer bounds over the open cells)"
                      % (lo_all, hi_all, lo_all / n, hi_all / n))


if __name__ == "__main__":
    main()
