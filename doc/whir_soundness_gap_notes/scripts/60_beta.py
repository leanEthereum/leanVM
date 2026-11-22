#!/usr/bin/env python3
"""Note 60, Section 3: interior losses in the N-cube and what they prove.

  beta(N, f)  = 1 - iota(f)/f : least fraction of a set of f points lost to its inner boundary.
  betamin(N, cap) = min over 1 <= f <= cap of beta(N, f) (rigorous lower bound by adaptive search).
  three sets : sum of |int| of three sets of < k points, against 2k.
  V(t)       : bound on the free sum for t members with pairwise coincidence sets < k (Proposition 3.8).

  python3 60_beta.py beta | three | lp | all
"""
import importlib.util, os, sys
from fractions import Fraction
from math import comb

spec = importlib.util.spec_from_file_location("h", os.path.join(os.path.dirname(os.path.abspath(__file__)), "60_harper.py"))
H = importlib.util.module_from_spec(spec)
spec.loader.exec_module(H)
NI, iota, ball = H.NI, H.iota, H.ball


def ratio_max(N, cap, tol=1e-7):
    """upper and lower bounds on R = max over 1 <= a, NI(a) <= cap of a / NI(a)."""
    amax = iota(N, cap)
    if amax < 1:
        return 0.0, 0.0
    lb = amax / NI(N, amax)
    r = 0
    while ball(N, r) <= amax:
        lb = max(lb, ball(N, r) / NI(N, ball(N, r)))
        r += 1
    ub = lb
    stack = [(1, amax)]
    while stack:
        a1, a2 = stack.pop()
        f1 = NI(N, a1)
        lb = max(lb, a1 / f1)
        if a1 == a2:
            continue
        u = a2 / f1
        if u <= lb + tol:
            ub = max(ub, u)
            continue
        mid = (a1 + a2) // 2
        stack.append((a1, mid))
        stack.append((mid + 1, a2))
    return lb, max(lb, ub)


def Phi(c):
    """concave piecewise linear function with Phi(C(s,2)) = s - 1: the largest average of
    (class size - 1) over positions whose average number of coinciding pairs is c."""
    s = 1
    while comb(s + 1, 2) <= c:
        s += 1
    return (s - 1) + (c - comb(s, 2)) / Fraction(s)


def free_sum_bound(t, rho, keep):
    """Proposition 3.8: sum_x (c_x - 1)_+ over free agreements of t members is at most
    n * Phi(keep * rho * C(t,2)), keep = max of |int Z|/|Z| over sets of fewer than k points."""
    return Phi(Fraction(keep) * Fraction(rho) * comb(t, 2))


RATES = (2, 4, 8, 16)


def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    Ns = list(range(10, 29))
    if mode in ("beta", "all"):
        phis = [Fraction(1, 64), Fraction(1, 32), Fraction(1, 16), Fraction(1, 8), Fraction(1, 4), Fraction(1, 3), Fraction(3, 8), Fraction(1, 2), Fraction(5, 8), Fraction(3, 4)]
        print("beta(N, phi) = 1 - iota(f)/f at f = floor(phi n) - 1  (largest set of fewer than phi n points)")
        print("N | " + " | ".join(str(p) for p in phis))
        for N in Ns:
            n = 2 ** N
            row = []
            for p in phis:
                f = int(p * n) - 1
                row.append(f"{1 - iota(N, f) / f:.4f}" if f >= 1 else "-")
            print(f"{N} | " + " | ".join(row))
        print()
        print("betamin(N, rho) = min over 1 <= f <= rho n - 1 of beta(N, f): [lower bound, upper bound]")
        for N in Ns:
            n = 2 ** N
            row = []
            for r in RATES:
                lo, hi = ratio_max(N, n // r - 1)
                row.append(f"1/{r}: [{1 - hi:.4f}, {1 - lo:.4f}]")
            print(f"{N} | " + " | ".join(row))
    if mode in ("three", "all"):
        print()
        print("three sets of < k points: (2k - bound)/n.  coprime: disjoint sets, bound = min(3 iota(k-1), n*Rmax);  common zeros: bound = 3 iota(k-1)")
        for N in Ns:
            n = 2 ** N
            row = []
            for r in RATES:
                k = n // r
                i3 = 3 * iota(N, k - 1)
                lo, hi = ratio_max(N, k - 1)
                cop = min(i3, hi * n)
                row.append(f"1/{r}: coprime {(2 * k - cop) / n:+.4f} common {(2 * k - i3) / n:+.4f}")
            print(f"{N} | " + " | ".join(row))
    if mode in ("lp", "all"):
        print()
        print("free sum bound V(t) = Phi((1-beta) rho C(t,2)) against (t-1) rho ('+' below, '-' not), and alpha_free(t): g_t(alpha) = V")
        for N in (10, 12, 14, 16, 18, 20, 22, 24, 25, 26, 27, 28):
            n = 2 ** N
            for r in RATES:
                lo, hi = ratio_max(N, n // r - 1)
                keep = Fraction(int(hi * 10 ** 6) + 1, 10 ** 6)
                marks, al = "", []
                for t in range(3, 9):
                    v = free_sum_bound(t, Fraction(1, r), keep)
                    marks += "+" if v < Fraction(t - 1, r) else "-"
                    # alpha_free: g_t(alpha) = t alpha - 1 + (1 - alpha)^t = V (Jensen form of note 57 Section 8)
                    lo_a, hi_a = 0.0, 1.0
                    for _ in range(60):
                        mid = (lo_a + hi_a) / 2
                        if t * mid - 1 + (1 - mid) ** t < float(v):
                            lo_a = mid
                        else:
                            hi_a = mid
                    al.append(f"{hi_a:.4f}")
                print(f"N={N} rho=1/{r} beta={1 - hi:.4f}: t=3..8 {marks}  alpha_free: {' '.join(al)}  limit sqrt((1-beta)rho)={(hi / r) ** 0.5:.4f}")
        print()
        print("smallest beta (step 0.0001) with V(t) < (t-1) rho")
        for r in RATES:
            row = []
            for t in range(3, 9):
                lo_b, hi_b = 0, 10000
                while lo_b < hi_b:
                    mid = (lo_b + hi_b) // 2
                    if free_sum_bound(t, Fraction(1, r), 1 - Fraction(mid, 10000)) < Fraction(t - 1, r):
                        hi_b = mid
                    else:
                        lo_b = mid + 1
                row.append(f"t={t}: {lo_b / 10000:.4f}")
            print(f"rho=1/{r}: " + "  ".join(row))

if __name__ == "__main__":
    main()
