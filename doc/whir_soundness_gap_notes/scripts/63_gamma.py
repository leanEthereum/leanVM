#!/usr/bin/env python3
"""Note 63, Sections 3 and 6: what each rung needs from the expansion constant gamma, and which d gives it.

  free   : largest gamma for which note 60's bound n*Phi(gamma*rho*C(t,2)) on the free sum of t members stays
           below (t-1)k (literal) and below B_t = (t-1)k + t*H(alpha_t)*n/64 (the rung's own budget).
  graph  : first-moment value gamma(d, phi) for a random d-out graph: every set Z of density phi has at most
           gamma*|Z| windows inside it, root of D(gamma || phi^d) = H(phi)/phi (+ 128/(phi n)); the same for
           windows with at most j points outside Z (gamma_j).
  python3 63_gamma.py free | graph | all
"""
import sys
from math import comb, log2


def H(p):
    return 0.0 if p <= 0 or p >= 1 else -p * log2(p) - (1 - p) * log2(1 - p)


def Phi(z):
    """piecewise linear concave, Phi(C(s,2)) = s - 1."""
    s = 1
    while comb(s + 1, 2) <= z:
        s += 1
    lo, hi = comb(s, 2), comb(s + 1, 2)
    return (s - 1) + (z - lo) / (hi - lo)


def Phi_inv(v):
    s = int(v) + 1
    lo, hi = comb(s, 2), comb(s + 1, 2)
    return lo + (v - (s - 1)) * (hi - lo)


def g(t, a):
    return t * a - 1 + (1 - a) ** t


def solve_alpha(t, rho, entropy=True):
    """threshold of rung t: g_t(alpha) = (t-1) rho + t H(alpha)/64."""
    lo, hi = rho, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        rhs = (t - 1) * rho + (t * H(mid) / 64 if entropy else 0)
        if g(t, mid) > rhs:
            hi = mid
        else:
            lo = mid
    return hi


def free_table():
    print("largest gamma for which the free sum bound of note 60 (with gamma for 1 - beta) closes rung t")
    print("lit: below (t-1)k; own: below the rung's budget B_t; asym: alpha_t^2/rho (t members replaced by a long list)")
    for rho in (1 / 2, 1 / 4, 1 / 8, 1 / 16):
        print(f"rate 1/{round(1 / rho)}")
        print("   t  alpha_t   lit     own     asym")
        for t in range(3, 17):
            a = solve_alpha(t, rho)
            B = (t - 1) * rho + t * H(a) / 64
            lit = Phi_inv((t - 1) * rho) / (rho * comb(t, 2))
            own = Phi_inv(B) / (rho * comb(t, 2))
            print(f"  {t:2d}  {a:.4f}  {min(lit, 1):.4f}  {min(own, 1):.4f}  {min(a * a / rho, 1):.4f}")


def D(a, b):
    """binary relative entropy in bits."""
    if a <= 0:
        return -log2(1 - b)
    if a >= 1:
        return -log2(b)
    return a * log2(a / b) + (1 - a) * log2((1 - a) / (1 - b))


def gamma_first_moment(p_in, phi, n=None):
    """least gamma with D(gamma || p_in) >= H(phi)/phi (+ 128/(phi n)); p_in = chance that a point of Z counts."""
    need = H(phi) / phi + (128 / (phi * n) if n else 0)
    if D(1.0, p_in) < need:
        return 1.0
    lo, hi = p_in, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if D(mid, p_in) >= need:
            hi = mid
        else:
            lo = mid
    return hi


def binom_tail_le(d, p, j):
    return sum(comb(d, i) * p ** i * (1 - p) ** (d - i) for i in range(j + 1))


def graph_table():
    print("random d-out graph, first moment over the graph, n = 2^25: gamma_j(d, phi) = largest fraction of a set of")
    print("density phi whose points have at most j partners outside the set (j = 0 is axiom W2)")
    n = 2 ** 25
    for phi in (1 / 2, 1 / 4, 1 / 8, 1 / 16):
        print(f"phi = 1/{round(1 / phi)}")
        print("   d   j=0     j=1     j=2     j=3")
        for d in (4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 20, 24):
            row = []
            for j in range(4):
                p_in = binom_tail_le(d, 1 - phi, j)
                row.append(gamma_first_moment(p_in, phi, n))
            print(f"  {d:2d}  " + "  ".join(f"{v:.4f}" for v in row))
    print("window form used by Lemma 5.1: gamma'_j(d, phi) = (number of x, inside Z or not, whose window has at most j")
    print("points outside Z) / |Z|; mean rate phi*P[Bin(d,1-phi) <= j] + (1-phi)*P[Bin(d,1-phi) <= j-1]")
    for phi in (1 / 2, 1 / 4):
        print(f"phi = 1/{round(1 / phi)}")
        print("   d   j=1     j=2     j=3     j=4")
        for d in (6, 8, 9, 10, 12, 14, 16, 20, 24):
            row = []
            for j in range(1, 5):
                pbar = phi * binom_tail_le(d, 1 - phi, j) + (1 - phi) * binom_tail_le(d, 1 - phi, j - 1)
                need = H(phi) + 128 / n
                lo, hi = pbar, 1.0
                for _ in range(200):
                    mid = (lo + hi) / 2
                    if D(mid, pbar) >= need:
                        hi = mid
                    else:
                        lo = mid
                row.append(hi / phi)
            print(f"  {d:2d}  " + "  ".join(f"{v:.4f}" for v in row))
    print("worst density: max over phi <= 1/2 of gamma_0(d, phi) (grid of 400 densities), and the phi attaining it")
    for d in (6, 8, 10, 12, 16):
        best = max(((gamma_first_moment((i / 800) ** d, i / 800, n), i / 800) for i in range(4, 401)))
        print(f"  d = {d:2d}: {best[0]:.4f} at phi = {best[1]:.4f}")


if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("free", "all"):
        free_table()
    if what in ("graph", "all"):
        graph_table()
