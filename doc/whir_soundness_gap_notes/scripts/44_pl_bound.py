#!/usr/bin/env python3
"""Note 44, section 5: the three-wise Johnson bound for primitive lists and the list bound it gives through the
period descent of note 39 (Theorem 1.3), conditional on Conjecture P in the formal model (Theorem 5.5, E = 0).

  python3 44_pl_bound.py            tables of the note
  python3 44_pl_bound.py check      brute-force checks of Lemma 5.2 (convexity, Jensen step) and of the class maximum

Exact integer arithmetic for the counting inequality, floats only for logarithms.
"""
import sys
from fractions import Fraction as Fr
from math import comb, log2, floor


def tau3(rho):
    """root of tau^2 (3 - tau) = 2 rho in (rho, sqrt(rho))"""
    lo, hi = rho, rho ** 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        if mid * mid * (3 - mid) > 2 * rho:
            hi = mid
        else:
            lo = mid
    return hi


def tau_m(rho, m):
    """threshold of the m-wise count: m tau - 1 + (1 - tau)^m = (m - 1) rho (m = 2 Johnson, m = 3 is tau_3)"""
    lo, hi = rho, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if m * mid - 1 + (1 - mid) ** m > (m - 1) * rho:
            hi = mid
        else:
            lo = mid
    return hi


def h(M, d):
    """(M - 2) C(d, 2) - C(d, 3) for integer d"""
    return (M - 2) * comb(d, 2) - comb(d, 3)


def hhat(M, num, den):
    """piecewise linear interpolation of h(M, .) at the rational point num/den, as a Fraction"""
    d0 = num // den
    fr = Fr(num, den) - d0
    if fr == 0:
        return Fr(h(M, d0))
    return h(M, d0) + fr * (h(M, d0 + 1) - h(M, d0))


def feasible(M, ne, a, c):
    """can M sets of size a in ne points satisfy sum over triples of (p_ij + p_il + p_jl - t_ijl) <= C(M,3) c ?
    necessary condition: ne * hhat(M a / ne) <= C(M, 3) c"""
    return ne * hhat(M, M * a, ne) <= comb(M, 3) * c


def fmax(ne, a, c, cap=10 ** 7):
    """largest M >= 2 passing the necessary condition (None if unbounded up to cap)"""
    # closed form upper bound, then exact scan downwards
    al, rh = Fr(a, ne), Fr(c, 2 * ne)
    A = al * al * (3 - al) - 2 * rh
    if A <= 0:
        return None
    B = 3 * (al + al * al - 2 * rh)
    top = max(int(B / A) + 2, int(1 / (1 - al)) + 2, 3)
    if top > cap:
        return None
    M = top
    while M > 2 and not feasible(M, ne, a, c):
        M -= 1
    return M


def class_f(n, k, T, U):
    """bound for primitive lists of the problems of the class C of section 5.3 at the levels with |U| <= U.
    By Lemma 5.4 (2) the worst problem is the ordinary one (a = T, K = k - 1, ne = n) with c = 2(k - 1) + U."""
    return fmax(n, T, 2 * (k - 1) + U)


def class_scan(n, k, T, U, steps=400):
    """numerical confirmation of Lemma 5.4 (2): fmax along the extreme line a - K = Delta, ne - a = n - T"""
    Delta, t0 = T - k + 1, n - T
    best = 2
    for s in range(steps + 1):
        a = T - (T - Delta - 1) * s // steps
        if a <= Delta:
            continue
        f = fmax(a + t0, a, 2 * (a - Delta) + U)
        if f is None:
            return None
        best = max(best, f)
    return best


def list_bound(N, R, tau):
    """log2 of the bound of Theorem 5.5, minimized over j0; returns (log2 bound, j0, f, kappa0)"""
    n = 1 << N
    k = n >> R
    T = int(tau * n) + 1
    Delta = T - k + 1
    best = None
    for j0 in range(1, N):
        U = 1 << (j0 - 1)  # largest |U| at the levels j < j0
        f = class_f(n, k, T, U)
        if f is None:
            continue
        kappa0 = (k - 1) >> j0
        G = comb(f + 1, 3)
        # (n / Delta)^(kappa0 + 1) + 1 <= 2 (n / Delta)^(kappa0 + 1)
        lg = j0 * log2(G) + N * j0 - j0 * (j0 - 1) / 2 + (kappa0 + 1) * log2(n / Delta) + 1
        if best is None or lg < best[0]:
            best = (lg, j0, f, kappa0)
    return best


def tables():
    print("thresholds tau_3(rho): tau^2 (3 - tau) = 2 rho")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        t3 = tau3(rho)
        print(f"  rho = 1/{1 << R}: tau_3 = {t3:.5f}, Johnson {rho ** 0.5:.5f}, (1 + 2 rho)/3 = {(1 + 2 * rho) / 3:.5f}")
    print("\nthresholds of the m-wise count (outlook, section 5.6): m = 2, 3, 4, 5, 6, 8")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        print(f"  rho = 1/{1 << R}: " + ", ".join(f"{tau_m(rho, m):.4f}" for m in (2, 3, 4, 5, 6, 8)))
    print("\nprimitive lists at level 0 (c = 2k - 1), n = 2^25: f(rho, tau)")
    N = 25
    n = 1 << N
    for R, taus in ((1, (0.654, 0.655, 0.66, 0.665)), (2, (0.444, 0.45, 0.46, 0.48, 0.499)), (3, (0.306, 0.31, 0.32, 0.34, 0.353)), (4, (0.213, 0.216, 0.22, 0.23, 0.249))):
        k = n >> R
        row = []
        for tau in taus:
            T = int(tau * n) + 1
            row.append(f"{tau}: {fmax(n, T, 2 * k - 1)}")
        print(f"  rho = 1/{1 << R}: " + ", ".join(row))
    print("\nlist bound through the descent (Theorem 5.5), log2, minimized over j0: (log2, j0, f, kappa0)")
    for N in (25, 28):
        for R, taus in ((1, (0.655, 0.66, 0.665)), (2, (0.45, 0.46, 0.48)), (3, (0.31, 0.32, 0.34)), (4, (0.216, 0.22, 0.23))):
            for tau in taus:
                b = list_bound(N, R, tau)
                if b is None:
                    print(f"  N = {N}, rho = 1/{1 << R}, tau = {tau}: no admissible j0")
                else:
                    print(f"  N = {N}, rho = 1/{1 << R}, tau = {tau}: 2^{b[0]:.0f}, j0 = {b[1]}, f = {b[2]}, kappa0 = {b[3]}")


def checks():
    # 1. second differences of h are M - 1 - d >= 0 for d <= M - 1
    for M in range(3, 60):
        for d in range(1, M):
            assert h(M, d + 1) - 2 * h(M, d) + h(M, d - 1) == M - 1 - d
    # 2. the Jensen step on random degree sequences, and the triple identity on random set systems
    import random
    rnd = random.Random(1)
    for _ in range(300):
        n, M = rnd.randint(6, 14), rnd.randint(3, 8)
        sets = [frozenset(rnd.sample(range(n), rnd.randint(2, n - 1))) for _ in range(M)]
        deg = [sum(x in s for s in sets) for x in range(n)]
        lhs = 0
        for i in range(M):
            for j in range(i + 1, M):
                for l in range(j + 1, M):
                    a, b, c = sets[i], sets[j], sets[l]
                    lhs += len(a & b) + len(a & c) + len(b & c) - len(a & b & c)
        assert lhs == sum(h(M, d) for d in deg)
        tot = sum(deg)
        assert sum(h(M, d) for d in deg) >= n * hhat(M, tot, n)
    # 3. worst case of the class is the top problem (a = T, ne = n, K = k - 1): fmax non-increasing along the scan,
    #    and non-decreasing in K and in ne at fixed a
    for (N, R, tau) in ((12, 1, 0.66), (12, 2, 0.46), (12, 3, 0.32), (12, 4, 0.22), (14, 1, 0.657), (14, 2, 0.45)):
        n = 1 << N
        k = n >> R
        T = int(tau * n) + 1
        Delta, t0 = T - k + 1, n - T
        for U in (1, 4, 16):
            top = fmax(n, T, 2 * (k - 1) + U)
            for _ in range(400):
                a = rnd.randint(Delta + 1, T)
                K = rnd.randint(0, a - Delta)
                ne = rnd.randint(a + 1, a + t0)
                f = fmax(ne, a, 2 * K + U)
                assert f is not None and f <= top, (N, R, tau, U, a, K, ne, f, top)
    # 4. the same on the extreme line at the sizes of the tables
    for (N, R, tau) in ((25, 1, 0.66), (25, 2, 0.46), (25, 3, 0.32), (25, 4, 0.22), (28, 1, 0.655), (28, 4, 0.216)):
        n = 1 << N
        k = n >> R
        T = int(tau * n) + 1
        for U in (1, 1 << 17, 1 << 19):
            assert class_scan(n, k, T, U) == class_f(n, k, T, U), (N, R, tau, U)
    print("checks passed")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "check":
        checks()
    else:
        tables()
