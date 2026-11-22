#!/usr/bin/env python3
"""Note 36, section 2: the theorems of the literature with their PRINTED constants, at leanVM's sizes.

For each theorem: the smallest relative agreement tau = 1 - radius it gives for a Reed-Solomon code with
k = 2^24, n = k / rho, points sampled from a field of 2^64 or 2^128 elements, against Johnson sqrt(rho).
Statements as read in the sources (note 36 section 1). Usage: python3 36_literature.py
"""
import math


def H2(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def agglz_printed(rho, n, k, lq):
    """AGGLZ Theorem 1.1: q >= n + k 2^(10 L / eps), radius L/(L+1) (1 - rho - eps), L >= 2."""
    best = None
    for L in range(2, 200):
        eps = 10 * L / math.log2((2.0 ** lq - n) / k)
        if eps >= 1 - rho:
            continue
        tau = (1 + L * (rho + eps)) / (L + 1)
        if best is None or tau < best[0]:
            best = (tau, L, eps)
    return best


def agglz_proof(rho, n, k, lq):
    """AGGLZ inequality (3.7) itself, r = floor(eps n / 2), target 2^-100:
    (L+2) n + log2 C(n,r) + (L+1) r + r log2(L k / (q - n)) <= -100."""
    best = None
    for L in range(2, 200):
        lo, hi = 0.0, 1 - rho
        ok = lambda eps: (L + 2) + H2(eps / 2) + (eps / 2) * (L + 1 + math.log2(L * k) - lq) <= -101.0 / n
        if not ok(hi):
            continue
        for _ in range(60):
            mid = (lo + hi) / 2
            if ok(mid):
                hi = mid
            else:
                lo = mid
        tau = (1 + L * (rho + hi)) / (L + 1)
        if best is None or tau < best[0]:
            best = (tau, L, hi)
    return best


def gz_printed(rho, n, k, lq):
    """Guo-Zhang Theorem 4.7: q >= 2^(L (L + c) / eps) L n (k - 1) + n, failure 2^-((c-2) n), c -> 2."""
    best = None
    room = lq - math.log2(n) - math.log2(k)
    for L in range(1, 200):
        if room - math.log2(L) <= 0:
            break
        eps = L * (L + 2) / (room - math.log2(L))
        if eps >= 1 - rho:
            continue
        tau = (1 + L * (rho + eps)) / (L + 1)
        if best is None or tau < best[0]:
            best = (tau, L, eps)
    return best


def lms_printed(rho, n, k, lq):
    """Levi-Mosheiff-Shagrithaya Corollary 3.12: q >= 2^(2 (L+1) (L+1+eta) / eps) k (4 (L+1))^(4 (L+1)) / eps, eta n = 100."""
    best = None
    for L in range(1, 60):
        b = L + 1
        fixed = math.log2(k) + 4 * b * math.log2(4 * b)
        lo, hi = 1e-6, 1 - rho
        ok = lambda eps: 2 * b * (b + 100.0 / n) / eps + fixed + math.log2(1 / eps) <= lq
        if not ok(hi):
            continue
        for _ in range(60):
            mid = (lo + hi) / 2
            if ok(mid):
                hi = mid
            else:
                lo = mid
        tau = (1 + L * (rho + hi)) / (L + 1)
        if best is None or tau < best[0]:
            best = (tau, L, hi)
    return best


def fks_printed(rho, lq):
    """Ferber-Kwan-Sauermann Theorem 3 with h = k - 1: agreement 3 c h / n for c >= 5,
    valid only if n <= sqrt(log2(q) c / 8) h, i.e. 1/rho <= sqrt(lq c / 8)."""
    best = None
    c = 5.0
    while c < 1e9:
        if 1 / rho <= math.sqrt(lq * c / 8):
            tau = 3 * c * rho
            if tau < 1 and (best is None or tau < best[0]):
                best = (tau, c)
            break
        c *= 1.01
    return best


def rw(lq, C0=1.0):
    """Rudra-Wootters Corollary 2: n >= 2 C0 log2(N) log2(L)^5 / eps, N = q^k, L = 1/eps, agreement 5 eps.
    Largest eps (hence rate) at which 5 eps < sqrt(rate) is possible at all."""
    # need rate <= eps / (2 C0 lq log2(1/eps)^5) and (5 eps)^2 < rate
    e = 0.5
    while e > 1e-40:
        rate_max = e / (2 * C0 * lq * math.log2(1 / e) ** 5)
        if 25 * e * e < rate_max:
            return e, rate_max
        e /= 1.05
    return None


def main():
    k = 2 ** 24
    print("smallest agreement tau given by the printed statements (None: no admissible parameter)")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        n = k * 2 ** R
        print(f"\nrate 2^-{R}, Johnson {math.sqrt(rho):.4f}")
        for lq in (64, 128):
            a = agglz_printed(rho, n, k, lq)
            b = agglz_proof(rho, n, k, lq)
            g = gz_printed(rho, n, k, lq)
            l = lms_printed(rho, n, k, lq)
            f = fks_printed(rho, lq)
            show = lambda x: "None" if x is None else f"{x[0]:.4f} (L or c = {x[1]:.3g})"
            print(f"  field 2^{lq}: AGGLZ Thm 1.1 {show(a)} | AGGLZ ineq. (3.7) {show(b)} | GZ Thm 4.7 {show(g)} | LMS Cor 3.12 {show(l)} | FKS Thm 3 {show(f)}")
    print("\nRudra-Wootters Corollary 2 (absolute constant C0 unspecified in the paper; C0 = 1 is the most favourable reading):")
    for lq in (64, 128):
        e, r = rw(lq)
        print(f"  field 2^{lq}: 5 eps < sqrt(rate) needs eps <= 2^{math.log2(e):.1f}, rate <= 2^{math.log2(r):.1f}")
    print("\nFerber-Kwan-Sauermann Theorem 3 below Johnson: needs 3 c rho < sqrt(rho) and 1/rho <= sqrt(log2(q) c / 8), c >= 5,")
    print("  i.e. log2 q >= 8 / (c rho^2) with rho < 1 / (9 c^2): log2 q >= 648 c^3 >= 81000")


if __name__ == "__main__":
    main()
