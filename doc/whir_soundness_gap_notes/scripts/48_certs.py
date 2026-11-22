#!/usr/bin/env python3
"""Note 48, part 1: certificates (m, B) with small Y1-degree B. Exact integers.

A certificate for (n, Delta, A) is a pair (m, B) with N(B, mA) > n R(m, B) (notes 35 and 41).
  A  closed forms of N(B, Z) and R(m, B) for small B, checked against the sums of 41_counts.py
  B  B = 1: N(1, Z) = Z^2/Delta + r(Delta - r)/Delta, R(m, 1) = m^2 + 1; no certificate with A^2 <= n Delta (brute check)
  C  thresholds: for each B, the smallest A (over all m) with a certificate, n = 2^25..2^28, Delta = n/2 + 5
  D  explicit certificates at chosen agreements, with B_jet and the margin N - nR
  E  the asymptotic threshold (n -> infinity, Delta = n/2) per B
Run: python3 48_certs.py [A] [B] [C] [D] [E]
"""
import sys
import importlib.util
import os
from fractions import Fraction
from math import ceil, sqrt, log2, isqrt

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("c41", os.path.join(here, "41_counts.py"))
c41 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c41)
R, N, R_sum, N_loop = c41.R, c41.N, c41.R_sum, c41.N_loop


def R_closed(m, B):
    """R(m, B) = (B+1)[m(m+1)/2 - mB/2 + B(2B+1)/6] for m >= 2B - 1 (note 48, Lemma 1.1)."""
    assert m >= 2 * B - 1
    return Fraction(B + 1) * (Fraction(m * (m + 1), 2) - Fraction(m * B, 2) + Fraction(B * (2 * B + 1), 6))


def N_closed(B, Z, D):
    """N(B, Z) = (B+1) S(Z) - Z B(B+1)/2 + Delta (B-1)B(B+1)/6 for Z >= (B-1) Delta, S(Z) = sum_t (Z - Delta t)_+."""
    assert Z >= (B - 1) * D
    q, r = divmod(Z, D)
    S = (q + 1) * Z - D * q * (q + 1) // 2
    return (B + 1) * S - Z * B * (B + 1) // 2 + D * (B - 1) * B * (B + 1) // 6


def part_A():
    print("A. closed forms against the defining sums")
    bad = 0
    for B in range(0, 8):
        for m in range(max(1, 2 * B - 1), 60):
            if R_closed(m, B) != R_sum(m, B) or R(m, B) != R_sum(m, B):
                bad += 1
    for D in (7, 16, 21):
        for B in range(0, 6):
            for Z in range(max(1, (B - 1) * D), 40 * D):
                if N_closed(B, Z, D) != N_loop(B, Z, D) or N(B, Z, D) != N_loop(B, Z, D):
                    bad += 1
    print(f"   mismatches: {bad}")
    print(f"   R(m, 1) = m^2 + 1: {all(R_sum(m, 1) == m * m + 1 for m in range(1, 200))}")
    print(f"   R(m, 2) = (3m^2 - 3m + 10)/2 for m >= 3: {all(2 * R_sum(m, 2) == 3 * m * m - 3 * m + 10 for m in range(3, 200))}")
    print(f"   R(m, 3) = 2m^2 - 4m + 14 for m >= 5: {all(R_sum(m, 3) == 2 * m * m - 4 * m + 14 for m in range(5, 200))}")
    print(f"   R(18, 5) = {R(18, 5)}")


def part_B():
    print("B. B = 1: N(1, Z) Delta = Z^2 + r (Delta - r), r = Z mod Delta; so N(1, mA) <= m^2 A^2/Delta + Delta/4")
    ok = True
    for D in (5, 8, 13, 64):
        for Z in range(1, 30 * D):
            r = Z % D
            if N_loop(1, Z, D) * D != Z * Z + r * (D - r):
                ok = False
    print(f"   identity checked on small cases: {ok}")
    print("   brute check that no certificate (m, 1) exists at or below the Johnson radius, small n, every Delta <= n, the four largest A with A^2 <= n Delta, m <= 60:")
    viol = 0
    for n in (16, 32, 64):
        for D in range(1, n):
            Amax = isqrt(n * D)
            for A in range(max(1, Amax - 3), Amax + 1):
                for m in range(1, 61):
                    if N(1, m * A, D) > n * R(m, 1):
                        viol += 1
    print(f"   violations: {viol}")
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        D = n // 2 + 5
        AJ = isqrt(n * D)            # largest A with A^2 <= n Delta
        # smallest A with a (m, 1) certificate, m <= 2000
        best = None
        for m in range(1, 2001):
            lo, hi = AJ, n
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if N(1, m * mid, D) > n * R(m, 1):
                    hi = mid
                else:
                    lo = mid
            if best is None or hi < best[0]:
                best = (hi, m)
        print(f"   n = 2^{lg}: floor(sqrt(n Delta)) = {AJ} ({AJ / n:.7f} n); smallest A with a certificate (m, 1), m <= 2000: "
              f"{best[0]} = floor(sqrt(n Delta)) + {best[0] - AJ} (m = {best[1]})")


def min_A(n, D, B, mmax=400):
    """smallest A such that some (m, B), m <= mmax, is a certificate; returns (A, m)."""
    best = None
    for m in range(max(1, B), mmax + 1):
        if not N(B, m * n, D) > n * R(m, B):
            continue
        lo, hi = 0, n
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if N(B, m * mid, D) > n * R(m, B):
                hi = mid
            else:
                lo = mid
        if best is None or hi < best[0]:
            best = (hi, m)
    return best


def part_C():
    print("C. smallest agreement with a certificate (m, B), m <= 400, Delta = n/2 + 5 (exact integers)")
    print("   Johnson: sqrt(n Delta)/n = 0.7071068 (+ 5e-6 for the slack 5)")
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        D = n // 2 + 5
        row = []
        for B in (1, 2, 3, 4, 5, 6, 8, 11):
            A, m = min_A(n, D, B)
            row.append(f"B={B}: {A / n:.6f} (m={m})")
        print(f"   n = 2^{lg}: " + "; ".join(row))
    print("   same, per B, the range of m that gives a certificate at selected agreements (n = 2^25):")
    n = 1 << 25
    D = n // 2 + 5
    for B in (2, 3):
        for a in (0.7040, 0.7045, 0.7046, 0.7047, 0.7050, 0.7055, 0.7060, 0.7065, 0.7070, 0.7015, 0.7018, 0.7020, 0.7030):
            A = ceil(a * n)
            ms = [m for m in range(B, 400) if N(B, m * A, D) > n * R(m, B)]
            if ms:
                print(f"     B = {B}, a = {a}: m in [{ms[0]}, {ms[-1]}] ({len(ms)} values), B_jet at smallest m = {(ms[0] * A - 1) // D}")
            else:
                print(f"     B = {B}, a = {a}: none")


def part_D():
    print("D. explicit certificates, Delta = n/2 + 5, A = ceil(a n)")
    for B, alist in ((2, (0.7050, 0.7055, 0.7060, 0.7065)), (3, (0.7020, 0.7030, 0.7050))):
        for a in alist:
            for lg in (25, 26, 27, 28):
                n = 1 << lg
                D = n // 2 + 5
                A = ceil(a * n)
                ms = [m for m in range(B, 400) if N(B, m * A, D) > n * R(m, B)]
                if not ms:
                    print(f"   B = {B}, a = {a}, n = 2^{lg}: none")
                    continue
                # the m with the largest margin, and the smallest m
                mb = max(ms, key=lambda m: N(B, m * A, D) - n * R(m, B))
                for m in sorted({ms[0], mb}):
                    NN, RR = N(B, m * A, D), R(m, B)
                    print(f"   B = {B}, a = {a}, n = 2^{lg}: A = {A}, (m, B) = ({m}, {B}), N = {NN} > n R = {n * RR} (R = {RR}), "
                          f"margin {NN - n * RR} = {(NN - n * RR) / n:.4f} n, B_jet = {(m * A - 1) // D}, "
                          f"queries {ceil(108 / log2(n / A))}")


def part_E():
    print("E. asymptotic thresholds (n -> infinity, Delta = n/2): certificate (m, B) iff nu(B, m, a) > R(m, B),")
    print("   nu = lim N(B, m a n)/n, evaluated as N(B, m A, D)/n at n = 2^60, Delta = n/2; a^(B) = inf over m of the root")
    n = 1 << 60
    D = n // 2
    for B in (1, 2, 3, 4, 5, 6, 8, 11, 20, 50):
        best = None
        for m in range(max(1, B), 12 * B + 80):
            Rm = R(m, B)
            if not N(B, m * n, D) > n * Rm:
                continue
            lo, hi = n // 2, n
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if N(B, m * mid, D) > n * Rm:
                    hi = mid
                else:
                    lo = mid
            if best is None or hi < best[0]:
                best = (hi, m)
        c = 3 * (B - 1) ** 2 / (4 * B * (1.5 * B + 1.5))
        lo, hi = 0.5, 1.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if 2 * mid * mid + c * (1 - mid) ** 2 > 1:
                hi = mid
            else:
                lo = mid
        a = best[0] / n
        print(f"   B = {B}: a^(B) = {a:.6f} at m = {best[1]}; real-m formula without the fractional term {hi:.6f}; "
              f"queries just above the threshold {ceil(108 / log2(1 / a))}")
    print(f"   Johnson sqrt(1/2) = {sqrt(0.5):.6f} (217 queries), a_1 = 0.689898 (B -> infinity)")


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C", "D", "E"]
    for w in which:
        {"A": part_A, "B": part_B, "C": part_C, "D": part_D, "E": part_E}[w]()
