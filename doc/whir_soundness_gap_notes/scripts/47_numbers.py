#!/usr/bin/env python3
"""Note 47: the bounds of Theorem R (note 46) with exact rationals, for comparison with the
numerals checked in lean_descent/PeriodDescent/Numbers.lean.

N = 25, k = 2^24, T = ceil(0.64 n), Delta = T - k + 1. For each stopping level j0 and each f:
log2 of G^j0 * 2^(N j0 - j0 (j0 - 1) / 2) * (B_j0 + 1), with G = C(f + 1, 3) (the notes) and
G = C(f, 2) (the constant of `one_step`), and the smallest e with bound <= 2^e.
No dependencies. Usage: python3 47_numbers.py
"""
from fractions import Fraction
from math import comb, log2

N = 25
n = 2 ** N
k = 2 ** 24
T = -((-64 * n) // 100)
Delta = T - k + 1


def base(j0):
    """B_j0 = max over kappa of prod_{i <= kappa} (n - m i) / (Delta + m (kappa - i))."""
    m = 2 ** j0
    best = (Fraction(-1), -1)
    for kappa in range((k - 1) // m + 1):
        p = Fraction(1)
        for i in range(kappa + 1):
            p *= Fraction(n - m * i, Delta + m * (kappa - i))
        best = max(best, (p, kappa))
    return best


def ceil_log2(x):
    """The smallest integer e with x <= 2^e, for a positive rational x."""
    e = 0
    while Fraction(2) ** e < x:
        e += 1
    return e


def main():
    print(f"N = {N}, k = 2^24, T = {T}, Delta = {Delta}")
    for j0 in range(24, 15, -1):
        B, kappa = base(j0)
        e = N * j0 - j0 * (j0 - 1) // 2
        print(f"j0 = {j0}: exponent of two {e}, degree bound {(k - 1) // 2 ** j0}, "
              f"B = {float(B):.6g} (floor {B.numerator // B.denominator}), attained at degree {kappa}")
        for f in (7, 16, 133, 134):
            notes = comb(f + 1, 3) ** j0 * 2 ** e * (B + 1)
            sharp = comb(f, 2) ** j0 * 2 ** e * (B + 1)
            print(f"  f = {f:4d}: C(f+1,3) = {comb(f + 1, 3):6d}: 2^{log2(notes):.2f} <= 2^{ceil_log2(notes)}"
                  f"   C(f,2) = {comb(f, 2):5d}: 2^{log2(sharp):.2f} <= 2^{ceil_log2(sharp)}")


if __name__ == "__main__":
    main()
