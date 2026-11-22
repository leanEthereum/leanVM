"""Where the interpolation inequality (4.5) of CWYZ26 Lemma 4.2 stops having a solution (researcher 08).

For a level's (n, d): the least agreement A at which some (m, D) with m <= 2^16 satisfies the inequality, against the
Johnson radius sqrt(n d). The gap is a finite-size loss of the bound: it does not depend on any grind.
"""

import math
import os
import sys
from math import isqrt

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import whir_model as wm


def least_agreement(n, d):
    lo, hi = isqrt(n * d) + 1, n
    while lo < hi:
        mid = (lo + hi) // 2
        if wm.interpolation(n, d, mid) is not None:
            hi = mid
        else:
            lo = mid + 1
    return hi


if __name__ == "__main__":
    print("kappa R k | n d | Johnson | least A with (4.5) solvable | gap points | gap/n | gap/sqrt(A) | gap/(A/d)")
    for kappa, rate, k in [(10, 1, 6), (12, 1, 6), (14, 1, 6), (16, 1, 6), (18, 1, 6), (20, 1, 6), (24, 1, 6), (24, 2, 6), (24, 4, 6), (14, 4, 4), (10, 7, 4), (6, 10, 4), (2, 13, 4), (4, 16, 4), (8, 13, 4), (2, 10, 4)]:
        n, d = 1 << (kappa + rate), (1 << kappa) - 1 + k
        a = least_agreement(n, d)
        j = math.sqrt(n * d)
        gap = a - j
        print(f"{kappa:2d} {rate:2d} {k} | 2^{kappa + rate} {d} | {j:.1f} | {a} | {gap:.1f} | {gap / n:.2e} | {gap / math.sqrt(a):.2f} | {gap / (a / d):.2f}")
