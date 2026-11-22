#!/usr/bin/env python3
"""54_single_cell.py: the non-degenerate quintics of Theorem 2.1 of note 51 are cut for EVERY profile by one pair (m, B)
and the bound (T) alone: the six integer inequalities at the vertices of the simplex (contact 2j on all lines, j = 0..5).

By Lemma 2.0 of note 51 (convexity) this proves that every absolutely irreducible first integral dE with b = 1, K = 2,
D_c <= 5, det E != 0 and W <= W_max is cut by Lemma C of note 35 with this pair.  Exact integers, defining sums only
(no closed form): 3 * [N(B, mA) - N(B - 1, mA - W_j)] > 3 * n * psi(j), where 3 W_j = 8 Delta + 1 + 2 n (3j - 4)_+ ."""
from fractions import Fraction
from importlib import import_module

C = import_module("54_cover")

for a, (m, B) in (("0.7065", (60, 18)), ("0.705", (60, 17))):
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        D = n // 2 + 5
        fa = Fraction(a)
        A = -((-fa.numerator * n) // fa.denominator)
        rows, Wmax, d0, thr, delta, chain = C.certificates(n, D, A, C.CERTS[a])
        assert D * (m + B) <= m * A - Wmax, "side condition of Lemma C"
        margins = []
        for j in range(6):
            num = 8 * D + 1 + (2 * n * (3 * j - 4) if j >= 2 else 0)        # 3 * (lower bound on W)
            psi = C.R(m, B) - C.R(m - 2 * j, B - 1)
            lhs = 3 * C.N_sum(B, m * A, D) - C.N_sum(B - 1, 3 * m * A - num, 3 * D)   # 3 * Phi(W_j)
            rhs = 3 * n * psi
            assert lhs > rhs
            margins.append((lhs - rhs) / (3 * n))
        print("a = %s, n = 2^%d, (m, B) = (%d, %d), bound (T): side condition holds at W_max = %d; margins (Phi - n psi(j)) / n for j = 0..5: %s"
              % (a, lg, m, B, Wmax, ", ".join("%.1f" % x for x in margins)))
