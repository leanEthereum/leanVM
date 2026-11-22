#!/usr/bin/env python3
"""Note 84, Section 6: log2 of the number of candidate circuits for Top_{Delta_t}(0) on T_J.
A dependent genuine system contains a circuit with at most L k_J rows, one direction per node;
count = binom(n_J, L k_J) * |Delta|^(L k_J) / t!  (labelings of the t members identified)."""
import math
for r in (3, 4, 7, 10):
    for J in (1, 2, 3, 4):
        nJ, kJ = 2 ** (J + r), 2 ** J
        row = []
        for t in (2, 3, 4, 5, 6, 8):
            L, nd = t - 1, t * (t - 1) // 2
            m = L * kJ
            if m > nJ:
                row.append(f"t={t}: -")
                continue
            lg = (math.lgamma(nJ + 1) - math.lgamma(m + 1) - math.lgamma(nJ - m + 1)) / math.log(2) + m * math.log2(nd) - math.log2(math.factorial(t))
            row.append(f"t={t}: {lg:6.1f}")
        print(f"r={r:2d} J={J} n_J={nJ:5d} k_J={kJ:2d}  " + "  ".join(row))
