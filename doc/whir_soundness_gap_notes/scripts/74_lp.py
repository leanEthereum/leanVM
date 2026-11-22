#!/usr/bin/env python3
"""Note 74, Section 4: the linear program behind the weight bound for L+1 members (leading term in k).
Variables x_c = number of leaves with a class of size c (c = 2..L+1), in units of k. Constraints, one for each size j+1 of a
sub-list T (Corollary 4.3 applied to T, averaged over T): sum_c p(c, j+1) x_c <= j, p = probability that a random
(j+1)-subset meets a fixed c-subset of the L+1 members in at least two points. Objective: sum_c (c-1) x_c.
Exact rational arithmetic, vertex enumeration."""
from fractions import Fraction as Fr
from itertools import combinations
from math import comb
def solve(A, b):
    n = len(A); M = [row[:] + [bi] for row, bi in zip(A, b)]
    for c in range(n):
        p = next((i for i in range(c, n) if M[i][c] != 0), None)
        if p is None: return None
        M[c], M[p] = M[p], M[c]
        M[c] = [x / M[c][c] for x in M[c]]
        for i in range(n):
            if i != c and M[i][c] != 0: M[i] = [x - M[i][c] * y for x, y in zip(M[i], M[c])]
    return [M[i][n] for i in range(n)]
print("members  LP bound/k   lift value (3L-1)/2   generalized Singleton L")
for L in range(2, 9):
    sizes = list(range(2, L + 2)); nv = len(sizes)
    cons = []
    for j in range(1, L + 1):
        row = [Fr(1) - Fr(comb(L - j, c) + (j + 1) * comb(L - j, c - 1), comb(L + 1, c)) for c in sizes]
        cons.append((row, Fr(j)))
    for i in range(nv): cons.append(([Fr(-1) if t == i else Fr(0) for t in range(nv)], Fr(0)))
    obj = [Fr(c - 1) for c in sizes]; best = None
    for sub in combinations(range(len(cons)), nv):
        x = solve([cons[i][0] for i in sub], [cons[i][1] for i in sub])
        if x is None: continue
        if all(sum(a * xi for a, xi in zip(row, x)) <= rhs for row, rhs in cons):
            val = sum(o * xi for o, xi in zip(obj, x))
            if best is None or val > best[0]: best = (val, x)
    print(f"{L + 1:7d}  {str(best[0]):>9} = {float(best[0]):.4f}   {(3 * L - 1) / 2:.1f}   {L}   x = {[str(t) for t in best[1]]}")
