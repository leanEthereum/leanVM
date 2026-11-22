#!/usr/bin/env python3
"""Note 60, Section 3.1: the sum over nonempty vertex sets T of the N-cube with |N[T]| <= n/2
of q^(-|dT|), q = 2^64.  Proved in the note:
   a_b := #{T : |dT| = b, |N[T]| <= n/2} = 0 for b < N,  a_N = n,  a_b = 0 for N < b < 2N-2,
   a_b <= C(n, b) (2^b - 1) in general,
so  n q^-N <= S <= n q^-N + sum_{b >= 2N-2} C(n,b) 2^b q^-b.
Prints log2 of the main term, log2 of the relative size of the tail, and checks a_b against
the exhaustive counts of 60_small.c for N = 4, 5 (hard-coded from its output)."""
from math import comb, log2, lgamma, log

Q = 64
print("N | log2(n q^-N) | log2(tail / main) <= | log2 of the note's bound sum_b C(n,b) 2^(bN) q^-b (leading term b = N)")
for N in range(10, 29):
    n = 2 ** N
    main = N - Q * N
    b0 = 2 * N - 2
    # tail <= sum_{b>=b0} (2n/q)^b / b! <= (2n/q)^b0 / b0! * 1/(1 - 2n/q)
    tail = b0 * (N + 1 - Q) - lgamma(b0 + 1) / log(2) + 1e-9
    note = N * (2 * N - Q) - lgamma(N + 1) / log(2)
    print(f"{N} | {main} | {tail - main:.1f} | {note:.1f}")
# exhaustive counts (|N[T]| <= n/2) from 60_small.c
ex = {4: {4: 16, 6: 80}, 5: {5: 32, 8: 240, 10: 928, 11: 2112, 12: 3400, 13: 2400}}
for N, d in ex.items():
    n = 2 ** N
    ok = all(b >= N and (b == N or b >= 2 * N - 2) and c <= comb(n, b) * (2 ** b - 1) for b, c in d.items()) and d[N] == n
    print(f"N={N}: exhaustive counts by boundary {d}: consistent with a_N = n, a_b = 0 for N < b < 2N-2, a_b <= C(n,b)(2^b-1): {ok}")
