#!/usr/bin/env python3
# Researcher 27. The conditional list bound of note 27, Theorem 6.3, as numbers.
#   python3 27_bounds.py
# Hypothesis H_{L+1}(C): any L + 1 members of a list with forced excess e = (L+1) T - n - L k + 1 >= 1 contain an
# affine relation (a triple function or an opposite ratio with a period group of size >= (e + L - 1) / C).
# Then |list| <= 3 + (L+1) L (L-1)^2 / 2 * Nsub * A, with pi the least power of two >= (e + L - 1) / C,
# Nsub the number of subspaces of size pi, dstar = floor((k - 1) / pi), A = prod_{i <= dstar + 1} (n-k+i)/(T-k+i).
from math import log2, ceil
from fractions import Fraction

def lgauss(N, c):  # log2 of the number of subspaces of codimension c in F_2^N
    return sum(log2((1 << (N - i)) - 1) - log2((1 << (c - i)) - 1) for i in range(c))

def bound(N, R, T, L, C):
    n = 1 << N; k = n >> R
    e = (L + 1) * T - n - L * k + 1
    if e < 1: return None
    need = Fraction(e + L - 1, C)
    pi = 1
    while pi < need: pi *= 2
    if pi > n: return None
    c = N - (pi.bit_length() - 1)
    dstar = (k - 1) // pi
    if dstar > 5000: return e, c, dstar, float('inf')
    lA = sum(log2(n - k + i) - log2(T - k + i) for i in range(1, dstar + 2))
    return e, c, dstar, log2((L + 1) * L * (L - 1) ** 2 / 2) + lgauss(N, c) + lA

def window(R, L):  # (lower, upper] in tau where L + 1 members are the first forced excess
    rho = Fraction(1, 1 << R)
    return (1 + L * rho) / (L + 1), (1 + (L - 1) * rho) / L

print("Four members (L = 3), rate 1/2. Columns: tau, then for each N: c = log2(n/pi), dstar, log2(bound)")
for C in (2, 4):
    print("  C = %d" % C)
    for tau in (0.6260, 0.6300, 0.6350, 0.6407, 0.6450, 0.6500, 0.6563, 0.6600, 0.6650, 0.6667):
        row = "    tau=%.4f" % tau
        for N in (25, 26, 27, 28):
            b = bound(N, 1, ceil(tau * (1 << N)), 3, C)
            row += "  N=%d: " % N + ("n/a" if b is None else "c=%d d*=%d 2^%.1f" % (b[1], b[2], b[3]))
        print(row)
print()
print("Four members, rate 1/4 (the four-member range is (7/16, 1/2])")
for C in (2, 4):
    print("  C = %d" % C)
    for tau in (0.4400, 0.4500, 0.4600, 0.4700, 0.4800, 0.4900, 0.4990):
        row = "    tau=%.4f" % tau
        for N in (25, 28):
            b = bound(N, 2, ceil(tau * (1 << N)), 3, C)
            row += "  N=%d: " % N + ("n/a" if b is None else "c=%d d*=%d 2^%.1f" % (b[1], b[2], b[3]))
        print(row)
print()
print("Extrapolation to L + 1 members (hypothesis H_{L+1}(C) with C = L - 1, the value for pure periods): top and middle of the part of each range inside the open window, N = 25 and 28")
WIN = {1: (0.5, 0.5 ** 0.5), 2: (0.375, 0.5), 3: (0.25, 0.125 ** 0.5), 4: (0.125, 0.25)}
for R, name in ((1, "1/2"), (2, "1/4"), (3, "1/8"), (4, "1/16")):
    for L in range(3, 17):
        lo, hi = window(R, L)
        bot = max(float(lo), WIN[R][0]); top = min(float(hi), WIN[R][1])
        if top <= bot + 1e-9: continue
        row = "  rate %s, %d members, tau in (%.4f, %.4f]:" % (name, L + 1, bot, top)
        for N in (25, 28):
            n = 1 << N
            b = bound(N, R, int(top * n), L, max(L - 1, 1))
            mid = bound(N, R, ceil((bot + top) / 2 * n), L, max(L - 1, 1))
            row += "  N=%d top: " % N + ("n/a" if b is None else "c=%d d*=%d 2^%.1f" % (b[1], b[2], b[3])) + ", middle: " + ("n/a" if mid is None else "c=%d 2^%.1f" % (mid[1], mid[3]))
        print(row)
