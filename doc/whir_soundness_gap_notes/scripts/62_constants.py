#!/usr/bin/env python3
"""Note 62: explicit constants. q = 2^64 unless LOGQ is given.

pairs      : e_2 of Theorem A, crude (any window system) and under (W2) with gamma <= 1/2.
triples    : eps_3 of Theorem H_3 (sections 5 to 7), thresholds, queries, list constants.
Usage: python3 62_constants.py pairs | triples
"""
import math, sys

LG = math.lgamma
LN2 = math.log(2.0)
LOGQ = 64


def lbinom(n, k):
    if k < 0 or k > n:
        return -math.inf
    return (LG(n + 1) - LG(k + 1) - LG(n - k + 1)) / LN2


def log2_sum_binom(a, j):
    """log2 of sum_{i<=j} C(a,i), upper bound: exact max term times count, or a bits."""
    if j >= a:
        return float(a)
    if j >= a // 2:
        return float(a)
    return lbinom(a, j) + math.log2(j + 1)


def e2_crude(n, k):
    e = 0
    while True:
        a = k + e
        if a > n:
            return None
        if LOGQ * (e + 1) >= 130 + lbinom(n, a) + log2_sum_binom(a, k - 1):
            return e
        e += max(1, int((130 + lbinom(n, a) + log2_sum_binom(a, k - 1) - LOGQ * (e + 1)) / (2 * LOGQ)))


def e2_expanding(n, k, a0):
    e = 0
    while True:
        a = k + e
        if a > n:
            return None
        extra = math.log2(4 * a0 + 1) + lbinom(a, 4 * a0) if a0 > 0 else 0.0
        extra = math.log2(2.0 ** min(extra, 1000) + 2) if extra < 1000 else extra + 1e-9
        need = 130 + lbinom(n, a) + extra
        if LOGQ * (e + 1) >= need:
            return e
        e += max(1, int((need - LOGQ * (e + 1)) / (2 * LOGQ)))


def H2(x):
    return 0.0 if x <= 0 or x >= 1 else -(x * math.log2(x) + (1 - x) * math.log2(1 - x))


def pairs():
    print("pairs: e_2 / n. columns: rate, crude (any window), (W2) a0=0, (W2) a0=16, limit H(rho)/64")
    for N in [10, 12, 16, 20, 24, 25, 26, 27, 28]:
        n = 2 ** N
        for r in [2, 4, 8, 16]:
            k = n // r
            c = e2_crude(n, k)
            x0 = e2_expanding(n, k, 0)
            x16 = e2_expanding(n, k, 16)
            print("N=%2d rate 1/%-2d  crude %8d (%.5f)   W2,a0=0 %8d (%.5f)   W2,a0=16 %8d (%.5f)   H/64=%.5f"
                  % (N, r, c, c / n, x0, x0 / n, x16, x16 / n, H2(1 / r) / 64))


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "pairs"
    if mode == "pairs":
        pairs()
    else:
        import importlib.util, os
        spec = importlib.util.spec_from_file_location("t62", os.path.join(os.path.dirname(os.path.abspath(__file__)), "62_triples.py"))
        m = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(m)
        m.main()
