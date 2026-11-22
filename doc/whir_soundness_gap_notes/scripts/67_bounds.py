#!/usr/bin/env python3
"""Note 67, section 1: at every level of the deployed shapes, the smallest agreement threshold A^(i,0) with a proven
list bound that s out-of-domain points (one batch, grinds 15 and 7) pay for, and the queries it gives.

The proven bounds are those of `67_model.best_list`: unique decoding, Johnson, and the shortened Johnson bound
(counting on j fixed columns, then Johnson), whose case j = d is the counting bound. The threshold is found by
bisection, which assumes that the least affordable threshold is where affordability changes (the bounds decrease
in the agreement up to their floors); every reported threshold is rechecked exactly.

Usage: python3 67_bounds.py [mu ...]
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from math import isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("m67", os.path.join(HERE, "67_model.py"))
m = importlib.util.module_from_spec(spec)
sys.modules["m67"] = m
spec.loader.exec_module(m)

BUDGETS = (8, 10, 12, 16, 24, 32, 48, 64, 96, 128)


def affordable(n, a0, d, ell, s):
    """Does a proven list bound at agreement a0 fit the row M0 with s points in one batch?"""
    bits_per_point = 128 - math.log2(d + (1 << ell) - 1)
    if a0 * a0 <= n * d and 2.9 * m.list_bits_estimate(n, a0, d) > (s + 1) * bits_per_point:
        return None
    big_l, src = m.best_list(n, a0, d)
    return (big_l, src) if m.m0_ok(big_l, d, ell, (s,) * ell, 15, 7) else None


def least_threshold(n, d, ell, s):
    """The least a0 >= d + 2 affordable with s points, or None when not even unique decoding is."""
    hi = (n + d) // 2 + 1  # unique decoding
    if hi > n or affordable(n, hi, d, ell, s) is None:
        return None
    lo = d + 2
    while lo < hi:
        mid = (lo + hi) // 2
        if affordable(n, mid, d, ell, s) is not None:
            hi = mid
        else:
            lo = mid + 1
    return lo


def main():
    mus = [int(x) for x in sys.argv[1:]] or [24, 26, 28, 30]
    print("columns: level, (kappa, ell), log2 n, d + 1; Johnson: least points, queries; then for each point budget s: queries,")
    print("log2(n / A0) of the least proven threshold, and the bound used (J Johnson, S shortened Johnson, C counting, U unique)")
    for rate in (1, 2, 3, 4):
        for mu in mus:
            shp = m.deployed_shape(mu, rate)
            print(f"\nrate 1/{1 << rate}, mu = {mu}")
            for i, (r, c, k) in enumerate(shp):
                final = i == len(shp) - 1
                n, d = 1 << (c + r), (1 << c) - 1 + k
                base = m.johnson_level(min(i, 1), r, c, k, 17, final, sched="batch")
                cells = []
                for s in BUDGETS:
                    a0 = least_threshold(n, d, k, s)
                    if a0 is None:
                        cells.append(f"s={s}: none")
                        continue
                    big_l, src = affordable(n, a0, d, k, s)
                    t = m.query_count(c + r, a0 + k, s, 17, final)
                    tag = {"J": "J", "u": "U", "c": "C", "s": "S"}[src[0]]
                    cells.append(f"s={s}: {t} q, {math.log2(n / a0):.3f} {tag}")
                jr = math.log2(n / (isqrt(n * d) + 1))
                print(f"  L{i} ({c},{k}) n=2^{c + r} d+1={d + 1} capacity {math.log2(n / (d + 1)):.2f} Johnson {jr:.3f}: {base.points} pts, {base.queries} q | " + "; ".join(cells))


if __name__ == "__main__":
    main()
