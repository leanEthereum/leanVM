#!/usr/bin/env python3
"""Note 84, Section 7: the slack eps_3 n of Theorem 5.1 against (a) the lower bound of note 77
Theorem 3.4 (three codewords coincide on 2k + s leaves, s = floor((k - 65)/63), for every MDS code
over GF(2^64): excess over 2k - 1 at least s + 1), and (b) the first-moment value for a uniformly
random code: the largest s with binom(n, 2k+s) 3^(2k+s) q^-(s+1) >= 2^-130."""
import importlib.util, math, os
HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("eps84", os.path.join(HERE, "84_eps.py"))
E = importlib.util.module_from_spec(spec); spec.loader.exec_module(E)

def first_moment(n, k, L, nd, bits=64.0, plog=-130.0):
    s = 0
    f = lambda s: E.log2_binom(n, L * k + s) + (L * k + s) * math.log2(nd) - bits * (s + 1)
    lo, hi = 0, n - L * k
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if f(mid) >= plog: lo = mid
        else: hi = mid
    return lo + 1  # excess over Lk - 1

for r in (3, 4, 7, 10):
    for logn in (20, 24):
        n, k = 2 ** logn, 2 ** (logn - r)
        for J in (0, 2):
            val, lam = E.best(r, logn - r, J, 2, 3)
            _, main, first, C, Cp, eh = E.eps(r, logn - r, J, 2, 3, -130.0, 0.0, lam, parts=True)
            pig = (k - 65) // 63 + 1
            fm = first_moment(n, k, 2, 3)
            print(f"rate 2^-{r} n=2^{logn} J={J}: eps_3 n / k = {val*n/k:.4f} (main {main*n/k:.4f}, first level {first*n/k:.4f}); pigeonhole lower bound / k = {pig/k:.4f}; first moment / k = {fm/k:.4f}; main/pigeonhole = {main*n/pig:.1f}, main/first moment = {main*n/fm:.2f}")
