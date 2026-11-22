#!/usr/bin/env python3
"""Note 61, section 9: the ladder with constant list size of note 57, section 8. Standard library only.

Hypothesis T_t at agreement A (note 57, section 8): for every word, every t members of its list at agreement A,
with agreement sets trimmed to A positions and cover counts c_x, satisfy

    sum_x (c_x - 1)_+  <=  B_t(A) := (t - 1) k + (t n H(A/n) + 130) / 64.

The finite-M inequality (note 61, Proposition J): if a word has M >= t list members at agreement A, then

    F(M) := t A - n + [(n - rem) C(M - m0, t) + rem C(M - m0 - 1, t)] / C(M, t)  <=  B_t(A),   M A = n m0 + rem,

because the cover count of a uniform t-subfamily at a position covered by m of the M sets is hypergeometric, its
expected excess is h(m) = t m / M - 1 + C(M - m, t) / C(M, t), h is convex and nondecreasing in m, and the m_x sum
to M A. F(M) is exact rational arithmetic here; B_t(A) has the entropy term in double precision (error below 1e-5
bits against a 130-bit margin). The list bound at A is (the least M >= t with F(M) > B_t(A)) - 1; it is finite
exactly when n g_t(A/n) > B_t(A), g_t(p) = t p - 1 + (1 - p)^t.

With a list below 2^63 the paper's Proposition 6.2 (machine-checked for any code with a generator over K) gives
2 M - 1 for every number of lanes and every extension of K, so the points are those of Theorem D' with that list.

Usage:
  python3 61_ladder.py            the tables of note 61, section 9 (under a minute)
  python3 61_ladder.py selftest
"""

from __future__ import annotations

import importlib.util
import math
import os
import random
import sys
from dataclasses import replace
from fractions import Fraction
from functools import lru_cache
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("params61", os.path.join(HERE, "61_params.py"))
p61 = importlib.util.module_from_spec(_spec)
sys.modules["params61"] = p61
_spec.loader.exec_module(p61)
c8, wm, d11 = p61.c8, p61.wm, p61.d11

TS = (3, 4, 5, 6, 8, 12, 16, 24)
RATES = (1, 2, 3, 4)
CAPS = (8, 32, 1 << 10, 1 << 20, 1 << 39)  # single-lane list sizes tried at a level (2 M - 1 after Proposition 6.2)


def b_bits(n, k, t, a):
    """64 B_t(A)."""
    return 64 * (t - 1) * k + t * p61.entropy_bits(n, a) + p61.MARGIN


def f_exact(m_fam, n, a, t):
    """F(M): the least possible average over the t-subfamilies of sum_x (c_x - 1)_+ for M sets of A positions."""
    m0, rem = divmod(m_fam * a, n)
    num = (n - rem) * comb(m_fam - m0, t) + (rem * comb(m_fam - m0 - 1, t) if rem else 0)
    return t * a - n + Fraction(num, comb(m_fam, t))


def excluded(m_fam, n, k, t, a):
    """No word has M list members at agreement A (given T_t at A)."""
    return 64 * f_exact(m_fam, n, a, t) > b_bits(n, k, t, a)


def g(t, p):
    return t * p - 1 + (1 - p) ** t


def above_threshold(n, k, t, a):
    return 64 * n * g(t, a / n) > b_bits(n, k, t, a)


def threshold(n, k, t, entropy=True):
    """The least A with n g_t(A/n) > B_t(A) (with `entropy` False: > (t - 1) k)."""
    lo, hi = k, n

    def ok(a):
        return above_threshold(n, k, t, a) if entropy else n * g(t, a / n) > (t - 1) * k

    while lo < hi:
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def list_bound(n, k, t, a):
    """The largest M that T_t at A does not exclude, or None when no M is excluded."""
    if excluded(t, n, k, t, a):
        return t - 1
    hi = 2 * t
    while not excluded(hi, n, k, t, a):
        hi *= 2
        if hi.bit_length() > 80:
            return None
    lo = hi // 2  # not excluded
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if excluded(mid, n, k, t, a):
            hi = mid
        else:
            lo = mid
    return lo


@lru_cache(maxsize=None)
def agreement_for(n, k, t, cap):
    """The least A at which a list of cap + 1 members is excluded (then so is every larger list, which contains
    one), or None when cap < t - 1, which the argument cannot give."""
    if cap + 1 < t or not excluded(cap + 1, n, k, t, n):
        return None
    lo, hi = threshold(n, k, t), n
    while lo < hi:
        mid = (lo + hi) // 2
        if excluded(cap + 1, n, k, t, mid):
            hi = mid
        else:
            lo = mid + 1
    return lo


def rung_level(index, rate, cols, k, t, final, partners):
    """A window-mixed level on rung t: the cheapest in bytes among a few list caps."""
    lv = _rung_level(min(index, 1), rate, cols, k, t, final)
    return None if lv is None else replace(lv, partners=partners)


@lru_cache(maxsize=None)
def _rung_level(index, rate, cols, k, t, final):
    log_n = cols + rate
    n, kk = 1 << log_n, 1 << cols
    if t > log_n - 1:
        return None
    d_mu, _ = p61.agreement_bound(n, kk)
    loss = p61.loss(n)
    best = None
    for cap in CAPS:
        a0 = agreement_for(n, kk, t, cap)
        if a0 is None or a0 <= d_mu + 2 * loss:
            continue
        lv = p61.Level(rate, cols, k, a0, a0 + k * loss, 2 * cap - 1, f"rung {t}", t, 64)
        lv = p61.finish(lv, final)
        if best is None or p61.level_bytes(index, lv) < p61.level_bytes(index, best):
            best = lv
    return best


@lru_cache(maxsize=None)
def _rs(_kind, index, rate, cols, k, final):
    return p61.rs_level(index, rate, cols, k, final)


def build(mu, rate, t, stride=False, mixed_levels=None):
    rates, cols, folds, _ = wm.ladder(mu, rate)
    out = []
    for i, (r, c, k) in enumerate(zip(rates, cols, folds)):
        final = i == len(rates) - 1
        best = replace(_rs(min(i, 1), i, r, c, k, final))
        if t and not final and (mixed_levels is None or i in mixed_levels):
            tt = min(t, c + r - 1)
            cand = rung_level(i, r, c, k, tt, final, tt if stride else -1)
            if cand is not None and p61.level_bytes(i, cand) < p61.level_bytes(i, best):
                best = cand
        out.append(best)
    return out


# --------------------------------------------------------------------------------------------------------------
# Tables
# --------------------------------------------------------------------------------------------------------------


def table_thresholds(mu=30):
    print(f"## L1. The rungs at level 0, mu = {mu}: thresholds, list constants, points; against Theorem M at L = t - 1\n")
    print("| rate | t | threshold without / with the entropy term, A/n | queries at the first column above it (with the loss) | list bound there | columns above the threshold for a list of 1000 / 32 / 8 | points for lists 1000 / 32 / 8 (after the factor 2) | Theorem M at L = t - 1: A/n, queries | its list, log2: direct / Proposition I' | its points: direct / Proposition I' |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    kappa, ell = mu - 6, 6
    for rate in RATES:
        n, k = 1 << (kappa + rate), 1 << kappa
        loss = p61.loss(n)
        for t in TS:
            if t > kappa + rate - 1:
                continue
            a_no, a_thr = threshold(n, k, t, entropy=False), threshold(n, k, t)
            w = p61.query_count(kappa + rate, a_thr + ell * loss, 40, False)
            lb = list_bound(n, k, t, a_thr)
            cols_above, pts = [], []
            for cap in (1000, 32, 8):
                a = agreement_for(n, k, t, cap)
                cols_above.append("none" if a is None else a - a_thr)
                pts.append("" if a is None else p61.points_needed(2 * cap - 1, kappa, ell))
            big_l = t - 1
            md = p61.mixed_level(rate, kappa, ell, big_l, "direct", False)
            mp = p61.mixed_level(rate, kappa, ell, big_l, "profile", False)
            print(
                f"| 1/{1 << rate} | {t} | {a_no / n:.4f} / {a_thr / n:.4f} | {w} | {'2^%.1f' % math.log2(lb) if lb else 'none'} | {' / '.join(map(str, cols_above))} | {' / '.join(map(str, pts))} "
                f"| {md.a0 / n:.4f}, {md.queries} | {p61.lg(md.list_size):.0f} / {p61.lg(mp.list_size):.0f} | {md.points} / {mp.points} |"
            )
    print()


def table_openings(mu=30):
    print(f"## L2. The whole opening on rung t, mu = {mu}; a level is mixed where that gives fewer bytes (rung clipped to N_i - 1)\n")
    print("| rate | t | queries per level | points per level | codes | KiB | vs today | recursion (est.), cube windows | recursion (est.), t stride partners | native window products: cube / strides |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        cfg, c0 = p61.today(mu, rate)
        rec0 = p61.today_recursion(c0)
        print(f"| 1/{1 << rate} | today | {' '.join(map(str, cfg.queries))} | one OOD | | {p61.kib(c0.proof_bytes)} | | {rec0:.0f} | | |")
        lv0 = p61.build(mu, rate, 0)
        cz = p61.cost(lv0)
        print(f"| | Reed-Solomon, plain fold | {' '.join(str(x.queries) for x in lv0)} | {' '.join(str(x.points) for x in lv0)} | | {p61.kib(cz.proof_bytes)} | {p61.pct(cz.proof_bytes, c0.proof_bytes)} | {cz.recursion:.0f} ({p61.pct(cz.recursion, rec0)}) | | |")
        for t in TS:
            lv = build(mu, rate, t)
            ls = build(mu, rate, t, stride=True)
            c, cs = p61.cost(lv), p61.cost(ls)
            codes = " ".join(("R%d" % x.big_l) if x.mixed else ("J" if x.code == "RS Johnson" else "C") for x in lv)
            print(
                f"| | {t} | {' '.join(str(x.queries) for x in lv)} | {' '.join(str(x.points) for x in lv)} | {codes} | {p61.kib(c.proof_bytes)} | {p61.pct(c.proof_bytes, c0.proof_bytes)} "
                f"| {c.recursion:.0f} ({p61.pct(c.recursion, rec0)}) | {cs.recursion:.0f} ({p61.pct(cs.recursion, rec0)}) | {c.window_mults} / {cs.window_mults:.0f} |"
            )
    print()


def table_level0_only(mu=30):
    print(f"## L3. Level 0 alone on rung t, mu = {mu}\n")
    print("| rate | t | level-0 queries | level-0 points | KiB | vs today | recursion (est.): cube / strides |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for rate in RATES:
        _, c0 = p61.today(mu, rate)
        rec0 = p61.today_recursion(c0)
        for t in TS:
            lv = build(mu, rate, t, mixed_levels={0})
            ls = build(mu, rate, t, stride=True, mixed_levels={0})
            c, cs = p61.cost(lv), p61.cost(ls)
            print(f"| 1/{1 << rate} | {t} | {lv[0].queries} | {lv[0].points} | {p61.kib(c.proof_bytes)} | {p61.pct(c.proof_bytes, c0.proof_bytes)} | {p61.pct(c.recursion, rec0)} / {p61.pct(cs.recursion, rec0)} |")
    print()


def table_windows(mu=30):
    print(f"## L4. What a window costs, level 0, mu = {mu}, rate 1/2 (kappa = 24, N = 25)\n")
    print("| window | partners | prover: products a codeword word (the NTT has about 12 butterflies a word) | Keccak-f a position for mu | verifier: changed factors a query | guest cycles a query added (est.) |")
    print("| --- | --- | --- | --- | --- | --- |")
    kappa, log_n = mu - 6, mu - 5
    prods = p61.window_products(kappa, log_n)
    print(f"| the cube, r = N + 1 | {log_n} | {log_n} | 1 | {prods} | {2 * prods + 4 * log_n + 8} |")
    for t in TS:
        sp = p61.stride_products(kappa, log_n, t)
        print(f"| strides, r = t + 1 = {t + 1} | {t} | {t} | {t / 25:.2f} | {sp} | {3 * sp + 4 * t + 8} |")
    print()


def selftest():
    rnd = random.Random(61)
    # The identity behind Proposition J: over all t-subfamilies, the average of sum_x (c_x - 1)_+ is sum_x h(m_x),
    # and it is at least F(M) when every set has at least A positions.
    from itertools import combinations

    for _ in range(40):
        n, m_fam, t = rnd.randrange(6, 13), rnd.randrange(3, 8), rnd.randrange(2, 4)
        t = min(t, m_fam)
        a = rnd.randrange(2, n)
        sets = [set(rnd.sample(range(n), a)) for _ in range(m_fam)]
        cover = [sum(x in s for s in sets) for x in range(n)]
        total, count = 0, 0
        for sub in combinations(range(m_fam), t):
            total += sum(max(sum(x in sets[i] for i in sub) - 1, 0) for x in range(n))
            count += 1
        avg = Fraction(total, count)
        h = sum(Fraction(t * m, m_fam) - 1 + Fraction(comb(m_fam - m, t), comb(m_fam, t)) for m in cover)
        assert avg == h and h >= f_exact(m_fam, n, a, t), (avg, h)
    # F(M) is attained by a balanced family, increases with M, and tends to n g_t(A/n) from below.
    n, k = 1 << 25, 1 << 24
    for t in (3, 5, 8, 16):
        a = threshold(n, k, t) + 1000
        prev = None
        for m_fam in (t, t + 1, 2 * t, 50, 1000, 10**6, 10**12, 10**18):
            f = f_exact(m_fam, n, a, t)
            assert f <= n * g(t, a / n) * (1 + 1e-12)
            assert prev is None or f >= prev
            prev = f
        assert float(prev) > n * g(t, a / n) - 1
    # The lead's thresholds (note 57, section 8), to its four digits; and its queries within one.
    lead = {1: {3: 0.6689, 4: 0.6354, 5: 0.6133, 8: 0.5777, 16: 0.5468}, 2: {3: 0.4643, 4: 0.4257, 5: 0.3996, 8: 0.3546, 16: 0.3107},
            3: {3: 0.3313, 4: 0.2961, 5: 0.2724, 8: 0.2313, 16: 0.1884}, 4: {3: 0.2428, 4: 0.2123, 5: 0.1923, 8: 0.1579, 16: 0.1216}}
    for rate, row in lead.items():
        n, k = 1 << (24 + rate), 1 << 24
        for t, val in row.items():
            assert abs(threshold(n, k, t) / n - val) < 1.5e-4, (rate, t, threshold(n, k, t) / n)
    # The list bound falls as the agreement grows and matches the first-order estimate.
    n, k, t = 1 << 25, 1 << 24, 4
    a = threshold(n, k, t) + (1 << 15)
    lb = list_bound(n, k, t, a)
    alpha = a / n
    est = alpha * (1 - alpha) ** (t - 1) * t * (t - 1) * n / 2 / (n * g(t, alpha) - b_bits(n, k, t, a) / 64)
    assert 0.8 < lb / est < 1.25, (lb, est)
    assert list_bound(n, k, t, a + (1 << 15)) < lb
    print("selftest passed")


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "selftest":
        selftest()
        return
    table_thresholds()
    table_windows()
    table_openings()
    table_level0_only()
    selftest()


if __name__ == "__main__":
    main()
