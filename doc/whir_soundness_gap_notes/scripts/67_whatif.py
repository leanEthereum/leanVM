#!/usr/bin/env python3
"""Note 67, sections 2 and 4: where the DEEP fold's proven gain comes from, and what a new result would add.

Part 1 (proven): on C's shape with A's level-0 query grind, level by level: C's queries, the DEEP fold at Johnson
thresholds only, with the shortened Johnson bound, and with every bound of section 1; then the DEEP-only knobs.
Part 2 (hypothetical, labelled so): the same shape with
  floor     the points at the floor of the paper's state function, s = 1 + ceil((110 + 2 log2 L) / log2(1/eps));
  count/c   a counting bound with its exponent divided by c (lists of 2^(log2 C(n,d+1)/C(A,d+1) / c));
  level 0   a list of 2^40 at agreement 0.66 n (rate 1/2) or 7/16 n (rate 1/4) at level 0, the paper's rows.
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("m67", os.path.join(HERE, "67_model.py"))
m = importlib.util.module_from_spec(spec)
sys.modules["m67"] = m
spec.loader.exec_module(m)
sys.path.insert(0, os.path.join(HERE, "08_retuning"))
import recommend  # noqa: E402

REAL = (m.best_list, m.list_bits_estimate, m.ladder_schedule)


def lgc(n, k):
    return (math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)) / math.log(2)


def set_hypothesis(divide=None, floor=False, shortened=True):
    """Swap the list bound and the schedule of the model, and forget its cached levels."""
    m._LEVELS.clear()
    m.best_list, m.list_bits_estimate, m.ladder_schedule = REAL
    if divide is not None:
        def bits(n, a, d):
            return 0.0 if a * a > n * d else (lgc(n, d + 1) - lgc(a, d + 1)) / divide

        def best(n, a, d):
            jl = m.johnson(n, a, d)
            return (jl, "Johnson") if jl is not None else (1 << math.ceil(bits(n, a, d)), f"count/{divide}")

        m.best_list, m.list_bits_estimate = best, bits
    elif not shortened:
        def best(n, a, d):
            jl = m.johnson(n, a, d)
            return (jl, "Johnson") if jl is not None else (m.counting(n, a, d) if d <= 5000 else 1 << 10**6, "counting")

        m.best_list = best
        m.list_bits_estimate = lambda n, a, d: 0.0 if a * a > n * d else lgc(n, d + 1) - lgc(a, d + 1)
    if floor:
        def sched(big_l, d, ell, g_point=15, g_fold=7):
            lam = 128 - math.log2(d + (1 << ell) - 1)
            return (1 + math.ceil((110 + 2 * m.lg(max(big_l, 2))) / lam),) * ell

        m.ladder_schedule = sched


def run(mu, rate, lists="proven", level0=None, objective="bytes"):
    shp = m.deployed_shape(mu, rate, recommend.config("C", mu))
    gq = [max(17, mu - 6)] + [17] * (len(shp) - 1)
    lv = m.build(shp, gq, objective=objective, lists=lists)
    if level0 is not None:
        r, c, k = shp[0]
        n = 1 << (c + r)
        cand = m.Level(0, r, c, k, math.ceil(level0 * n), 1 << 40, "assumed", gq[0], False)
        assert cand.finish("ladder", 15, 7)
        lv[0] = cand
    return lv, m.cost(lv)


def main():
    for mu in (24, 28, 30):
        for rate in (1, 2):
            c = m.today_cost(mu, rate, recommend.config("C", mu))
            print(f"\nmu = {mu}, rate 1/{1 << rate}; C: queries {c['queries']}, {c['bytes'] / 1024:.1f} KiB, {c['cycle_equiv'] / 1000:.1f}k cycle-eq")
            rows = [("proven: Johnson only", dict(), dict(lists="johnson")), ("proven: Johnson and counting (the paper's two)", dict(shortened=False), dict()),
                    ("proven: all of section 1", dict(), dict()), ("proven: all, levels chosen for cycle-eq", dict(), dict(objective="cycles")),
                    ("HYPOTHETICAL floor", dict(floor=True), dict()), ("HYPOTHETICAL count/2", dict(divide=2), dict()), ("HYPOTHETICAL count/4", dict(divide=4), dict()),
                    ("HYPOTHETICAL count/8", dict(divide=8), dict()), ("HYPOTHETICAL count/4 and floor", dict(divide=4, floor=True), dict()),
                    ("HYPOTHETICAL count/4 and floor, for cycle-eq", dict(divide=4, floor=True), dict(objective="cycles")),
                    ("HYPOTHETICAL level 0 below Johnson", dict(), dict(level0=0.66 if rate == 1 else 7 / 16))]
            for name, hyp, kw in rows:
                set_hypothesis(**hyp)
                lv, d = run(mu, rate, **kw)
                print(f"  {name}: queries {d['queries']}, points {d['points']}, {d['point_scalars']} point scalars, {d['bytes'] / 1024:.1f} KiB ({100 * (d['bytes'] / c['bytes'] - 1):+.1f}% C),"
                      f" {d['cycle_equiv'] / 1000:.1f}k cycle-eq ({100 * (d['cycle_equiv'] / c['cycle_equiv'] - 1):+.1f}% C)")
    set_hypothesis()
    print("\nDEEP-only knobs, mu = 30, rate 1/2, C's shape, proven lists (bytes; point scalars; grind log2 perms):")
    shp = m.deployed_shape(30, 1, recommend.config("C", 30))
    gq = [24] + [17] * (len(shp) - 1)
    for sched in ("batch", "ladder"):
        for g_point, g_fold in ((15, 7), (15, 12), (15, 17), (20, 7), (20, 17)):
            m._LEVELS.clear()
            lv = m.build(shp, gq, sched=sched, g_point=g_point, g_fold=g_fold)
            d = m.cost(lv, g_point=g_point, g_fold=g_fold)
            print(f"  {sched}, point grind {g_point}, fold grind {g_fold}: points {d['points']}, {d['point_scalars']} scalars, {d['bytes'] / 1024:.2f} KiB, grind 2^{math.log2(d['grind']):.2f}")


if __name__ == "__main__":
    main()
