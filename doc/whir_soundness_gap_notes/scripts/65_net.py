#!/usr/bin/env python3
"""Note 65: the net of a sparsely mixed code on rung t with d partners a position, on note 61's model (imported).

N1  The crude count C(n'', k'') / C(A'', k'') of a quotient domain of n'' points, and the points it costs.
N2  Per rung, rate and d: queries, opening, guest recursion metric (cycles + 8 a KECCAK step) under four ways of
    getting a partner's weight, prover time added. The levels are note 61's ladder levels (61_ladder.build) with the
    window cost taken out (partners = 0 keeps one KECCAK step a query for the oracle) and this note's models put in:

      direct, unrelated partner   d (38 + 4 kappa + 6)                 decode, point, chain, combine
      direct, pool partner        d (10 + 2 kappa + 4)
      delegated, unrelated        -(7.6 kappa - 37) + 15 (d + 1) + 3 + 38 d,  fixed F a level
      delegated, pool             -(7.6 kappa - 37) + 15 (d + 1) + 3 + 10 d,  fixed F + 3300 a level
      F = 38 R + N (N + 1) + 500 + 2^aq + 2^al,  R = 5 a + 10 rounds,  a = aq + al,  bytes 16 (3 R + 11) a level.

    Prover, in percent of today's rate-1/2 proving time (note 65, 1.1): mixing d (0.07..0.13) (12.7..16.8) c,
    oracle (4..5) c, points 2.3, with c = 2^(R - 1) the codeword's size against rate 1/2; the rate itself costs
    32..52 a halving (note 61, measured).
"""
import importlib.util
import math
import os
import sys
from dataclasses import replace
from math import comb

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("ladder61", os.path.join(HERE, "61_ladder.py"))
l61 = importlib.util.module_from_spec(_spec)
sys.modules["ladder61"] = l61
_spec.loader.exec_module(l61)
p61 = l61.p61
MU = 30
DMIN = {(1, 4): 5, (1, 5): 5, (1, 8): 7, (2, 4): 4, (2, 5): 5, (2, 8): 7}  # 65_expansion.py, E2, note 60's bound


def window_cycles(model, w, kappa, log_n, d):
    """(cycles added over the level's w queries, fixed cycles, proof bytes) of a mixed level."""
    chain = max(0.0, 7.6 * kappa - 37)
    if model == "direct":
        return w * d * (38 + 4 * kappa + 6), 0.0, 0
    if model == "direct pool":
        return w * d * (10 + 2 * kappa + 4), 0.0, 0
    aq, al = math.ceil(math.log2(w)), math.ceil(math.log2(d + 1))
    rounds = 5 * (aq + al) + 10
    fixed = 38 * rounds + log_n * (log_n + 1) + 500 + 2**aq + 2**al + (3300 if model == "gkr pool" else 0)
    per = -chain + 15 * (d + 1) + 3 + (10 if model == "gkr pool" else 38) * d
    if d * (log_n + 64) > 1088:
        per += 8
    return w * per, fixed, 16 * (3 * rounds + 11)


def evaluate(rate, t, d, mixed_levels=None):
    levels = [replace(lv, partners=0) if lv.mixed else lv for lv in l61.build(MU, rate, t, stride=True, mixed_levels=mixed_levels)]
    c = p61.cost(levels)
    out = {"queries": [lv.queries for lv in levels], "points": [lv.points for lv in levels], "mixed": [lv.mixed for lv in levels]}
    for model in ("direct", "direct pool", "gkr", "gkr pool"):
        cyc = byt = 0.0
        for lv in levels:
            if lv.mixed:
                a, f, b = window_cycles(model, lv.queries, lv.cols, lv.log_block, d)
                cyc, byt = cyc + a + f, byt + b
        out[model] = (c.recursion + cyc, c.proof_bytes + byt)
    return out


def prover_added(rate, d):
    c = 2 ** (rate - 1)
    lo = d * 0.07 * 12.7 * c + 4 * c + 2.3
    hi = d * 0.13 * 16.8 * c + 5 * c + 2.3
    return lo, hi


def table_crude():
    print("## N1. The crude count on a quotient of n'' points, and the points a level needs for it (kappa = 24, 6 folds)\n")
    print("| rate | agreement | n'' = 64 | 256 | 512 | 1024 | 2048 | 4096 |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for rate, alphas in ((1, (0.6354, 0.6133, 0.5777)), (2, (0.4257, 0.3996, 0.3546))):
        for a in alphas:
            cells = []
            for lg in (6, 8, 9, 10, 11, 12):
                n2 = 1 << lg
                k2 = n2 >> rate
                size = comb(n2, k2) // comb(math.ceil(a * n2), k2)
                pts = p61.points_needed(2 * 8 * size, 24, 6)
                cells.append(f"2^{math.log2(size):.0f}, {pts if pts else '> 400'}")
            print(f"| 1/{1 << rate} | {a} | " + " | ".join(cells) + " |")
    print()


def table_net():
    print(f"## N2. The net at mu = {MU}: rung t, d partners, every level mixed where that saves bytes\n")
    print("| rate | t | d | queries per level | points | KiB with the delegation's bytes | vs today, same rate | vs today's rate 1/2 | recursion vs today, same rate: direct unrelated / direct pool / delegated unrelated / delegated pool | prover added, % of today's rate-1/2 time |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    _, base = p61.today(MU, 1)
    for rate in (1, 2):
        cfg, c0 = p61.today(MU, rate)
        rec0 = p61.today_recursion(c0)
        rate_cost = (0, 0) if rate == 1 else (32, 52)
        print(f"| 1/{1 << rate} | today | 0 | {' '.join(map(str, cfg.queries))} | one OOD | {p61.kib(c0.proof_bytes)} | | {p61.pct(c0.proof_bytes, base.proof_bytes)} | | {rate_cost[0]} to {rate_cost[1]} |")
        for t in (4, 5, 8):
            for d in sorted({max(8, t), DMIN[rate, t]}, reverse=True):
                r = evaluate(rate, t, d)
                lo, hi = prover_added(rate, d)
                recs = " / ".join(p61.pct(r[m][0], rec0) for m in ("direct", "direct pool", "gkr", "gkr pool"))
                byt = r["gkr"][1]
                print(
                    f"| | {t} | {d} | {' '.join(map(str, r['queries']))} | {' '.join(map(str, r['points']))} | {p61.kib(byt)} "
                    f"| {p61.pct(byt, c0.proof_bytes)} | {p61.pct(byt, base.proof_bytes)} | {recs} | {rate_cost[0] + lo:.0f} to {rate_cost[1] + hi:.0f} |"
                )
    print()


def table_level0():
    print(f"## N3. Level 0 alone mixed, mu = {MU}, delegated weights, unrelated partners\n")
    print("| rate | t | d | level-0 queries | KiB | vs today, same rate | recursion vs today, same rate |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for rate in (1, 2):
        _, c0 = p61.today(MU, rate)
        rec0 = p61.today_recursion(c0)
        for t in (4, 5, 8):
            for d in sorted({max(8, t), DMIN[rate, t]}, reverse=True):
                r = evaluate(rate, t, d, mixed_levels={0})
                print(f"| 1/{1 << rate} | {t} | {d} | {r['queries'][0]} | {p61.kib(r['gkr'][1])} | {p61.pct(r['gkr'][1], c0.proof_bytes)} | {p61.pct(r['gkr'][0], rec0)} |")
    print()


if __name__ == "__main__":
    table_crude()
    table_net()
    table_level0()
