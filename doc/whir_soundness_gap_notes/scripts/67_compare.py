#!/usr/bin/env python3
"""Note 67, section 3: today's protocol (deployed, A, B, C of note 08, and its best ladder of `67_search.py`) against
the DEEP fold under proven list bounds (the paper's printed instance, the deployed ladder, C's shape with A's grinds,
and the best ladders of `67_search.py`), at rates 1/2 and 1/4 and mu = 24, 28, 30. Prints markdown tables.

The ladders marked `*` are the winners of `67_search.py` (files 67_search_output_*.txt), copied here.
Guest cycle-equivalents = query cycles (note 08's fit) + 8 a KECCAK step + point cycles (note 11's count: two
cycles a field product and 20 a point); the column 'floor' counts one cycle a product and nothing else for a point.
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

wm, d11 = m.wm, m.d11

# (mu, rate): (today's protocol least bytes, DEEP least bytes, DEEP least cycle-equivalents), grinds A
BEST = {
    (24, 1): (((5, 4, 4, 4, 3), (3, 1, 1, 1)), ((5, 4, 4, 4, 3), (3, 1, 1, 1)), ((5, 4, 4, 5, 3), (3, 1, 1, 1))),
    (24, 2): (((5, 4, 4, 4, 3), (3, 1, 1, 1)), ((5, 4, 4, 4, 3), (3, 1, 1, 1)), ((5, 5, 5, 5), (3, 1, 0))),
    (28, 1): (((5, 4, 4, 4, 3, 3), (3, 1, 1, 1, 1)), ((5, 4, 4, 5, 5), (3, 1, 1, 0)), ((5, 4, 5, 5, 5), (3, 1, 1, 0))),
    (28, 2): (((5, 4, 4, 5, 5), (3, 1, 1, 0)), ((5, 4, 4, 5, 5), (3, 1, 1, 1)), ((5, 5, 5, 4, 5), (3, 1, 1, 1))),
    (30, 1): (((5, 4, 4, 4, 4, 4), (3, 1, 1, 1, 0)), ((5, 4, 4, 4, 4, 4), (3, 1, 1, 1, 0)), ((5, 4, 4, 4, 4, 5), (3, 1, 1, 1, 1))),
    (30, 2): (((5, 4, 4, 4, 4, 4), (3, 1, 1, 1, 0)), ((5, 4, 4, 4, 4, 4), (3, 1, 1, 1, 1)), ((5, 4, 5, 4, 4, 5), (3, 1, 1, 1, 1))),
}


def fmt(ladder):
    return "".join(map(str, ladder[0])) + "/" + "".join(map(str, ladder[1]))


def today_knobs(mu, folds, reds):
    g0 = max(17, mu - 6)
    return wm.with_knobs(
        initial_fold=folds[0], initial_reduction=reds[0], residual_max=mu - sum(folds),
        fold_levels=tuple((i, k) for i, k in enumerate(folds) if i >= 1), reduction_levels=tuple(enumerate(reds)),
        g_query_levels=((0, g0),), g_batch=14, g_ood=16,
    )


def today_row(name, mu, rate, kn):
    c = m.today_cost(mu, rate, kn)
    return dict(name=name, queries=c["queries"], points=None, bytes=c["bytes"], keccak=c["guest_keccak"], cyc=c["cycle_equiv"], floor=c["cycle_equiv"],
                enc=c["encoding"], grind=c["grind"], share=0.0)


def deep_row(name, mu, rate, shp, gq, sched="ladder", objective="bytes"):
    lv = m.build(shp, gq, sched=sched, objective=objective)
    c = m.cost(lv)
    products = sum((x.point_cycles() - 20 * x.points) / 2 for x in lv)
    return dict(name=name, queries=c["queries"], points=c["points"], bytes=c["bytes"], keccak=c["guest_keccak"], cyc=c["cycle_equiv"],
                floor=c["query_cycles"] + 8 * c["guest_keccak"] + products, enc=m.encoding(shp), grind=c["grind"], share=m.point_prover_share(lv, mu, rate))


def paper_row(mu, rate):
    lv = d11.build(mu, rate)
    c = d11.deep_cost(mu, lv)
    pts = d11.point_guest_cycles(lv)
    shp = m.deployed_shape(mu, rate)

    class _L:  # the prover-share estimate reads sbar, points, cols, k
        def __init__(self, x):
            self.sbar, self.points, self.cols, self.k = (x.points,) * x.k, x.points, x.cols, x.k

    floor_pts = (pts - 20 * sum(x.points for x in lv)) / 2
    return dict(name="P (paper)", queries=[x.queries for x in lv], points=[x.points for x in lv], bytes=c.proof_bytes,
                keccak=c.guest_keccak, cyc=c.guest_query_cycles + 8 * c.guest_keccak + pts, floor=c.guest_query_cycles + 8 * c.guest_keccak + floor_pts,
                enc=m.encoding(shp), grind=c.grind_perms, share=m.point_prover_share([_L(x) for x in lv], mu, rate))


def table(mu, rate):
    g0 = max(17, mu - 6)
    t_best, d_best, d_cyc = BEST[(mu, rate)]
    rows = [today_row(name, mu, rate, recommend.config(key, mu)) for name, key in (("today", "today"), ("A", "A"), ("B", "B"), ("C", "C"))]
    rows.append(today_row(f"T* {fmt(t_best)}", mu, rate, today_knobs(mu, *t_best)))
    rows.append(paper_row(mu, rate))
    dep = m.deployed_shape(mu, rate)
    rows.append(deep_row("D0", mu, rate, dep, [17] * len(dep)))
    c_shape = m.deployed_shape(mu, rate, recommend.config("C", mu))
    rows.append(deep_row("D+C", mu, rate, c_shape, [g0] + [17] * (len(c_shape) - 1)))
    shp = m.shape(mu, rate, list(d_best[0]), list(d_best[1]))
    rows.append(deep_row(f"D* {fmt(d_best)}", mu, rate, shp, [g0] + [17] * (len(shp) - 1)))
    shp = m.shape(mu, rate, list(d_cyc[0]), list(d_cyc[1]))
    rows.append(deep_row(f"Dc {fmt(d_cyc)}", mu, rate, shp, [g0] + [17] * (len(shp) - 1), objective="cycles"))
    base, c_row = rows[0], rows[3]
    print(f"\n**$\\mu = {mu}$, rate 1/{1 << rate}** (percentages: against today / against C)\n")
    print("| configuration | queries per level | points per level | opening, KiB | guest Keccak | guest cycle-eq | same, point floor | prover: NTT, Merkle, grind ($\\log_2$ perms), points |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for r in rows:
        pct = lambda key: f"{100 * (r[key] / base[key] - 1):+.1f}% / {100 * (r[key] / c_row[key] - 1):+.1f}%"
        pts = " ".join(map(str, r["points"])) if r["points"] else "1 OOD each"
        print(
            f"| {r['name']} | {' '.join(map(str, r['queries']))} | {pts} | {r['bytes'] / 1024:.1f} ({pct('bytes')}) | {r['keccak']:.0f} | {r['cyc'] / 1000:.1f}k ({pct('cyc')})"
            f" | {r['floor'] / 1000:.1f}k ({100 * (r['floor'] / c_row['floor'] - 1):+.1f}% C) | x{r['enc'][1] / base['enc'][1]:.2f}, x{r['enc'][2] / base['enc'][2]:.2f}, {math.log2(r['grind']):.2f}, {r['share']:+.1f}% |"
        )


if __name__ == "__main__":
    for mu in (24, 28, 30):
        for rate in (1, 2):
            table(mu, rate)
