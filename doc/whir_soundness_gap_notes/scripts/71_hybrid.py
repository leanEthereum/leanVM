#!/usr/bin/env python3
"""Note 71, section 5.3: the hybrid opening. Level 0 is the tree code with the DEEP fold (points, scalar fold);
levels 1 and later are today's protocol at configuration C's knobs (Annex B's analysis, one OOD point a level).

The boundary row (sketch in the note): ((A_end - 1)/n)^t + (sbar + t + 1) L_1 / q <= 2^-(125 - g_query), with L_1
the Johnson list of level 1 that note 08's model derives. Usage: python3 71_hybrid.py [--bestcap]
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("p71", os.path.join(HERE, "71_payoff.py"))
p71 = importlib.util.module_from_spec(spec)
sys.modules["p71"] = p71
spec.loader.exec_module(p71)
t71, m67, c8, recommend = p71.t71, p71.m67, p71.c8, p71.recommend
wm = m67.wm
Q = 1 << 128


def hybrid(mu, rate, big_l, eps, kn):
    cfg = wm.derive(mu, rate, kn)
    lv0c, later = cfg.levels[0], cfg.levels[1:]
    g0 = kn.query_grind(0)
    tree = p71.TreeLevel(rate, lv0c.cols, lv0c.k, big_l, eps, g0)
    n, held, l1 = 1 << tree.log_block, tree.points, later[0].list_bound
    t = 1
    while True:
        room = (1 << (128 - 125 + g0)) - (t + 1 + held) * l1
        if room > 0 and (tree.a_end - 1) ** t * Q <= room * n**t:
            break
        t += 1
    tree.queries = t
    sponge = c8.SpongeCount()
    first = tree.sbar[0]
    scalars = 3 + first + 1
    sponge.absorb(2)
    sponge.grind(15)
    sponge.sample(tree.per_point * first)
    sponge.absorb(first)
    sponge.grind(7)
    sponge.sample()
    grind = (1 << 15) + (1 << 7) + tree.k * (1 << tree.g_fold) + (1 << g0) + len(later) * (1 << kn.g_ood)
    for j in range(tree.k):
        fresh = tree.sbar[j] - tree.sbar[j - 1] if j else 0
        scalars += fresh + 2 + tree.sbar[j] + 1
        sponge.absorb(fresh + 2 + tree.sbar[j])
        sponge.grind(tree.g_fold)
        sponge.sample(1 + tree.per_point * (tree.sbar[j + 1] - tree.sbar[j] if j + 1 < tree.k else 0))
    out = dict(bytes=0.0, guest_keccak=0.0, cycles=0.0)
    levels = [tree] + later
    for i, lv in enumerate(levels):
        final, depth, t = i == len(levels) - 1, lv.log_block, lv.queries
        if i:
            for _ in range(lv.k):
                scalars += 5
                sponge.absorb(4)
                sponge.grind(kn.g_fold)
                sponge.sample(2)
            grind += lv.k * (1 << kn.g_fold) + (1 << kn.query_grind(i))
        per_word = 128 // depth
        if final:
            n_final = (1 << lv.cols) + lv.k
            scalars += n_final + 1 + 2 * lv.cols
            sponge.absorb(n_final)
            sponge.grind(17)
            sponge.sample(-(-t // per_word))
            for _ in range(lv.cols):
                sponge.absorb(2)
                sponge.sample()
        else:
            high = lv.k if i else 0
            scalars += 2 + high + 3
            sponge.absorb(2 + high)
            sponge.grind(kn.g_ood)
            sponge.sample(lv.cols)
            sponge.absorb()
            sponge.grind(17)
            sponge.sample(-(-t // per_word) + 1)
        words = c8.leaf_words(i, lv.k)
        cap = c8.merkle_cap_depth(t, depth)
        out["bytes"] += 16 + 4 * t + c8.expected_distinct(1 << depth, t) * 8 * words + 32 * c8.expected_siblings(depth, t)
        out["guest_keccak"] += t * (c8.leaf_perms(words) + depth - cap) + c8.expected_cap_hashes(cap, t)
        out["cycles"] += t * c8.guest_query_cycles(i, lv.k, depth - cap, lv.cols, final)
        if i == 0:
            total, h, _bits, table_perms = t71.twiddle_plan(depth, lv.cols, t)
            out["guest_keccak"] += t * h / 4 + table_perms
            out["cycles"] += t * (total - 2 * h - t71.FOLD_SAVED_PER_ROUND * lv.k - t71.HIGH_SAVED) - 8 * table_perms + tree.point_cycles()
    out["bytes"] += 16 * scalars
    out["guest_keccak"] += sponge.perms
    out["cycle_equiv"] = out["cycles"] + 8 * out["guest_keccak"]
    out["queries"], out["grind"], out["tau"] = [lv.queries for lv in levels], grind, float(tree.tau)
    return out


def main():
    if "--bestcap" in sys.argv:
        c8.merkle_cap_depth = p71.best_cap_depth
        print("cap rule retuned for every configuration\n")
    rng = lambda xs: f"{max(xs):+.1f} to {min(xs):+.1f}"
    for rate in (1, 2):
        print(f"\n**Rate 1/{1 << rate}: hybrid (tree code and DEEP fold at level 0, C after it), against C, in percent** (range over $\\mu = 24, 28, 30$)\n")
        print("| $L$ | $\\varepsilon$ | $\\tau$ | level-0 queries | KiB at $\\mu = 24, 28, 30$ | bytes | guest Keccak | guest cycle-eq | clear win |")
        print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
        for big_l in p71.LS:
            for eps in p71.EPS:
                by, ke, cy, qs, kib = [], [], [], [], []
                for mu in (24, 28, 30):
                    kn = recommend.config("C", mu)
                    base = m67.today_cost(mu, rate, kn)
                    h = hybrid(mu, rate, big_l, eps, kn)
                    by.append(100 * (h["bytes"] / base["bytes"] - 1))
                    ke.append(100 * (h["guest_keccak"] / base["guest_keccak"] - 1))
                    cy.append(100 * (h["cycle_equiv"] / base["cycle_equiv"] - 1))
                    qs.append(h["queries"][0])
                    kib.append(h["bytes"] / 1024)
                win = "yes" if max(by) < -10 and max(cy) <= 0 else ("bytes only" if max(by) < -10 else "no")
                print(f"| {big_l} | {int(eps * 64)}/64 | {h['tau']:.3f} | {qs[0]}, {qs[1]}, {qs[2]} | {kib[0]:.1f}, {kib[1]:.1f}, {kib[2]:.1f} | {rng(by)} | {rng(ke)} | {rng(cy)} | {win} |")


if __name__ == "__main__":
    main()
