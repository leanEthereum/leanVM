#!/usr/bin/env python3
"""Note 71: the compact payoff table of the summary. With C's knobs, DEEP fold at every level and the hybrid of
section 5.4, against C; absolute numbers for today and C. Deployed cap rule. Usage: python3 71_final_table.py"""

import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("h71", os.path.join(HERE, "71_hybrid.py"))
h71 = importlib.util.module_from_spec(spec)
sys.modules["h71"] = h71
spec.loader.exec_module(h71)
p71, m67, recommend = h71.p71, h71.m67, h71.recommend
MUS = (24, 28, 30)

print("| rate | config | $\\mu = 24$ | $\\mu = 28$ | $\\mu = 30$ |")
print("| --- | --- | --- | --- | --- |")
for rate in (1, 2):
    for name, key in (("today", "today"), ("C", "C")):
        cells = []
        for mu in MUS:
            c = m67.today_cost(mu, rate, recommend.config(key, mu))
            cells.append(f"{c['bytes'] / 1024:.1f} KiB, {c['guest_keccak']:.0f} Keccak, {c['cycle_equiv'] / 1000:.1f}k")
        print(f"| 1/{1 << rate} | {name} | " + " | ".join(cells) + " |")
rng = lambda xs: f"{max(xs):+.0f} to {min(xs):+.0f}"
for rate in (1, 2):
    print(f"\n**Rate 1/{1 << rate}** (tree code with C's knobs; KiB, Keccak, cycle-eq in thousands at $\\mu = 24, 28, 30$; percent against C)\n")
    print("| $L$ | $\\varepsilon$ | $\\tau$ | $q_0$ | DEEP at every level: KiB | Keccak | cycle-eq | bytes % | guest % | hybrid: KiB | bytes % | guest % | clear win (DEEP / hybrid) |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for big_l in p71.LS:
        for eps in p71.EPS:
            d, h, by, cy, hby, hcy = [], [], [], [], [], []
            for mu in MUS:
                kn = recommend.config("C", mu)
                base = m67.today_cost(mu, rate, kn)
                _dep, (cs, gq) = p71.shapes(mu, rate)
                c, lv = p71.tree_cost(cs, gq, big_l, eps)
                hy = h71.hybrid(mu, rate, big_l, eps, kn)
                d.append(c)
                h.append(hy)
                by.append(100 * (c["bytes"] / base["bytes"] - 1))
                cy.append(100 * (c["cycle_equiv"] / base["cycle_equiv"] - 1))
                hby.append(100 * (hy["bytes"] / base["bytes"] - 1))
                hcy.append(100 * (hy["cycle_equiv"] / base["cycle_equiv"] - 1))
            win = lambda b, c: "yes" if max(b) < -10 and max(c) <= 0 else ("bytes" if max(b) < -10 else "no")
            j = lambda f: ", ".join(f(x) for x in d)
            print(f"| {big_l} | {int(eps * 64)}/64 | {float(lv[0].tau):.3f} | {j(lambda x: str(x['queries'][0]))} | {j(lambda x: f'{x['bytes'] / 1024:.1f}')} | {j(lambda x: f'{x['guest_keccak']:.0f}')}"
                  f" | {j(lambda x: f'{x['cycle_equiv'] / 1000:.1f}')} | {rng(by)} | {rng(cy)} | {', '.join(f'{x['bytes'] / 1024:.1f}' for x in h)} | {rng(hby)} | {rng(hcy)} | {win(by, cy)} / {win(hby, hcy)} |")
