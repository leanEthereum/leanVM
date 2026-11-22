#!/usr/bin/env python3
"""Note 71, section 5: the opening with a random tree code at level 0 (DEEP fold, scalar fold at level 0), against
today's protocol and note 08's configuration C. Prints markdown. Usage: python3 71_payoff.py [--points] [--full]

Levels 1 and later are note 67's best proven DEEP-fold levels (Reed-Solomon, affine fold, ladder schedules).
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("t71", os.path.join(HERE, "71_tree_level.py"))
t71 = importlib.util.module_from_spec(spec)
sys.modules["t71"] = t71
spec.loader.exec_module(t71)
m67, c8 = t71.m67, t71.c8
import recommend  # noqa: E402  (08_retuning, on the path through 67_model)


class TreeLevel:
    index, final = 0, False

    def __init__(self, rate, cols, k, big_l, eps, g_query, g_fold=12, g_point=15, sched="ladder", point="tensor"):
        self.log_inv_rate, self.cols, self.k, self.g_query, self.g_fold = rate, cols, k, g_query, g_fold
        self.log_block, self.list_size = cols + rate, big_l
        n, mu = 1 << self.log_block, cols + k
        self.tau = (1 + big_l * Fraction(1, 1 << rate)) / (big_l + 1) + eps
        self.loss = max(-(-n >> (g_fold + 1)) - 1, 0)  # columns of agreement lost a round
        self.a_end = math.ceil(self.tau * n) + k * self.loss
        blocks = -(-mu // 8)
        self.per_point = mu if point == "multilinear" else blocks  # challenges a point
        e = mu if point == "multilinear" else blocks * 256
        self.sbar = t71.ladder(big_l, e, k, g_point, g_fold) if sched == "ladder" else (t71.one_batch(big_l, e, k, g_point, g_fold),) * k
        self.points = self.sbar[-1]
        self.queries = m67.query_count(self.log_block, self.a_end, self.points, g_query, False) if self.a_end < n else None

    def point_cycles(self):
        """As note 67's count (two cycles a product, 20 a point): one product a held point a round, the squarings
        that expand a point, and the weight at the terminal point."""
        per = (self.cols + self.k) + 2 * self.cols + 1
        return 2 * (sum(self.sbar) + self.points * per) + 20 * self.points


def cost(levels, g_point=15, g_fold=7, g_batch=7):
    """`67_model.cost` with a tree level 0: two scalars and one challenge a round, no high part, twiddles."""
    sponge, n_levels, lv0 = c8.SpongeCount(), len(levels), levels[0]
    tree = isinstance(lv0, TreeLevel)
    first = lv0.sbar[0]
    scalars = 3 + first
    sponge.absorb(2)
    sponge.grind(g_point)
    sponge.sample((lv0.per_point if tree else 2) * first)
    sponge.absorb(first)
    scalars += 1
    sponge.grind(g_batch)
    sponge.sample()
    grind = n_levels * (1 << g_point) + (1 << g_batch)
    merkle_bytes = guest_keccak = query_cycles = point_cycles = 0.0
    native_keccak = 0
    for i, lv in enumerate(levels):
        is_tree = tree and i == 0
        sent, chal, cpp, gf = (2, 1, lv.per_point, lv.g_fold) if is_tree else (4, 2, 2, g_fold)
        depth, t = lv.log_block, lv.queries
        for j in range(lv.k):
            fresh = lv.sbar[j] - lv.sbar[j - 1] if j else 0
            scalars += fresh + sent + lv.sbar[j] + 1
            sponge.absorb(fresh + sent + lv.sbar[j])
            sponge.grind(gf)
            sponge.sample(chal + cpp * (lv.sbar[j + 1] - lv.sbar[j] if j + 1 < lv.k else 0))
        grind += lv.k * (1 << gf) + (1 << lv.g_query)
        per_word = 128 // depth
        if lv.final:
            n_final = (1 << lv.cols) + lv.k
            scalars += n_final + 1 + 2 * lv.cols
            sponge.absorb(n_final)
            sponge.grind(lv.g_query)
            sponge.sample(-(-t // per_word))
            for _ in range(lv.cols):
                sponge.absorb(2)
                sponge.sample()
        else:
            s_next, high = levels[i + 1].sbar[0], (0 if is_tree else lv.k)
            scalars += 2 + high + 1 + s_next + 1
            sponge.absorb(2 + high)
            sponge.grind(g_point)
            sponge.sample(2 * s_next)
            sponge.absorb(s_next)
            sponge.grind(lv.g_query)
            sponge.sample(-(-t // per_word) + 1)
        words = c8.leaf_words(i, lv.k)
        perms = c8.leaf_perms(words)
        merkle_bytes += 16 + 4 * t + c8.expected_distinct(1 << depth, t) * 8 * words + c8.DIGEST * c8.expected_siblings(depth, t)
        cap = c8.merkle_cap_depth(t, depth)
        guest_keccak += t * (perms + depth - cap) + c8.expected_cap_hashes(cap, t)
        native_keccak += t * (perms + depth)
        query_cycles += t * c8.guest_query_cycles(i, lv.k, depth - cap, lv.cols, lv.final)
        if is_tree:
            total, h, bits, table_perms = t71.twiddle_plan(depth, lv.cols, t)
            guest_keccak += t * h / 4 + table_perms
            native_keccak += t * -(-lv.cols // 4)
            query_cycles += t * (total - 2 * h - t71.FOLD_SAVED_PER_ROUND * lv.k - t71.HIGH_SAVED) - 8 * table_perms
            lv.hashed, lv.table_bits = h, bits
        point_cycles += lv.point_cycles()
    guest_keccak += sponge.perms
    return {"bytes": merkle_bytes + 16 * scalars, "guest_keccak": guest_keccak, "native_keccak": native_keccak + sponge.perms,
            "cycle_equiv": query_cycles + point_cycles + 8 * guest_keccak, "grind": grind,
            "queries": [lv.queries for lv in levels], "points": [lv.points for lv in levels]}


LS, EPS = (2, 3, 4, 8, 16), (Fraction(1, 64), Fraction(2, 64), Fraction(4, 64))


def shapes(mu, rate):
    g0 = max(17, mu - 6)
    dep = m67.deployed_shape(mu, rate)
    cs = m67.deployed_shape(mu, rate, recommend.config("C", mu))
    return (dep, [17] * len(dep)), (cs, [g0] + [17] * (len(cs) - 1))


def tree_cost(shape, gq, big_l, eps, **kw):
    lv = m67.build(shape, gq, sched="ladder", objective="bytes")
    r, c, k = shape[0]
    lv[0] = TreeLevel(r, c, k, big_l, eps, gq[0], **kw)
    return None if lv[0].queries is None else (cost(lv), lv)


def selftest():
    """With a Reed-Solomon level 0 this cost function must equal note 67's."""
    for mu, rate in ((24, 1), (30, 2)):
        for shape, gq in shapes(mu, rate):
            lv = m67.build(shape, gq, sched="ladder", objective="bytes")
            a, b = cost(lv), m67.cost(lv)
            assert abs(a["bytes"] - b["bytes"]) < 1e-6 and abs(a["guest_keccak"] - b["guest_keccak"]) < 1e-6
            assert abs(a["cycle_equiv"] - b["cycle_equiv"]) < 1e-6 and a["grind"] == b["grind"]
    print("selftest passed: the cost function reproduces 67_model.cost on Reed-Solomon levels\n")


def points_table():
    print("| $\\mu$ | RS DEEP level 0, one batch ($L = 2^7$, $2^{40}$; fold grind 7) | tree, multilinear points | tree, tensor-power points (4 challenges) | same, ladder |")
    print("| --- | --- | --- | --- | --- |")
    for mu in (24, 28, 30):
        d = (1 << (mu - 6)) + 5
        rs = [m67.one_batch(1 << b, d, 6) for b in (7, 40)]
        ml = [t71.one_batch(big_l, mu, 6, 15, 12) for big_l in (2, 16, 1 << 20)]
        tp = [t71.one_batch(big_l, -(-mu // 8) * 256, 6, 15, 12) for big_l in (2, 16, 1 << 20)]
        lad = t71.ladder(16, -(-mu // 8) * 256, 6, 15, 12)
        print(f"| {mu} | {rs[0]}, {rs[1]} | {ml} for $L = 2, 16, 2^{{20}}$ | {tp} | {lad} at $L = 16$ |")


def row(c, base):
    return f"{c['bytes'] / 1024:.1f} ({100 * (c['bytes'] / base['bytes'] - 1):+.1f}%) | {c['guest_keccak']:.0f} | {c['cycle_equiv'] / 1000:.1f}k ({100 * (c['cycle_equiv'] / base['cycle_equiv'] - 1):+.1f}%)"


def table(mu, rate):
    (dep, gq_dep), (cs, gq_c) = shapes(mu, rate)
    today, conf_c = m67.today_cost(mu, rate), m67.today_cost(mu, rate, recommend.config("C", mu))
    print(f"\n**$\\mu = {mu}$, rate 1/{1 << rate}.** Today: {today['queries'][0]} level-0 queries, {today['bytes'] / 1024:.1f} KiB, {today['guest_keccak']:.0f} Keccak, {today['cycle_equiv'] / 1000:.1f}k cycle-eq."
          f" C: {conf_c['queries'][0]} queries, {conf_c['bytes'] / 1024:.1f} KiB, {conf_c['guest_keccak']:.0f} Keccak, {conf_c['cycle_equiv'] / 1000:.1f}k cycle-eq. Percentages are against C.\n")
    print("| $L$ | $\\varepsilon$ | $\\tau$ | $q_0$ alone | alone: KiB | Keccak | cycle-eq | $q_0$ with C | with C's knobs: KiB | Keccak | cycle-eq |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    out = []
    for big_l in LS:
        for eps in EPS:
            a, b = tree_cost(dep, gq_dep, big_l, eps), tree_cost(cs, gq_c, big_l, eps)
            if a is None or b is None:
                continue
            tau = float(b[1][0].tau)
            print(f"| {big_l} | {int(eps * 64)}/64 | {tau:.3f} | {a[0]['queries'][0]} | {row(a[0], conf_c)} | {b[0]['queries'][0]} | {row(b[0], conf_c)} |")
            out.append((big_l, eps, tau, a[0], b[0], conf_c, today))
    return out


def best_cap_depth(queries, depth):
    """The cap rule with its noise removed: among the cap depths 2 to 8 that leave a path of whole windows (the
    deployed rule's range), the one that costs the guest least, at 8 cycle-equivalents a KECCAK step, 3.85 walk
    cycles a path level and 2 cycles a cap node for the flags. It differs from the deployed rule only where the
    tree depth is 2 modulo 6, where both 2 and 8 qualify and the deployed rule switches at 128 queries."""
    caps = [c for c in range(2, min(depth, 8) + 1) if (depth - c) % c8.QUERY_WINDOW_BITS == 0]
    return min(caps, key=lambda c: queries * (depth - c) * 11.85 + 9 * c8.expected_cap_hashes(c, queries) + 2 * (1 << c))


def summary():
    """Bytes and cycle-equivalents against C, alone and with C's knobs, one line per (L, eps): the range over the
    sizes. A clear win: more than ten percent below C on bytes at every size, and the guest not slower at any."""
    rng = lambda xs: f"{max(xs):+.1f} to {min(xs):+.1f}"
    for rate in (1, 2):
        print(f"\n**Rate 1/{1 << rate}, against C, in percent** (range over $\\mu = 24, 28, 30$)\n")
        print("| $L$ | $\\varepsilon$ | $\\tau$ | alone: bytes | alone: guest cycle-eq | with C's knobs: level-0 queries | bytes | guest cycle-eq | clear win |")
        print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
        for big_l in LS:
            for eps in EPS:
                cols = {0: ([], []), 1: ([], [])}
                qs, tau = [], None
                for mu in (24, 28, 30):
                    conf_c = m67.today_cost(mu, rate, recommend.config("C", mu))
                    for which, (shape, gq) in enumerate(shapes(mu, rate)):
                        c, lv = tree_cost(shape, gq, big_l, eps)
                        cols[which][0].append(100 * (c["bytes"] / conf_c["bytes"] - 1))
                        cols[which][1].append(100 * (c["cycle_equiv"] / conf_c["cycle_equiv"] - 1))
                        if which:
                            qs.append(c["queries"][0])
                            tau = float(lv[0].tau)
                by, cy = cols[1]
                win = "yes" if max(by) < -10 and max(cy) <= 0 else ("bytes only" if max(by) < -10 else "no")
                print(f"| {big_l} | {int(eps * 64)}/64 | {tau:.3f} | {rng(cols[0][0])} | {rng(cols[0][1])} | {qs[0]}, {qs[1]}, {qs[2]} | {rng(by)} | {rng(cy)} | {win} |")


if __name__ == "__main__":
    if "--bestcap" in sys.argv:
        c8.merkle_cap_depth = best_cap_depth
        print("cap rule: the best cap depth for each level and configuration (today and C included)\n")
    else:
        selftest()
    if "--points" in sys.argv:
        points_table()
    elif "--summary" in sys.argv:
        summary()
    else:
        for mu in (24, 28, 30):
            for rate in (1, 2):
                table(mu, rate)
