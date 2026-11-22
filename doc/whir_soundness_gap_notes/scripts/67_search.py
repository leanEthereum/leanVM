#!/usr/bin/env python3
"""Note 67: search over the DEEP-fold ladders under proven list bounds (Johnson, shortened Johnson, counting).

For each (mu, rate) and each grind profile, every ladder with
  level 0: 2^k0 lanes, k0 in {4, 5, 6}; domain reduction after it in {3, 4};
  later levels: fold rounds in {3, 4, 5} (the last two levels also 2), leaves of at most 64 K words;
  later domain reductions 1 or 2 (one value a ladder), the last one also 0;
  final polynomial of 2^kappa + ell coefficients, kappa in 1..6, ell <= 2^kappa (S1);
is kept when its encoding stays within the budget of note 08's configuration C against today's deployment (NTT
work at most x1.05, committed words at most x1.05, Merkle permutations at most x1.15), then every level takes the
proven threshold with the least bytes (or the least guest cycle-equivalents).

The same ladders are evaluated for today's protocol (note 08's model), so that the two protocols are compared at
their own best ladder. By default the final polynomial is capped as today (kappa_last <= k0, the guest's rule
RESIDUAL_MAX_LOG <= INITIAL_FOLDING_FACTOR); `--free-residual` lifts the cap up to kappa_last = 6.

Usage: python3 67_search.py [--free-residual] [mu ...]
"""

from __future__ import annotations

import importlib.util
import os
import sys
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("m67", os.path.join(HERE, "67_model.py"))
m = importlib.util.module_from_spec(spec)
sys.modules["m67"] = m
spec.loader.exec_module(m)


def compositions(total, parts, last_parts, max_len=9):
    """Ordered sums of `total` with parts in `parts`, the last two taken from `last_parts`."""
    out = []

    def rec(rest, acc):
        if rest == 0:
            if all(p in parts for p in acc[:-2]) or len(acc) <= 2:
                out.append(tuple(acc))
            return
        if len(acc) == max_len:
            return
        for p in last_parts:
            if p <= rest:
                rec(rest - p, acc + [p])

    rec(total, [])
    return [c for c in out if all(p in parts for p in c[:-2])]


def ladders(mu):
    for k0 in (4, 5, 6):
        for residual in range(1, 7):
            rest = mu - k0 - residual
            for later in compositions(rest, (3, 4, 5), (2, 3, 4, 5)):
                if not later or later[-1] > (1 << residual):
                    continue
                folds = (k0,) + later
                for r0 in (3, 4):
                    if r0 > k0:
                        continue
                    for r in (1, 2):
                        for r_last in {r, 0}:
                            reds = (r0,) + (r,) * (len(later) - 2) + ((r_last,) if len(later) >= 2 else ())
                            reds = reds[: len(folds) - 1]
                            if any(red > k for red, k in zip(reds, folds)):
                                continue
                            yield folds, reds


def grind_profile(name, mu, n_levels):
    g0 = max(17, mu - 6) if name == "A" else 17
    return [g0] + [17] * (n_levels - 1)


def today_knobs(mu, folds, reds, profile):
    """Today's protocol on the same ladder; profile A is note 08's grinds (level-0 query grind, batch 14, OOD 16)."""
    g0 = max(17, mu - 6)
    extra = dict(g_query_levels=((0, g0),), g_batch=14, g_ood=16) if profile == "A" else {}
    return m.wm.with_knobs(
        initial_fold=folds[0],
        initial_reduction=reds[0],
        residual_max=mu - sum(folds),
        fold_levels=tuple((i, k) for i, k in enumerate(folds) if i >= 1),
        reduction_levels=tuple(enumerate(reds)),
        **extra,
    )


def evaluate(args):
    mu, rate, profile, folds, reds = args
    shp = m.shape(mu, rate, list(folds), list(reds))
    gq = grind_profile(profile, mu, len(shp))
    rows = {}
    for objective in ("bytes", "cycles"):
        lv = m.build(shp, gq, sched="ladder", objective=objective)
        c = m.cost(lv)
        rows["deep-" + objective] = (c["bytes"], c["cycle_equiv"], c["guest_keccak"], c["queries"], c["points"], [x.source for x in lv], m.point_prover_share(lv, mu, rate))
    kn = today_knobs(mu, folds, reds, profile)
    if m.wm.ladder(mu, rate, kn) is not None and m.wm.derive(mu, rate, kn) is not None:
        c = m.today_cost(mu, rate, kn)
        rows["today"] = (c["bytes"], c["cycle_equiv"], c["guest_keccak"], c["queries"], [], [], 0.0)
    return rows


def show(tag, job, r, base):
    return (
        f"  {tag}: folds {job[3]} reductions {job[4]}: {r[0] / 1024:.1f} KiB ({100 * (r[0] / base['bytes'] - 1):+.1f}%), {r[1] / 1000:.1f}k cycle-eq"
        f" ({100 * (r[1] / base['cycle_equiv'] - 1):+.1f}%), Keccak {r[2]:.0f}, queries {r[3]}"
        + (f", points {r[4]}, lists {r[5]}, points {r[6]:.1f}% of Prove" if r[4] else "")
    )


def main():
    free = "--free-residual" in sys.argv
    mus = [int(x) for x in sys.argv[1:] if x.isdigit()] or [24, 28, 30]
    print(f"residual constraint: {'none' if free else 'final polynomial of at most 2^k0 + ell coefficients (kappa_last <= k0), as today'}")
    for mu in mus:
        for rate in (1, 2):
            base = m.today_cost(mu, rate)
            w0, n0, p0 = base["encoding"]
            jobs = []
            for folds, reds in sorted(set(ladders(mu))):
                if not free and mu - sum(folds) > folds[0]:
                    continue
                w, n, p = m.encoding(m.shape(mu, rate, list(folds), list(reds)))
                if w <= 1.05 * w0 and n <= 1.05 * n0 and p <= 1.15 * p0:
                    jobs += [(mu, rate, profile, folds, reds) for profile in ("std", "A")]
            with Pool(4) as pool:
                res = pool.map(evaluate, jobs, chunksize=32)
            print(f"\n## mu = {mu}, rate 1/{1 << rate}: {len(jobs) // 2} ladders within the encoding budget; today {base['bytes'] / 1024:.1f} KiB, {base['cycle_equiv'] / 1000:.1f}k cycle-equivalents")
            for profile in ("std", "A"):
                print(f"query grinds {profile}:")
                for kind, col, top in (("today", 0, 2), ("today", 1, 2), ("deep-bytes", 0, 3), ("deep-cycles", 1, 3)):
                    rows = [(job, rr[kind]) for job, rr in zip(jobs, res) if job[2] == profile and kind in rr]
                    rows.sort(key=lambda x: x[1][col])
                    label = {"today": "today's protocol", "deep-bytes": "DEEP, proven lists", "deep-cycles": "DEEP, proven lists"}[kind] + (", least bytes" if col == 0 else ", least cycle-eq")
                    for job, r in rows[:top]:
                        print(show(label, job, r, base))


if __name__ == "__main__":
    main()
