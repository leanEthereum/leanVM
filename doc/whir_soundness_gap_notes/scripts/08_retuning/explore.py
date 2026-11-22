"""Knob sweeps and Pareto fronts over the validated model (researcher 08).

Usage:
  python3 explore.py sweeps            one-knob sweeps around the deployed configuration
  python3 explore.py pareto [OUT.json] the full grid for mu in {20, 24, 28, 30} and rates 1..4 (about 4 cores)
  python3 explore.py slack             the analysis-slack variants of the note's section 4
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import costs
import whir_model as wm

GRIND_RATE = 15.0e6  # Keccak-f per second of the grind kernel on one core: a calibration input, see the note


def metrics(mu, rate, kn, fill=1.0):
    cfg = wm.derive(mu, rate, kn, faithful=True)
    if cfg is None:
        return None
    c = costs.cost(cfg, fill)
    flags = []
    if any(costs.leaf_words(i, lv.k) > 64 for i, lv in enumerate(cfg.levels)):
        flags.append("leaf>64w")
    if max(cfg.queries) > 256:
        flags.append("queries>256")
    if cfg.residual > kn.initial_fold:
        flags.append("residual>k0")
    return {
        "queries": cfg.queries,
        "lists": [lv.list_bound for lv in cfg.levels],
        "rates": [lv.log_inv_rate for lv in cfg.levels],
        "folds": [lv.k for lv in cfg.levels],
        "residual": cfg.residual,
        "bytes": c.proof_bytes,
        "guest_keccak": c.guest_keccak,
        "native_keccak": c.native_keccak,
        "guest_keccak_cap8": c.guest_keccak_cap8,
        "guest_cycles": c.guest_cycles,
        "grind": c.grind_perms,
        "grind_max_bits": c.grind_max_bits,
        "encode_words": c.encode_words,
        "encode_ntt": c.encode_ntt,
        "commit_perms": c.commit_perms,
        "flags": flags,
    }


def fmt(m, base=None):
    s = f"q={m['queries']} {m['bytes'] / 1024:7.1f} KiB  keccak {m['guest_keccak']:6.0f}  cycles~{m['guest_cycles'] / 1000:6.1f}k  grind 2^{math.log2(m['grind']):5.2f}"
    if base:
        s += (
            f"  | bytes {100 * (m['bytes'] / base['bytes'] - 1):+5.1f}%  keccak {100 * (m['guest_keccak'] / base['guest_keccak'] - 1):+5.1f}%"
            f"  cycles {100 * (m['guest_cycles'] / base['guest_cycles'] - 1):+5.1f}%"
            f"  enc x{m['encode_ntt'] / base['encode_ntt']:.2f}  merkle x{m['commit_perms'] / base['commit_perms']:.2f}"
        )
    if m["flags"]:
        s += "  [" + ",".join(m["flags"]) + "]"
    return s


def kdesc(kn):
    d = wm.DEPLOYED
    parts = []
    for name in ("initial_fold", "initial_reduction", "sub_fold", "sub_reduction", "residual_max", "g_query", "g_fold", "g_batch", "g_ood", "g_query_levels", "max_list_0"):
        if getattr(kn, name) != getattr(d, name):
            parts.append(f"{name}={getattr(kn, name)}")
    return " ".join(parts) or "deployed"


def sweeps():
    for mu, rate in [(30, 1), (24, 1), (30, 2), (24, 2), (30, 4)]:
        base = metrics(mu, rate, wm.DEPLOYED)
        print(f"\n===== mu={mu} rate=2^-{rate}: deployed {fmt(base)}")
        print("-- query grind, every level")
        for g in (18, 19, 20, 21, 22, 24, 26, 28, 30, 32):
            print(f"  g_query={g:2d}: {fmt(metrics(mu, rate, wm.with_knobs(g_query=g)), base)}")
        print("-- query grind, level 0 only (later levels at 17)")
        for g in (20, 22, 24, 26, 28, 30, 32):
            print(f"  L0={g:2d}: {fmt(metrics(mu, rate, wm.with_knobs(g_query_levels=((0, g),))), base)}")
        print("-- OOD grind (with the fold grind that it needs), list caps of later levels")
        for g_ood, g_fold in [(15, 7), (17, 8), (19, 9), (21, 10), (23, 11), (27, 13), (31, 15), (35, 17)]:
            m = metrics(mu, rate, wm.with_knobs(g_ood=g_ood, g_fold=g_fold))
            print(f"  g_ood={g_ood} g_fold={g_fold}: lists {m['lists']} {fmt(m, base)}")
        print("-- fold grind alone")
        for g_fold in (5, 6, 7, 8, 10, 14):
            m = metrics(mu, rate, wm.with_knobs(g_fold=g_fold))
            print(f"  g_fold={g_fold}: " + (f"lists {m['lists']} {fmt(m, base)}" if m else "infeasible"))
        print("-- batching grind and level 0's list cap")
        for g_batch, cap, g_ood, g_fold in [(12, 166, 15, 7), (13, 166, 15, 7), (14, 166, 16, 7), (16, 512, 19, 9), (20, 8192, 27, 13), (24, 1 << 17, 35, 17)]:
            m = metrics(mu, rate, wm.with_knobs(g_batch=g_batch, max_list_0=cap, g_ood=g_ood, g_fold=g_fold))
            print(f"  g_batch={g_batch} max_list_0={cap} g_ood={g_ood} g_fold={g_fold}: " + (f"lists {m['lists']} {fmt(m, base)}" if m else "infeasible"))
        print("-- level 0 fold (lanes) and the domain reduction after it")
        for k0 in (3, 4, 5, 6, 7, 8):
            for r0 in range(1, k0 + 1):
                m = metrics(mu, rate, wm.with_knobs(initial_fold=k0, initial_reduction=r0, residual_max=min(5, k0)))
                if m:
                    print(f"  k0={k0} r0={r0}: {fmt(m, base)}")
        print("-- later folds and their domain reduction")
        for ks in (2, 3, 4, 5, 6):
            for rs in range(0, ks + 1):
                m = metrics(mu, rate, wm.with_knobs(sub_fold=ks, sub_reduction=rs))
                if m:
                    print(f"  ks={ks} rs={rs}: {fmt(m, base)}")
        print("-- residual")
        for res in (2, 3, 4, 5, 6, 7, 8, 9, 10):
            m = metrics(mu, rate, wm.with_knobs(residual_max=res))
            if m:
                print(f"  residual_max={res} (residual {m['residual']}): {fmt(m, base)}")


# ---------------------------------------------------------------------------------------------------------------
# Pareto
# ---------------------------------------------------------------------------------------------------------------

def _profiles():
    """name -> (g_query, per-level overrides, g_fold, g_batch, g_ood). MAX_LIST_0 stays 166."""
    out = {"deployed": (17, (), 7, 13, 15), "lists166": (17, (), 7, 14, 16)}
    for g in (19, 20, 21, 22, 23, 24, 26, 28):
        out[f"L0={g}"] = (17, ((0, g),), 7, 13, 15)
    for g in (20, 22, 24):
        out[f"L0={g}+lists166"] = (17, ((0, g),), 7, 14, 16)
    out["L0=22,L1=19"] = (17, ((0, 22), (1, 19)), 7, 13, 15)
    out["L0=24,L1=20"] = (17, ((0, 24), (1, 20)), 7, 13, 15)
    out["all=20"] = (20, (), 7, 13, 15)
    out["all=24"] = (24, (), 7, 13, 15)
    return out


GRIND_PROFILES = _profiles()


def profile_knobs(name, **shape):
    gq, levels, g_fold, g_batch, g_ood = GRIND_PROFILES[name]
    return wm.with_knobs(g_query=gq, g_query_levels=levels, g_fold=g_fold, g_batch=g_batch, g_ood=g_ood, **shape)


def shapes():
    for k0 in (4, 5, 6, 7):
        for r0 in range(1, min(k0, 5) + 1):
            for ks in (3, 4, 5):
                for rs in (0, 1, 2):
                    yield dict(initial_fold=k0, initial_reduction=r0, sub_fold=ks, sub_reduction=rs, residual_max=min(5, k0))


def _eval(args):
    mu, rate, name, shape = args
    kn = profile_knobs(name, **shape)
    m = metrics(mu, rate, kn)
    return (mu, rate, name, shape, m)


def pareto(out_path):
    work = [(mu, rate, name, shape) for mu in (20, 24, 28, 30) for rate in (1, 2, 3, 4) for shape in shapes() for name in GRIND_PROFILES]
    # Group by shape so that a worker's level cache serves every grind profile of a shape.
    t = time.time()
    rows = []
    with Pool(4) as pool:
        for i, (mu, rate, name, shape, m) in enumerate(pool.imap(_eval, work, chunksize=len(GRIND_PROFILES))):
            if m is not None:
                rows.append({"mu": mu, "rate": rate, "profile": name, "shape": shape, **m})
            if i % 2000 == 0:
                print(f"{i}/{len(work)} {time.time() - t:.0f}s", flush=True)
    json.dump(rows, open(out_path, "w"))
    print(f"{len(rows)} feasible of {len(work)} in {time.time() - t:.0f}s -> {out_path}")


def slack():
    variants = [
        ("deployed", wm.DEPLOYED),
        ("no degree slack (d = 2^kappa - 1)", wm.with_knobs(no_degree_slack=True)),
        ("no per-round loss (A_j = A)", wm.with_knobs(no_round_loss=True)),
        ("both", wm.with_knobs(no_degree_slack=True, no_round_loss=True)),
        ("no u128 conservatism", wm.with_knobs(exact_wide=True)),
        ("multiplicity up to 2^22", wm.with_knobs(max_multiplicity=1 << 22, exact_wide=True)),
        ("unlimited fold grind", wm.with_knobs(g_fold=125)),
    ]
    for rate in (1, 2, 3, 4):
        for mu in (16, 18, 20, 22, 24, 26, 28, 30):
            base = wm.derive(mu, rate)
            print(f"rate=2^-{rate} mu={mu}: Johnson limit {wm.johnson_limit_queries(base)}")
            for name, kn in variants:
                cfg = wm.derive(mu, rate, kn, faithful=True)
                print(f"    {name:36s} {cfg.queries if cfg else None}  lists {[lv.list_bound for lv in cfg.levels] if cfg else None}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "sweeps"
    if cmd == "sweeps":
        sweeps()
    elif cmd == "pareto":
        pareto(sys.argv[2] if len(sys.argv) > 2 else "pareto.json")
    elif cmd == "slack":
        slack()
