"""Pareto fronts from explore.py's grid (researcher 08).

Usage: python3 fronts.py PARETO.json
Per stacked size and rate: the deployed row, the size of the four-objective front (proof bytes, guest Keccak,
expected grind permutations, encoding work), and the best configurations under a few prover budgets.
"""

import json
import math
import sys

OBJ = ("bytes", "guest_keccak", "grind", "encode_ntt")
REC_KECCAK_WEIGHT = 8.0  # proving time of one KECCAK step in ordinary cycles, read off one recursion trace (see the note)


def rec(r):
    return r["guest_cycles"] + REC_KECCAK_WEIGHT * r["guest_keccak"]


def front(rows, objectives=OBJ):
    pts = sorted(rows, key=lambda r: tuple(r[k] for k in objectives))
    keep = []
    for r in pts:
        if not any(all(o[k] <= r[k] for k in objectives) and any(o[k] < r[k] for k in objectives) for o in keep):
            keep = [o for o in keep if not (all(r[k] <= o[k] for k in objectives) and any(r[k] < o[k] for k in objectives))]
            keep.append(r)
    return keep


def shape_str(s):
    return f"k0={s['initial_fold']} r0={s['initial_reduction']} ks={s['sub_fold']} rs={s['sub_reduction']}"


def row_str(r, base):
    pct = lambda k: 100 * (r[k] / base[k] - 1)
    return (
        f"{shape_str(r['shape']):22s} {r['profile']:16s} q={str(r['queries']):34s} {r['bytes'] / 1024:6.1f} KiB ({pct('bytes'):+5.1f}%)"
        f" keccak {r['guest_keccak']:5.0f} ({pct('guest_keccak'):+5.1f}%) cycles~{r['guest_cycles'] / 1000:5.1f}k ({pct('guest_cycles'):+5.1f}%)"
        f" rec ({100 * (rec(r) / rec(base) - 1):+5.1f}%) grind 2^{math.log2(r['grind']):5.2f} enc x{r['encode_ntt'] / base['encode_ntt']:.2f}"
        f" merkle x{r['commit_perms'] / base['commit_perms']:.2f}" + (" [" + ",".join(r["flags"]) + "]" if r["flags"] else "")
    )


def main(path):
    rows = json.load(open(path))
    for mu in (20, 24, 28, 30):
        for rate in (1, 2, 3, 4):
            sub = [r for r in rows if r["mu"] == mu and r["rate"] == rate]
            base = next(r for r in sub if r["profile"] == "deployed" and shape_str(r["shape"]) == "k0=6 r0=3 ks=4 rs=1")
            f = front(sub)
            print(f"\n===== mu={mu} rate=2^-{rate}: {len(sub)} configurations, front of {len(f)}")
            print("  today      " + row_str(base, base))
            budgets = [
                ("same shape, grind <= 2^(mu-6)+today", lambda r: shape_str(r["shape"]) == "k0=6 r0=3 ks=4 rs=1" and r["grind"] <= base["grind"] + 2 ** max(mu - 6, 17) + 2**18),
                ("enc <= 1.05, today's grind", lambda r: r["encode_ntt"] <= 1.05 * base["encode_ntt"] and r["grind"] <= base["grind"] * 1.3 and not r["flags"]),
                ("enc <= 1.05, grind <= 2^(mu-6)+today", lambda r: r["encode_ntt"] <= 1.05 * base["encode_ntt"] and r["grind"] <= base["grind"] + 2 ** max(mu - 6, 17) + 2**18 and not r["flags"]),
                ("enc <= 1.40, grind <= 2^(mu-6)+today", lambda r: r["encode_ntt"] <= 1.40 * base["encode_ntt"] and r["grind"] <= base["grind"] + 2 ** max(mu - 6, 17) + 2**18 and not r["flags"]),
            ]
            for name, ok in budgets:
                cand = [r for r in f if ok(r)]
                if not cand:
                    cand = [r for r in sub if ok(r)]
                print(f"  -- {name}")
                for key, label in (("bytes", "min bytes "), ("guest_keccak", "min keccak"), (None, "min rec   ")):
                    best = min(cand, key=(lambda r: rec(r)) if key is None else (lambda r: r[key]))
                    print(f"     {label} " + row_str(best, base))


if __name__ == "__main__":
    main(sys.argv[1])
