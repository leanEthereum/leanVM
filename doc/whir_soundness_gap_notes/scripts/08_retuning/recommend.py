"""The recommended configurations next to the deployed one (researcher 08).

Usage: python3 recommend.py [--fill F] [--markdown]
A: the deployed ladder with RESIDUAL_MAX_LOG = 6, a size-scaled level-0 query grind, max(17, mu - 6) bits, and the
   list grinds at MAX_LIST_0 (batch 14, OOD 16).
B: 32 lanes at level 0 (INITIAL_FOLDING_FACTOR = 5), every grind as deployed.
C: A and B together.
D: (rate 1/4 only, printed with --extra) the domain reduction after level 0 raised to 4.
"""

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import costs
import explore
import whir_model as wm


def config(name, mu):
    g0 = max(17, mu - 6)
    grind = dict(g_query_levels=((0, g0),), g_batch=14, g_ood=16)
    lanes = dict(initial_fold=5, initial_reduction=3, residual_max=5)
    return {"today": wm.DEPLOYED, "A": wm.with_knobs(residual_max=6, **grind), "B": wm.with_knobs(**lanes), "C": wm.with_knobs(**grind, **lanes)}[name]


def main():
    fill = float(sys.argv[sys.argv.index("--fill") + 1]) if "--fill" in sys.argv else 1.0
    mus = (20, 24, 26, 28, 30)
    print(f"fill = {fill}; grind seconds are single-threaded at {explore.GRIND_RATE / 1e6:.0f} M permutations/s\n")
    print("| mu | rate | config | queries per level | WHIR bytes (KiB) | guest Keccak | guest Keccak, cap 8 | native Keccak | guest query cycles (est.) | grind perms (log2) | grind s (1 thread) | NTT work | Merkle perms |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for mu in mus:
        for rate in (1, 2, 3, 4):
            base = explore.metrics(mu, rate, wm.DEPLOYED, fill)
            for name in ("today", "A", "B", "C"):
                m = explore.metrics(mu, rate, config(name, mu), fill)
                pct = lambda k: "" if name == "today" else f" ({100 * (m[k] / base[k] - 1):+.1f}%)"
                print(
                    f"| {mu} | 1/{1 << rate} | {name} | {' '.join(map(str, m['queries']))} | {m['bytes'] / 1024:.1f}{pct('bytes')} | {m['guest_keccak']:.0f}{pct('guest_keccak')}"
                    f" | {m['guest_keccak_cap8']:.0f}{pct('guest_keccak_cap8')} | {m['native_keccak']}{pct('native_keccak')}"
                    f" | {m['guest_cycles'] / 1000:.1f}k{pct('guest_cycles')} | {math.log2(m['grind']):.2f} | {m['grind'] / explore.GRIND_RATE:.3f}"
                    f" | x{m['encode_ntt'] / base['encode_ntt']:.2f} | x{m['commit_perms'] / base['commit_perms']:.2f} |"
                )
    if "--extra" in sys.argv:
        print("\nD: rate 1/4 at level 0 with the later levels of rate 1/2 (RS_DOMAIN_INITIAL_REDUCTION_FACTOR = 4), against deployed rate 1/2 and 1/4")
        for mu in mus:
            b1 = explore.metrics(mu, 1, wm.DEPLOYED, fill)
            b2 = explore.metrics(mu, 2, wm.DEPLOYED, fill)
            d = explore.metrics(mu, 2, wm.with_knobs(initial_reduction=4), fill)
            for name, m in (("rate 1/2", b1), ("D", d), ("rate 1/4", b2)):
                print(f"| {mu} | {name} | {' '.join(map(str, m['queries']))} | {m['bytes'] / 1024:.1f} | {m['guest_keccak']:.0f} | x{m['encode_ntt'] / b1['encode_ntt']:.2f} | x{m['encode_words'] / b1['encode_words']:.2f} |")


if __name__ == "__main__":
    main()
