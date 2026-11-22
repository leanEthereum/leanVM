"""Cross-check whir_model.py at non-deployed knobs against the Rust search itself (researcher 08).

The Rust search reads its knobs from constants of `crates/verifier`, so it cannot be run at other values in place.
`crosscheck.sh` copies `whir_config.rs` and `affine_mca.rs`, unmodified but for their imports, into a scratch crate
outside the repository whose stub `verifier` module carries the constants of one variant, and prints the query counts
and level-start lists of every admitted shape. This script compares those files with the model.

Usage: python3 crosscheck.py DIR   (DIR holds out_<k0>_<ks>_<r0>_<rs>_<res>_<gq>_<gf>_<gb>_<go>.txt)
"""

import ast
import glob
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import whir_model as wm


def main(directory):
    bad = total = fast_diff = fast_queries_diff = 0
    for path in sorted(glob.glob(os.path.join(directory, "out_*.txt"))):
        k0, ks, r0, rs, res, gq, gf, gb, go = map(int, os.path.basename(path)[4:-4].split("_"))
        kn = wm.with_knobs(initial_fold=k0, sub_fold=ks, initial_reduction=r0, sub_reduction=rs, residual_max=res, g_query=gq, g_fold=gf, g_batch=gb, g_ood=go)
        miss = 0
        rows = [ln.split(" ", 2) for ln in open(path).read().splitlines() if ln.strip()]
        for rate, log_n, rest in rows:
            want = None if rest == "None" else tuple(ast.literal_eval("[" + rest.replace("] [", "], [") + "]"))
            cfg = wm.derive(int(log_n), int(rate), kn, faithful=True)
            got = None if cfg is None else (cfg.queries, [lv.list_bound for lv in cfg.levels])
            fast = wm.derive(int(log_n), int(rate), kn, faithful=False)
            got_fast = None if fast is None else (fast.queries, [lv.list_bound for lv in fast.levels])
            total += 1
            if got != (None if want is None else (list(want[0]), list(want[1]))):
                miss += 1
                print(f"  MISMATCH rate={rate} mu={log_n}: rust {want} model {got}")
            if got != got_fast:
                fast_diff += 1
                fast_queries_diff += got is None or got_fast is None or got[0] != got_fast[0]
        bad += miss
        print(f"k0={k0} ks={ks} r0={r0} rs={rs} residual_max={res} grinds q/f/b/o={gq}/{gf}/{gb}/{go}: {len(rows)} shapes, {miss} mismatches")
    print(f"{total} derivations, {bad} mismatches between the Rust and the faithful port")
    print(f"the fast search differs from the faithful one in {fast_diff} derivations ({fast_queries_diff} of them in a query count)")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main(sys.argv[1])
