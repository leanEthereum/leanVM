"""Validate whir_model.py against the committed table WHIR_QUERIES (crates/verifier/src/whir.rs).

Usage: python3 validate.py [--fast-only] [--jobs N]
Runs the faithful port (the Rust's bisection) and the fast search on every admitted shape, rates 1..4 and stacked
sizes 16..30, and reports every mismatch. Exit status 1 on any mismatch.
"""

import os
import re
import sys
import time
from multiprocessing import Pool

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import whir_model as wm

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))


def committed_table():
    src = open(os.path.join(REPO, "crates", "verifier", "src", "whir.rs")).read()
    body = src[src.index("const WHIR_QUERIES") :]
    body = body[body.index("= [") + 2 :]
    body = body[: body.index("];") + 1]
    rows = re.findall(r"\[(&\[[^\n]*\])\],", body)
    table = [[[int(x) for x in cell.split(",")] for cell in re.findall(r"&\[([0-9,]+)\]", row)] for row in rows]
    assert len(table) == 4 and all(len(r) == 15 for r in table), "unexpected table shape"
    return table


def one(args):
    rate, log_n, faithful = args
    t = time.time()
    cfg = wm.derive(log_n, rate, wm.DEPLOYED, faithful=faithful)
    detail = None
    if cfg is not None:
        detail = [(lv.log_inv_rate, lv.cols, lv.k, lv.agreement, lv.list_bound, [r[0] for r in lv.rounds]) for lv in cfg.levels]
    return rate, log_n, faithful, (cfg.queries if cfg else None), detail, time.time() - t


def main():
    jobs = 4
    if "--jobs" in sys.argv:
        jobs = int(sys.argv[sys.argv.index("--jobs") + 1])
    modes = [False] if "--fast-only" in sys.argv else [True, False]
    table = committed_table()
    work = [(rate, log_n, f) for f in modes for rate in range(1, 5) for log_n in range(16, 31)]
    bad = 0
    results = {}
    with Pool(jobs) as pool:
        for rate, log_n, faithful, queries, detail, dt in pool.imap_unordered(one, work):
            want = table[rate - 1][log_n - 16]
            ok = queries == want
            bad += not ok
            results[(rate, log_n, faithful)] = (queries, detail)
            print(f"{'ok ' if ok else 'BAD'} {'faithful' if faithful else 'fast    '} rate=2^-{rate} mu={log_n} model={queries} table={want} ({dt:.1f}s)", flush=True)
    if len(modes) == 2:
        for rate in range(1, 5):
            for log_n in range(16, 31):
                a, b = results[(rate, log_n, True)], results[(rate, log_n, False)]
                if a != b:
                    bad += 1
                    print(f"BAD fast != faithful at rate=2^-{rate} mu={log_n}: {a} vs {b}")
    print(f"{len(work)} derivations, {bad} mismatches")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
