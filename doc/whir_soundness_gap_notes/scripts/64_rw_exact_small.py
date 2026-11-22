"""Note 64, 6a calibration: exact largest interior over all sets of k - 1 points at n = 16 (all 11440 sets) and at n = 32
restricted to k = 8 (all C(32,7) sets), against the heuristic search of 64_rw_lib.best_interior, on sampled random graphs."""
import importlib.util, os, random
from itertools import combinations
spec = importlib.util.spec_from_file_location("rw", os.path.join(os.path.dirname(__file__), "64_rw_lib.py"))
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)
rng = random.Random(5)
for n, s, ds in ((16, 7, (2, 4, 6)), (32, 7, (2, 4, 6))):
    for d in ds:
        agree = tot = 0
        pairs = []
        for _ in range(6):
            win = R.rand_windows(n, d, rng)
            masks = [sum(1 << y for y in w) for w in win]
            best = 0
            for Z in combinations(range(n), s):
                zm = 0
                for y in Z: zm |= 1 << y
                c = 0
                for x in Z:
                    if masks[x] & ~zm == 0: c += 1
                if c > best: best = c
            h = R.best_interior(win, s, rng, restarts=40)[0]
            pairs.append((best, h)); agree += best == h; tot += 1
        print(f"n={n} sets of {s} points d={d}: (exact, heuristic) over 6 graphs: {pairs}; equal in {agree}/{tot}", flush=True)
