"""Note 64, random windows (a): largest interior of a set of at most k - 1 points, random d-out graphs against the cube.
Usage: python3 64_rw_interior.py N graphs seed
Prints, for k = n/2 and n/4: the cube (Harper-optimal sets are found by the same search, as a control) and
d = 2, 4, 6, 8: mean and max over sampled graphs of max|int Z| / (k - 1), and the first-moment ceiling gamma*
(largest g with phi * D(g || phi^d) <= H(phi), natural logs, phi = (k-1)/n), valid for n large only."""
import importlib.util, os, random, sys
from math import log

spec = importlib.util.spec_from_file_location("rw", os.path.join(os.path.dirname(__file__), "64_rw_lib.py"))
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)
N, graphs, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
n, rng = 1 << N, random.Random(seed)


def gamma_star(d, phi):
    H = -phi * log(phi) - (1 - phi) * log(1 - phi)
    p = phi ** d
    D = lambda g: (g * log(g / p) + (1 - g) * log((1 - g) / (1 - p))) if 0 < g < 1 else (log(1 / p) if g >= 1 else 0)
    if phi * D(1) <= H:
        return 1.0
    lo, hi = p, 1.0
    for _ in range(60):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if phi * D(mid) <= H else (lo, mid)
    return lo


for k in (n // 2, n // 4):
    s = k - 1
    c, _ = R.best_interior(R.cube_windows(N), s, rng, restarts=40)
    line = f"N={N} n={n} k={k}: cube (d={N}) {c}/{s} = {c/s:.3f}"
    for d in (2, 4, 6, 8):
        if d + 1 > s:
            line += f" | d={d}: window larger than k-1"
            continue
        vals = [R.best_interior(R.rand_windows(n, d, rng), s, rng, restarts=40)[0] for _ in range(graphs)]
        line += f" | d={d}: mean {sum(vals)/len(vals)/s:.3f} max {max(vals)}/{s} = {max(vals)/s:.3f} (gamma* {gamma_star(d, s/n):.2f})"
    print(line, flush=True)
