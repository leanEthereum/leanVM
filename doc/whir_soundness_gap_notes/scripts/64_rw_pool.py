"""Note 64, random windows (c): partners x XOR c with c drawn per position from a public pool of P offsets (note 66,
Section 4). Largest interior of a set of at most k - 1 points, k = n/2, against fully random partners.
Usage: python3 64_rw_pool.py N graphs seed
Pools: 'basis' = the N unit offsets (a random d-subset of the cube directions per position), 'P=2N', 'P=4N' random
nonzero offsets (re-drawn until they span), and 'all' = every nonzero offset (a random XOR partner)."""
import importlib.util, os, random, sys
spec = importlib.util.spec_from_file_location("rw", os.path.join(os.path.dirname(__file__), "64_rw_lib.py"))
R = importlib.util.module_from_spec(spec); spec.loader.exec_module(R)
N, graphs, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
n, rng = 1 << N, random.Random(seed)
s = n // 2 - 1


def spans(pool):
    basis = []
    for v in pool:
        for b in basis:
            v = min(v, v ^ b)
        if v:
            basis.append(v)
    return len(basis) == N


def make_pool(P):
    if P == N:
        return [1 << i for i in range(N)]
    if P >= n - 1:
        return list(range(1, n))
    while True:
        pool = rng.sample(range(1, n), P)
        if spans(pool):
            return pool


for d in (4, 6, 8):
    line = f"N={N} n={n} k={n//2} d={d}:"
    for name, P in (("basis", N), ("P=2N", 2 * N), ("P=4N", 4 * N), ("all", n - 1)):
        if d > P:
            line += f" {name}: d > P |"
            continue
        vals = []
        for _ in range(graphs):
            pool = make_pool(P)
            win = [[x] + [x ^ c for c in rng.sample(pool, d)] for x in range(n)]
            vals.append(R.best_interior(win, s, rng, restarts=30)[0])
        hyp = ((N - 1) / P) ** d if P < n - 1 else 0.5 ** d
        line += f" {name}: mean {sum(vals)/len(vals)/s:.3f} max {max(vals)/s:.3f} (coordinate hyperplane alone {hyp:.3f}) |"
    print(line, flush=True)
