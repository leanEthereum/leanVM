#!/usr/bin/env python3
"""Note 73: Lemma 2.1(c) with no sampling error. For a fixed T_j ([8,4], MDS or defective) and a label (Y, D, c),
enumerate every vector of used twiddles t in K^D (uniform in T1 and in T2) and compute exactly
P[tight and G >= g], against q^-g / (1 - d/q). GF(16): labels with d <= 5; GF(256): d <= 2. Needs numpy."""
import importlib.util, itertools, os, sys
import numpy as np
spec = importlib.util.spec_from_file_location("toy", os.path.join(os.path.dirname(os.path.abspath(__file__)), "73_toy.py"))
toy = importlib.util.module_from_spec(spec); spec.loader.exec_module(toy)

def exact(F, G, Y, D, chunk=1 << 16):
    q = F.q; nj, kj = G.shape; d = len(D); m = F.m
    rkY = toy.rank1(F, G[Y]) if Y else 0
    total = q ** d; cnt = {}; ntight = 0
    base = np.zeros((2 * len(Y), 2 * kj), dtype=np.uint8)
    for i, p in enumerate(Y):
        base[2 * i, :kj] = G[p]; base[2 * i + 1, kj:] = G[p]
    for start in range(0, total, chunk):
        idx = np.arange(start, min(start + chunk, total), dtype=np.int64); B = len(idx)
        t = np.stack([(idx >> (m * i)) & (q - 1) for i in range(d)], axis=1).astype(np.uint8)
        M = np.zeros((B, 2 * len(Y) + d, 2 * kj), dtype=np.uint8)
        M[:, :2 * len(Y), :] = base[None]
        for i, p in enumerate(D):
            M[:, 2 * len(Y) + i, :kj] = G[p][None]
            M[:, 2 * len(Y) + i, kj:] = F.mul[t[:, i][:, None], G[p][None]]
        rk = toy.brank(F, M.copy()); Gx = 2 * rkY + d - rk
        tight = np.ones(B, dtype=bool)
        for p in D:
            extra = np.zeros((B, 1, 2 * kj), dtype=np.uint8); extra[:, 0, kj:] = G[p][None]
            tight &= toy.brank(F, np.concatenate([M, extra], axis=1)) > rk
        ntight += int(tight.sum())
        for g in range(1, d + 1):
            cnt[g] = cnt.get(g, 0) + int((tight & (Gx >= g)).sum())
    return total, ntight, cnt

if __name__ == "__main__":
    worst = 0.0
    for m in (4, 8):
        F = toy.GF(m); q = F.q; dmax = 5 if m == 4 else 2
        for variant in ("T1", "T2"):
            for topkind in ("MDS", "defective"):
                while True:
                    Ts, _ = toy.tree(F, variant, 1, 2); G = Ts[2]
                    if (topkind == "MDS") == toy.is_mds(F, G): break
                fams = [("Y = 1 node, D = 5", [0], [1, 2, 3, 4, 5]), ("Y = 2 nodes, D = 4", [0, 5], [1, 2, 6, 7]),
                        ("Y = 2 nodes, D = 5", [0, 5], [1, 2, 3, 6, 7]), ("Y = 3 nodes, D = 2", [0, 3, 6], [1, 4]),
                        ("Y = 3 nodes, D = 3", [0, 3, 6], [1, 4, 7]), ("Y empty, D = 5", [], [0, 2, 4, 6, 7])]
                if topkind == "defective":
                    sing = [list(c) for c in itertools.combinations(range(8), 4) if toy.rank1(F, G[list(c)]) < 4]
                    Ys = sing[0]; cl = toy.closure(F, G, Ys)[0]; rest = [p for p in range(8) if p not in cl]
                    fams += [("Y = singular 4-subset, D = 2", Ys, rest[:2]), ("Y = singular 4-subset, D = 3", Ys, rest[:3]),
                             ("Y = 3 of the singular 4, D = 3", Ys[:3], [Ys[3]] + rest[:2])]
                print(f"GF(2^{m}) {variant}, T_j {topkind}:")
                for name, Y, D in fams:
                    if len(D) > dmax or len(D) == 0: continue
                    total, ntight, cnt = exact(F, G, Y, D); d = len(D)
                    parts = []
                    for g in range(1, d):
                        pr = cnt[g] / total; bnd = q ** -g / (1 - d / q); worst = max(worst, pr / bnd)
                        if cnt[g]: parts.append(f"g>={g}: {cnt[g]}/{total} = {pr:.3e} (bound {bnd:.3e}, ratio {pr / bnd:.3f})")
                    assert cnt[d] == 0
                    print(f"    {name}: P[tight] = {ntight / total:.3e}; " + ("; ".join(parts) if parts else "no fresh excess for any t"))
                    sys.stdout.flush()
    print(f"largest exact ratio P[tight, G >= g] / (q^-g / (1 - d/q)) over all labels: {worst:.4f}")
