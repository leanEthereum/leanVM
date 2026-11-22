#!/usr/bin/env python3
"""Note 73, Conjecture 9.3, sampled version for [8,4] codes over GF(16): P over uniform t in K^8 of
"dim{v in V : t*v in V} >= 2 and full support", for Reed-Solomon, random MDS and two-level tree codes.
Additive law: q^-3 = 2.44e-4. General position: q^-4 = 1.53e-5. Lemma 2.1: q^-2. Needs numpy."""
import importlib.util, os, sys, itertools
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("al", os.path.join(here, "73_additive_law.py"))
al = importlib.util.module_from_spec(spec); spec.loader.exec_module(al)
toy, F = al.toy, al.F; q = F.q
rng = np.random.default_rng(7310)

def sample(G, B=2_000_000, chunk=1 << 17):
    nu, d = G.shape; H = al.nullspace_basis(G); hits = {2: 0, 3: 0, 4: 0}; nfs = {2: 0}
    done = 0
    while done < B:
        b = min(chunk, B - done); done += b
        t = rng.integers(0, q, size=(b, d), dtype=np.uint8)
        GT = F.mul[G[None, :, :], t[:, None, :]]
        A = np.zeros((b, nu, d - nu), dtype=np.uint8)
        for l in range(d): A ^= F.mul[GT[:, :, l][:, :, None], H[:, l][None, None, :]]
        rk = toy.brank(F, A.copy()); dim = nu - rk
        cand = dim >= 2
        nfs[2] += int(cand.sum())
        if cand.any():
            Ac = A[cand]; rkc = rk[cand]; full = np.ones(len(Ac), dtype=bool)
            for p in range(d):
                ext = np.concatenate([Ac, np.broadcast_to(G[:, p][None, :, None], (len(Ac), nu, 1))], axis=2)
                full &= toy.brank(F, ext.copy()) > rkc
            for delta in hits: hits[delta] += int((full & (dim[cand] >= delta)).sum())
    return {k: v / B for k, v in hits.items()}, nfs[2] / B

if __name__ == "__main__":
    nu, d = 4, 8
    codes = []
    xs = rng.choice(np.arange(0, 16), size=d, replace=False).astype(np.uint8)
    G = np.ones((nu, d), dtype=np.uint8)
    for i in range(1, nu): G[i] = F.mul[G[i - 1], xs]
    codes.append(("Reed-Solomon", G))
    found = 0
    while found < 2:
        G = np.concatenate([np.eye(nu, dtype=np.uint8), rng.integers(1, 16, size=(nu, d - nu), dtype=np.uint8)], axis=1)
        if al.is_mds(G): found += 1; codes.append((f"random MDS {found}", G))
    for variant in ("T1", "T2"):
        for rep in range(2):
            while True:
                Ts, _ = toy.tree(F, variant, 1, 2); T = Ts[2]
                if toy.is_mds(F, T): break
            codes.append((f"two-level tree code {variant} #{rep + 1}", T.T.copy()))
    print(f"[8,4] codes over GF(16), 2000000 uniform t each; q^-3 = {q**-3:.2e}, q^-4 = {q**-4:.2e}")
    for name, G in codes:
        h, nf = sample(G)
        print(f"  {name}: P[dim >= 2, full support] = {h[2]:.2e}; P[dim >= 3, full support] = {h[3]:.2e}; P[dim >= 2, any support] = {nf:.2e}")
        sys.stdout.flush()
