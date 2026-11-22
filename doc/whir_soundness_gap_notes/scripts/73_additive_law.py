#!/usr/bin/env python3
"""Note 73, Conjecture 9.3 at toy size: for an MDS code V of length d and dimension nu over GF(16),
count exactly the vectors t in K^d with dim{v in V : t*v in V} >= delta and full support,
against q^(2nu - delta) (Lemma 2.1), q^(2nu - 2delta + 1) (additive law) and q^(d - delta(d - 2nu + delta)) (general position).
Codes: Reed-Solomon, random MDS, and the code N_j(Y) read on D for a random tree code T_j (T1 and T2).
Needs numpy (run with /usr/bin/python3 on this machine)."""
import importlib.util, itertools, sys, os
import numpy as np
spec = importlib.util.spec_from_file_location("toy", os.path.join(os.path.dirname(os.path.abspath(__file__)), "73_toy.py"))
toy = importlib.util.module_from_spec(spec); spec.loader.exec_module(toy)
F = toy.GF(4); q = F.q
rng = np.random.default_rng(7309)

def nullspace_basis(M):
    """Rows spanning {x : M x = 0} over GF(16); M is (r, c)."""
    M = M.copy(); r, c = M.shape; piv = []; row = 0
    for col in range(c):
        pr = next((i for i in range(row, r) if M[i, col]), None)
        if pr is None: continue
        M[[row, pr]] = M[[pr, row]]
        M[row] = F.mul[F.inv[M[row, col]], M[row]]
        for i in range(r):
            if i != row and M[i, col]: M[i] ^= F.mul[M[i, col], M[row]]
        piv.append(col); row += 1
        if row == r: break
    free = [j for j in range(c) if j not in piv]; out = []
    for f in free:
        x = np.zeros(c, dtype=np.uint8); x[f] = 1
        for i, pc in enumerate(piv): x[pc] = M[i, f]
        out.append(x)
    return np.array(out, dtype=np.uint8).reshape(len(free), c)

def matmul(A, B):
    out = np.zeros((A.shape[0], B.shape[1]), dtype=np.uint8)
    for i in range(A.shape[0]):
        for j in range(B.shape[1]):
            acc = 0
            for l in range(A.shape[1]): acc ^= int(F.mul[A[i, l], B[l, j]])
            out[i, j] = acc
    return out

def is_mds(G):
    nu, d = G.shape
    return all(toy.rank1(F, G[:, list(c)].T.copy()) == nu for c in itertools.combinations(range(d), nu))

def count(G, chunk=1 << 17):
    """G: (nu, d) generator. Returns counts[delta] = #t with dim V(t) >= delta and full support."""
    nu, d = G.shape
    H = nullspace_basis(G)                      # (d - nu, d), G H^T = 0
    assert not matmul(G, H.T).any()
    counts = np.zeros(nu + 1, dtype=np.int64); total = q ** d
    for start in range(0, total, chunk):
        idx = np.arange(start, min(start + chunk, total), dtype=np.int64)
        t = np.stack([(idx >> (4 * i)) & 15 for i in range(d)], axis=1).astype(np.uint8)       # (B, d)
        # A(t) = G diag(t) H^T : (B, nu, d - nu)
        GT = F.mul[G[None, :, :], t[:, None, :]]                                                 # (B, nu, d)
        A = np.zeros((len(idx), nu, d - nu), dtype=np.uint8)
        for l in range(d):
            A ^= F.mul[GT[:, :, l][:, :, None], H[:, l][None, None, :]]
        rk = toy.brank(F, A.copy())
        dim = nu - rk
        full = np.ones(len(idx), dtype=bool)
        for p in range(d):
            ext = np.concatenate([A, np.broadcast_to(G[:, p][None, :, None], (len(idx), nu, 1))], axis=2)
            full &= toy.brank(F, ext.copy()) > rk
        for delta in range(1, nu + 1):
            counts[delta] += int((full & (dim >= delta)).sum())
    return counts

def report(name, G):
    nu, d = G.shape; c = count(G)
    import math
    parts = []
    for delta in range(max(1, 2 * nu - d + 1), nu + 1):
        lg = math.log(c[delta], q) if c[delta] else float("-inf")
        parts.append(f"delta={delta}: {c[delta]} = q^{lg:.2f} (Lemma 2.1 q^{2*nu-delta}, additive q^{2*nu-2*delta+1}, general position q^{d-delta*(d-2*nu+delta)})")
    print(f"  {name}, [d, nu] = [{d}, {nu}]: " + "; ".join(parts)); sys.stdout.flush()

if __name__ == "__main__":
    for (d, nu) in ((6, 3), (5, 2), (6, 2)):
        print(f"GF(16), length {d}, dimension {nu}: number of t in K^{d} with dim V(t) >= delta and full support")
        xs = rng.choice(np.arange(1, 16), size=d, replace=False).astype(np.uint8)
        G = np.ones((nu, d), dtype=np.uint8)
        for i in range(1, nu): G[i] = F.mul[G[i - 1], xs]
        report("Reed-Solomon", G)
        found = 0
        while found < 3:
            G = np.concatenate([np.eye(nu, dtype=np.uint8), rng.integers(1, 16, size=(nu, d - nu), dtype=np.uint8)], axis=1)
            if is_mds(G): found += 1; report(f"random MDS {found}", G)
        for variant in ("T1", "T2"):
            # tree code T_2 = [8, 4]; Y = 4 - nu nodes, D = d of the others; V = N(Y) read on D
            while True:
                Ts, _ = toy.tree(F, variant, 1, 2); T = Ts[2]
                if not toy.is_mds(F, T): continue
                perm = rng.permutation(8); Y = list(perm[:4 - nu]); D = list(perm[4 - nu:4 - nu + d])
                if len(D) < d: break
                N = nullspace_basis(T[Y]) if Y else np.eye(4, dtype=np.uint8)      # rows a with <g_p, a> = 0 on Y
                V = matmul(N, T[D].T)                                             # (nu, d)
                if V.shape[0] == nu and is_mds(V): report(f"tree code {variant}, N(Y) on D", V); break
