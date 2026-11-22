"""Note 85: the counterexample to (C*) and (C'), checked from first principles (independent of 85_chain.py's chain code).
Three members, (k, n) = (16, 32): three zero blocks of scale 8 (three common leaves each) and three pair blocks.
Prints, for several draws of the twiddles: the rank, the weight, B(P; Q*) = 2 r_up(Q*) + sum_x rank(Lambda_x | Delta_p),
the dimensions of S', K_i, K_s cap K_t at scale 8, the dimension of sum_r (K_s cap K_t) (x) B_r inside ker P, and the value
Phi of note 74's one-level count for Y = Y* + <nu_i (x) g_{p_i}> (nu_i the functional killing the solutions at the mixed
pair of zero block i).  Usage: 85_cex.py [10]   (10: the ten-member version, members = pairs of five blocks)"""
import sys, os, random, itertools, importlib.util
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lib83", os.path.join(here, "83_lib.py")); L83 = importlib.util.module_from_spec(spec); spec.loader.exec_module(L83)
spec = importlib.util.spec_from_file_location("ch85", os.path.join(here, "85_chain.py")); CH = importlib.util.module_from_spec(spec); spec.loader.exec_module(CH)
def tok(s): return [0 if t == "." else sum(1 << int(c, 36) for c in t) for t in s.split()]
if len(sys.argv) > 1 and sys.argv[1] == "10":
    cls = CH.staircase_multi(8, 4, 3, 0)
    for q in range(3): cls[4 * q + 3] = 0          # the leaf left in a zero block carries no class
else:
    cls = tok("012 012 012 . 012 012 012 . 012 012 012 . 01 01 01 01 02 02 02 02 12 12 12 12 . . . . . . . .")
n = 32; k = 16; v = 4; t = max(c.bit_length() for c in cls); L = t - 1
def vec(M): return np.ascontiguousarray(M, dtype=np.uint64)
for seed in (1, 2, 3):
    rnd = random.Random(8500 + seed); tw = L83.make_tw(v, rnd)
    G = L83.gen(tw, v); G1 = L83.gen(tw[1:], v - 1); G2 = L83.gen(tw[2:], v - 2)
    sp = [CH.class_thetas(C) for C in cls]; w = sum(map(len, sp))
    rows = CH.rows_binary(G, k, L, sp); ker = L83.kernel(np.array(rows), L * k); d0 = len(ker); r = L * k - d0
    # Q*: binary functionals killing both bottom slices of every solution at each pair
    K3 = ker.reshape(d0, L, k)
    s0 = L83.matmul(vec(K3[:, :, 0::2]).reshape(d0 * L, k // 2), G1.T.copy()).reshape(d0, L, n // 2)
    s1 = L83.matmul(vec(K3[:, :, 1::2]).reshape(d0 * L, k // 2), G1.T.copy()).reshape(d0, L, n // 2)
    Dp = [np.concatenate([s0[:, :, p], s1[:, :, p]], axis=0) for p in range(n // 2)]
    Q = [CH.binary_annihilator(D, L) for D in Dp]
    rowsQ = CH.rows_binary(G1, k // 2, L, Q); kerQ = L83.kernel(np.array(rowsQ), L * k // 2); d1 = len(kerQ); rQ = L * k // 2 - d1
    ev = L83.matmul(kerQ.reshape(d1 * L, k // 2), G1.T.copy()).reshape(d1, L, n // 2)
    B = 2 * rQ
    for x in range(n):
        if not sp[x]: continue
        T = np.zeros((len(sp[x]), L), dtype=np.uint64)
        for a, th in enumerate(sp[x]):
            for l in range(L):
                if (th >> l) & 1: T[a, l] = 1
        B += L83.rank(L83.matmul(T, vec(ev[:, :, x >> 1]).T.copy()))
    # scale 8: the top pattern (one class per block) and the spaces K_i
    top = [0, 0, 0] + [cls[4 * q] for q in range(3, 8)]
    kerS = L83.kernel(np.array(CH.rows_binary(G2, k // 4, L, [CH.class_thetas(C) for C in top])), L * k // 4); dS = len(kerS)
    evS = L83.matmul(kerS.reshape(dS * L, k // 4), G2.T.copy()).reshape(dS, L, 8)
    def Kdim(blocks):   # solutions of the top pattern vanishing at the given blocks
        A = np.concatenate([evS[:, :, q] for q in blocks], axis=1)   # dS x (L * len)
        return dS - L83.rank(A)
    a1 = [Kdim([i]) for i in range(3)]; a2 = [Kdim([s, u]) for s, u in ((1, 2), (0, 2), (0, 1))]; a3 = Kdim([0, 1, 2])
    # note 74's count with Y = Y* + <nu (x) g_p>, nu in the annihilator of the solutions at the mixed pairs 1, 3, 5
    extra = []; inter = 0
    for p in (1, 3, 5):
        D = Dp[p]; rk = L83.rank(D)
        ann = L83.kernel(D, L)                       # functionals nu with nu . delta = 0 on the solutions at p
        for nu in ann:
            rw = np.zeros(L * k // 2, dtype=np.uint64)
            for l in range(L): rw[l * (k // 2):(l + 1) * (k // 2)] = [L83.mul(int(nu[l]), int(g)) for g in G1[p]]
            extra.append(rw)
        inter += len(ann)
    dimY = L83.rank(np.array(rowsQ + extra))
    Phi = 2 * dimY
    for x in range(n):
        if not sp[x]: continue
        Ux = CH.rows_binary(G1, k // 2, L, [sp[x] if p == x >> 1 else [] for p in range(n // 2)])
        Phi += L83.rank(np.array(rowsQ + extra + Ux)) - dimY
    # the relations among the rows: components u_x = sum_theta c_{x,theta} theta (x) g_p; an exact binary Q would force u_x in Y_Q (x) F, inside Y*
    A = np.array(rows); rel = L83.kernel(np.ascontiguousarray(A.T), A.shape[0]); outside = set()
    idx = []; 
    for x in range(n): idx += [(x, th) for th in sp[x]]
    for c in rel:
        for x in range(n):
            ux = np.zeros(L * k // 2, dtype=np.uint64); nz = False
            for i, (y, th) in enumerate(idx):
                if y != x or int(c[i]) == 0: continue
                nz = True
                for l in range(L):
                    if (th >> l) & 1:
                        seg = np.array([L83.mul(int(c[i]), int(g)) for g in G1[x >> 1]], dtype=np.uint64)
                        ux[l * (k // 2):(l + 1) * (k // 2)] ^= seg
            if nz and L83.rank(np.array(rowsQ + [ux])) > rQ: outside.add(x)
    print(f"   relations among the rows: {len(rel)}; leaves whose relation component is outside Y*: {sorted(outside)}")
    print(f"seed {seed}: members {t} w={w} Lk={L * k} rank={r} kernel={d0} | Q*: weight {sum(map(len, Q))} rank {rQ} kernel {d1} | B(P;Q*)={B}"
          f" | scale 8: dim S'={dS} dim K_i={a1} dim K_s∩K_t={a2} (sum {sum(a2)}) triple {a3} | Y*+nu: dim {dimY} (Y* {rQ}, {inter} functionals nu), Phi={Phi}")
