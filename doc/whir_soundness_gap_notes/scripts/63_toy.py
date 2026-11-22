#!/usr/bin/env python3
"""Note 63, Section 8: toy experiments for quadruples (t = 4).

  planted : the plain Reed-Solomon quadruple "spine times leave-one-out quadratics in L_G" (free sum 1.75 n - 3
            against 3k = 1.5 n at rate 1/2), under a local window, the cube window and random d-out windows.
  search  : random d-out windows, one sampled mu: impose 3k - 1 random agreement conditions on (d_1, d_2, d_3),
            take the kernel vector, score the quadruple with its best word; compare with 3k.
  lemmaR  : brute force over GF(2) and GF(4) of the revealed-set bound (Lemma 5.1): number of value assignments
            on U with every window of rank <= u - 1, against patterns * q^(u|U| - |U| + alpha).
  python3 63_toy.py planted | search | lemmaR | all
"""
import importlib.util, itertools, os, random, sys
from math import comb

spec = importlib.util.spec_from_file_location("lib63", os.path.join(os.path.dirname(os.path.abspath(__file__)), "63_lib.py"))
L = importlib.util.module_from_spec(spec)
spec.loader.exec_module(L)


def windows_cube(N):
    return [[x] + [x ^ (1 << i) for i in range(N)] for x in range(1 << N)]


def windows_local(N, tp):
    return [[x] + [x ^ (1 << i) for i in range(tp)] for x in range(1 << N)]


def windows_random(N, d, rng):
    n = 1 << N
    return [[x] + rng.sample([y for y in range(n) if y != x], d) for x in range(n)]


def encode(F, vals, W, mu):
    """note 66: symbol at x is P(x) + sum_l mu_l(x) P(pi_l(x))."""
    out = []
    for x, w in enumerate(W):
        acc = vals[x]
        for l, y in enumerate(w[1:]):
            acc ^= F.mul(mu[x][l], vals[y])
        out.append(acc)
    return out


def free_sums(evals, W):
    t, single, multi = len(evals), 0, 0
    for w in W:
        key = {}
        for i in range(t):
            key.setdefault(tuple(evals[i][y] for y in w), []).append(i)
        single += max(len(c) for c in key.values()) - 1
        multi += t - len(key)
    return single, multi


def planted(seed=1):
    rng = random.Random(seed)
    F = L.GF(8)
    print("planted quadruple g * Q_i(L_G), G of codimension 3, Q_i the quadratics through three of four points")
    print("  N   n   k  3k | max degree | predicted plain free sum | window: free sum, best-word sum (min/max over 5 mu)")
    for N in (5, 6, 7):
        n, k = 1 << N, 1 << (N - 1)
        G = range(1 << (N - 3))
        LG = []
        for x in range(n):
            acc = 1
            for gg in G:
                acc = F.mul(acc, x ^ gg)
            LG.append(acc)
        coset = [x >> (N - 3) for x in range(n)]
        s = [LG[c << (N - 3)] for c in range(8)]
        cval = [F.rand(rng, True) for _ in range(4)]
        Q = []
        for i in range(4):
            idx = [l for l in range(4) if l != i]
            Q.append(F.interpolate([s[l] for l in idx], [cval[l] for l in idx]))
        zeros = [x for x in range(n) if coset[x] in (4, 5)][:-1]
        gpoly = F.vanishing(zeros)
        gv = [F.peval(gpoly, x) for x in range(n)]
        evals = [[F.mul(gv[x], F.peval(Q[i], LG[x])) for x in range(n)] for i in range(4)]
        deg = max(F.degree(F.interpolate(list(range(n)), ev)) for ev in evals)
        pred = 3 * len(zeros) + 2 * (n // 2)
        row = f" {N:2d} {n:3d} {k:3d} {3 * k:3d} | {deg:3d} | {pred:3d} |"
        for name, W in (("local(3)", windows_local(N, N - 3)), ("cube", windows_cube(N)), ("random d=6", windows_random(N, min(6, N), rng))):
            fs, _ = free_sums(evals, W)
            best = []
            for _ in range(5):
                mu = [[F.rand(rng) for _ in w[1:]] for w in W]
                best.append(L.best_word_sum([encode(F, ev, W, mu) for ev in evals]))
            row += f" {name}: {fs}, {min(best)}/{max(best)};"
        print(row)


def search(seed=2):
    rng = random.Random(seed)
    print("adaptive search, random d-out windows, t = 4: best sum of (c_x - 1)_+ found against 3k")
    print("  q    N   k  d  3k | trials | scores: min mean max | kernel dimension max")
    for m, N, k, d, trials in ((8, 4, 8, 4, 300), (8, 5, 16, 5, 200), (8, 5, 8, 5, 300), (16, 5, 16, 5, 100), (16, 6, 32, 6, 30)):
        F = L.GF(m)
        n = 1 << N
        W = windows_random(N, d, rng)
        mu = [[F.rand(rng) for _ in w[1:]] for w in W]
        pw = [[1] * k for _ in range(n)]
        for x in range(n):
            for j in range(1, k):
                pw[x][j] = F.mul(pw[x][j - 1], x)
        grow = []
        for x, w in enumerate(W):
            r = list(pw[x])
            for l, y in enumerate(w[1:]):
                r = [a ^ F.mul(mu[x][l], b) for a, b in zip(r, pw[y])]
            grow.append(r)
        scores, kdim = [], 0
        for _ in range(trials):
            rows, cover = [], [[] for _ in range(n)]
            while len(rows) < 3 * k - 1:
                x = rng.randrange(n)
                if len(cover[x]) == 4:
                    continue
                if not cover[x]:
                    cover[x].append(rng.randrange(4))
                j = rng.choice([i for i in range(4) if i not in cover[x]])
                r = [0] * (3 * k)
                for mem in (cover[x][0], j):
                    if mem:
                        r[(mem - 1) * k:mem * k] = grow[x]
                cover[x].append(j)
                rows.append(r)
            ker = F.kernel(rows, 3 * k)
            kdim = max(kdim, len(ker))
            v = ker[0]
            polys = [[0] * k] + [v[i * k:(i + 1) * k] for i in range(3)]
            if len({tuple(p) for p in polys}) < 4:
                continue
            cws = [[F.peval(grow_dot, 0) for grow_dot in ()] for _ in ()]
            cws = []
            for p in polys:
                cws.append([_dot(F, grow[x], p) for x in range(n)])
            scores.append(L.best_word_sum(cws))
        print(f" 2^{m:<2d} {N:2d} {k:3d} {d:2d} {3 * k:3d} | {len(scores):3d} | {min(scores)} {sum(scores) / len(scores):.2f} {max(scores)} | {kdim}")


def _dot(F, row, vec):
    acc = 0
    for a, b in zip(row, vec):
        if a and b:
            acc ^= F.mul(a, b)
    return acc


def lemma_r(seed=3):
    rng = random.Random(seed)
    print("Lemma 5.1 by brute force: count of assignments with every window of rank <= u - 1, and the bound")
    print("  q  u  |U|  windows (sizes)  | count | log_q count | u|U| - (|U| - alpha) | bound holds (with pattern factor)")
    for m, u, nU, nw, ws in ((1, 2, 7, 4, 3), (1, 3, 6, 4, 4), (1, 3, 7, 5, 4), (2, 2, 5, 3, 3), (2, 2, 6, 4, 3), (1, 2, 9, 6, 4), (1, 3, 7, 6, 5)):
        q = 1 << m
        F = L.GF(4) if m == 2 else None
        wins = [sorted(rng.sample(range(nU), ws)) for _ in range(nw)]
        alpha = max(len(E) for r in range(nU + 1) for E in itertools.combinations(range(nU), r)
                    if all(len(set(E) & set(w)) <= u - 1 for w in wins))
        vecs = list(itertools.product(range(q), repeat=u))

        def rank(rows):
            if m == 1:
                M, rk = [list(r) for r in rows], 0
                for c in range(u):
                    piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
                    if piv is None:
                        continue
                    M[rk], M[piv] = M[piv], M[rk]
                    for i in range(len(M)):
                        if i != rk and M[i][c]:
                            M[i] = [a ^ b for a, b in zip(M[i], M[rk])]
                    rk += 1
                return rk
            Fq = _GF4
            return Fq.rank(rows)

        count = 0
        for assign in itertools.product(vecs, repeat=nU):
            if all(rank([assign[y] for y in w]) <= u - 1 for w in wins):
                count += 1
        from math import log
        lg = log(count) / log(q)
        expo = u * nU - (nU - alpha)
        patt = sum(comb(ws, j) for j in range(u)) ** nw
        print(f"  {q}  {u}  {nU}  {nw} x {ws}  | {count} | {lg:.2f} | {expo} | {count <= patt * q ** expo}")


class _GF4cls:
    MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
    INV = [0, 1, 3, 2]

    def rank(self, rows):
        M, rk = [list(r) for r in rows], 0
        ncol = len(M[0])
        for c in range(ncol):
            piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            iv = self.INV[M[rk][c]]
            M[rk] = [self.MUL[iv][v] for v in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c]:
                    f = M[i][c]
                    M[i] = [a ^ self.MUL[f][b] for a, b in zip(M[i], M[rk])]
            rk += 1
        return rk


_GF4 = _GF4cls()

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    if what in ("planted", "all"):
        planted()
    if what in ("search", "all"):
        search()
    if what in ("lemmaR", "all"):
        lemma_r()
