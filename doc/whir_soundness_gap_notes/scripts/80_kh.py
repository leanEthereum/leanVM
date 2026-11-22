#!/usr/bin/python3
# Referee 80: note 79, Proposition 6.1 and Theorem 6.2.
#  (1) literal brute force over all mu and all M at toy size: Pr_mu[M in S(mu)] = prod_x q^(-r_x(M)) (0 if unsolvable),
#      and E|S(mu) cap L| <= q^(-w) sum_{M in L} q^(w_free(M)).
#  (2) exact values of K(Lambda) = q^(-Lk) sum_{M in L} q^(w_free(M)): the hypothesis KH fails on concentrated patterns.
#  (3) the thresholds of Theorem 6.2 and the distance slack that collinear lists need.
import itertools, math, random, sys
from functools import reduce

def field(m):
    poly = {2: 0b111, 3: 0b1011, 4: 0b10011}[m]
    q = 1 << m
    def mul(a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a & q: a ^= poly
        return r
    T = [[mul(a, b) for b in range(q)] for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        for b in range(1, q):
            if T[a][b] == 1: inv[a] = b
    return q, T, inv

def rank(rows, T, inv):
    rows = [list(r) for r in rows]
    rk = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        p = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if p is None: continue
        rows[rk], rows[p] = rows[p], rows[rk]
        iv = inv[rows[rk][c]]
        rows[rk] = [T[iv][a] for a in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c]
                rows[i] = [a ^ T[f][b] for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def lam_basis(C, L):
    # basis of span(e_l - e_l' : l, l' in C), members 0..L, e_0 = 0, as vectors of length L
    ms = [l for l in range(L + 1) if (C >> l) & 1]
    out = []
    for l in ms[1:]:
        vec = [0] * L
        vec[l - 1] = 1
        if ms[0] >= 1: vec[ms[0] - 1] = 1
        out.append(vec)
    return out

def toy(m, n, k, L, pattern, pis, seed, brute=True):
    q, T, inv = field(m)
    rng = random.Random(seed)
    d = len(pis)
    # an MDS base code: rows (1, t, t^2, ...) at distinct points (any base code would do for Proposition 6.1)
    G = []
    if n <= q:
        for t in rng.sample(range(q), n):
            row = [1]
            for _ in range(k - 1): row.append(T[row[-1]][t])
            G.append(row)
    else:  # Proposition 6.1 is for any base code: random rows
        G = [[rng.randrange(q) for _ in range(k)] for _ in range(n)]
    lam = [lam_basis(pattern[x], L) for x in range(n)]
    w = sum(len(b) for b in lam)
    Ms = list(itertools.product(range(q), repeat=L * k))
    def delta(M, y):  # M g_y in K^L
        return [reduce(lambda a, b: a ^ b, (T[M[l * k + e]][G[y][e]] for e in range(k)), 0) for l in range(L)]
    def in_list(M):
        rows = [tuple(M[l * k:(l + 1) * k]) for l in range(L)]
        if any(not any(r) for r in rows): return False
        return len(set(rows)) == L
    # exact local law
    pred = {}; wfree = {}
    for M in Ms:
        dl = [delta(M, y) for y in range(n)]
        logp = 0; solv = True; wf = 0
        for x in range(n):
            if not lam[x]: continue
            win = [x] + [pi[x] for pi in pis]
            N = [[reduce(lambda a, b: a ^ b, (T[f[l]][dl[y][l]] for l in range(L)), 0) for y in win] for f in lam[x]]
            r_all = rank(N, T, inv); r_par = rank([row[1:] for row in N], T, inv)
            wf += len(lam[x]) - r_all
            if r_all != r_par: solv = False
            logp += r_all
        pred[M] = (q ** (d * n - logp)) if solv else 0  # predicted number of mu
        wfree[M] = wf
    worst = 0
    if brute:
        cnt = dict.fromkeys(Ms, 0)
        for mu in itertools.product(range(q), repeat=d * n):
            H = [[G[x][e] ^ reduce(lambda a, b: a ^ b, (T[mu[a * n + x]][G[pis[a][x]][e]] for a in range(d)), 0) for e in range(k)] for x in range(n)]
            for M in Ms:
                ok = True
                for x in range(n):
                    if not lam[x]: continue
                    val = [0] * L
                    for l in range(L):
                        s = 0
                        for e in range(k): s ^= T[M[l * k + e]][H[x][e]]
                        val[l] = s
                    for f in lam[x]:
                        s = 0
                        for l in range(L): s ^= T[f[l]][val[l]]
                        if s: ok = False; break
                    if not ok: break
                if ok: cnt[M] += 1
        worst = sum(1 for M in Ms if cnt[M] != pred[M])
    lst = [M for M in Ms if in_list(M)]
    E_exact = sum(pred[M] for M in lst) / q ** (d * n)
    bound = sum(q ** wfree[M] for M in lst) / q ** w
    Kval = sum(q ** wfree[M] for M in lst) / q ** (L * k)
    Kfull = sum(q ** wfree[M] for M in lst if rank([M[l * k:(l + 1) * k] for l in range(L)], T, inv) == L) / q ** (L * k)
    return dict(q=q, w=w, mismatches=worst, E=E_exact, bound=bound, K=Kval, Kfull=Kfull, nlist=len(lst))

def H2(t): return 0 if t in (0, 1) else -t * math.log2(t) - (1 - t) * math.log2(1 - t)
def threshold(L, rho, C, bits=64):
    t = (1 + L * rho) / (L + 1)
    for _ in range(200): t = (1 + L * rho) / (L + 1) + H2(t) / bits + math.log2(C) / (bits * (L + 1))
    return t

if __name__ == "__main__":
    print("== (1) Proposition 6.1 by literal enumeration of all mu and all M (GF(4))")
    cases = [
        ("n=5 k=2 L=2 d=1, classes 012 01 02 12 012, pi a 5-cycle", 2, 5, 2, 2, [7, 3, 5, 6, 7], [[1, 2, 3, 4, 0]]),
        ("n=5 k=2 L=2 d=1, classes 012 012 012 01 12, pi with a fixed point", 2, 5, 2, 2, [7, 7, 7, 3, 6], [[1, 0, 2, 4, 3]]),
        ("n=4 k=2 L=3 d=1, classes 0123 012 13 23, pi a 4-cycle", 2, 4, 2, 3, [15, 7, 10, 12], [[1, 2, 3, 0]]),
        ("n=3 k=2 L=2 d=2, classes 012 012 01, two maps", 2, 3, 2, 2, [7, 7, 3], [[1, 2, 0], [2, 0, 1]]),
    ]
    for name, m, n, k, L, pat, pis in cases:
        r = toy(m, n, k, L, pat, pis, 1)
        print(f"  {name}: w={r['w']}, M with a wrong count of mu: {r['mismatches']} of {r['q'] ** (L * k)}; E|S cap L| = {r['E']:.6f} <= bound {r['bound']:.6f}: {r['E'] <= r['bound'] + 1e-12}")
    print("== (2) K(Lambda) exactly (no enumeration of mu); KH asks K <= C^n")
    for m, n, k, L, tsize in [(3, 6, 2, 2, 3), (3, 6, 2, 2, 4), (3, 6, 2, 2, 5), (3, 7, 3, 2, 4), (3, 7, 3, 2, 5), (4, 7, 2, 2, 4), (4, 7, 2, 2, 5), (2, 4, 2, 3, 3), (3, 6, 2, 3, 4)]:
        q = 1 << m
        if q ** (L * k) > 300000: continue
        pat = [(1 << (L + 1)) - 1] * tsize + [0] * (n - tsize)
        r = toy(m, n, k, L, pat, [[(x + 1) % n for x in range(n)]], 2, brute=False)
        pred = q ** ((L - 1) * (tsize - k + 1))
        print(f"  q={q} n={n} k={k} L={L}, all members agree on |T|={tsize}: K = {r['K']:.2f}, K over rank-L M only = {r['Kfull']:.3f}, q^((L-1)(|T|-k+1)) = {pred}, ratio K/that = {r['K'] / pred:.3f}")
    print("  a pattern with no full class, L=3: members 0,1,2 agree on T, member 3 elsewhere")
    for tsize in (3, 4):
        r = toy(2, 4, 2, 3, [7] * tsize + [8] * (4 - tsize), [[1, 2, 3, 0]], 3, brute=False)
        print(f"    q=4 n=4 k=2 |T|={tsize}: K = {r['K']:.2f}, over rank-3 M only = {r['Kfull']:.3f}")
    print("== (3) thresholds of Theorem 6.2 (n -> infinity), and the zeros a collinear list needs")
    for rho, Ls in [(0.5, [2, 3, 4, 8, 16]), (0.25, [3, 4, 8, 16])]:
        for C in (4, 1):
            row = []
            for L in Ls:
                t = threshold(L, rho, C)
                eps = t - (1 + L * rho) / (L + 1)
                s = 64 * (L + 1) * eps / L
                row.append(f"L={L}: tau={t:.4f} (collinear lists need distance slack {s:.2f}/64)")
            print(f"  rate {rho}, C={C}: " + "; ".join(row))
    print("  first-moment distance slack s solves s = H(rho + s/64) + log2(C1): C1=1: %.3f, C1=2: %.3f, C1=4: %.3f (rate 1/2, in units of n/64)" % tuple(
        [reduce(lambda s, _: H2(0.5 + s / 64) + math.log2(c1), range(100), 1.0) for c1 in (1, 2, 4)]))
