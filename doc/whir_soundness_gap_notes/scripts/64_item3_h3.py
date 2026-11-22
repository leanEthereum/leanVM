"""Note 64, item 3: search for triples (0, d1, d2) and a word maximizing u_2 + 2 u_3 for one sampled mu, cube window.

Usage: python3 64_item3_h3.py m N k iters seed
A. random pairs (d1, d2). B. structured families with free agreements (no look at mu). C. adaptive adversary:
   impose 2k - 2 of the linear conditions "pair agrees at x" on (d1, d2), take the 2-dimensional kernel u + lam v,
   pick the best lam (each remaining condition is one root), then re-impose a random subset of the satisfied
   conditions and repeat (local search). Generic linear algebra alone gives 2k - 1.
"""
import importlib.util, random, sys, os
from math import comb, log2

spec = importlib.util.spec_from_file_location("lib64", os.path.join(os.path.dirname(__file__), "64_lib.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)
m, N, k, iters, seed = (int(a) for a in sys.argv[1:6])
F, n, dirs, rng = L.GF(m), 1 << N, list(range(N)), random.Random(seed)
q, mul, inv = F.q, F.mul, F.inv
pw = L.powers(F, n, k)
mu = L.sample_mu(F, n, N + 1, rng)
rnd = lambda d: [F.rand(rng) for _ in range(d)]
sym = lambda coef: L.mix(F, mu, L.evaluate(F, pw, coef + [0] * (k - len(coef))), dirs)


def count3(s1, s2):
    return sum(2 if (a == 0 and b == 0) else (1 if (a == 0 or b == 0 or a == b) else 0) for a, b in zip(s1, s2))


def kernel(rows, ncol):
    rows, piv = [r[:] for r in rows], []
    for c in range(ncol):
        p = next((i for i in range(len(piv), len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        r = len(piv); rows[r], rows[p] = rows[p], rows[r]
        iv = inv(rows[r][c]); rows[r] = [mul(iv, a) for a in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]; rows[i] = [a ^ mul(f, b) for a, b in zip(rows[i], rows[r])]
        piv.append(c)
    out = []
    for c in (c for c in range(ncol) if c not in piv):
        v = [0] * ncol; v[c] = 1
        for r, pc in enumerate(piv):
            v[pc] = rows[r][c]
        out.append(v)
    return out


# A. random
A = [count3(sym(rnd(k)), sym(rnd(k))) for _ in range(300)]
print(f"q=2^{m} N={N} k={k} 2k={2*k}: A random: mean {sum(A)/len(A):.3f} max {max(A)} (prediction 3n/q = {3*n/q:.3f})")
# B. structured, free agreements
R = max(r for r in range(N) if len(L.ball(N, 0, r)) < k)
B0, B1 = L.ball(N, 0, R), L.ball(N, n - 1, R)
Z0, Z1, iB = L.vanishing(F, B0), L.vanishing(F, B1), len(L.interior(B0, N))
LU = L.vanishing(F, [0, 1, 2, 3])
def comp(Q):
    out = [0]
    for c in reversed(Q):
        out = L.poly_mul(F, out, LU); out[0] ^= c
    return out[:k]
fam = {
    f"common ball (|B|={len(B0)}, free 2*int = {2*iB})": lambda: (L.poly_mul(F, Z0, rnd(k - len(B0))), L.poly_mul(F, Z0, rnd(k - len(B0)))),
    f"two antipodal balls (free 2*int = {2*iB})": lambda: (L.poly_mul(F, Z0, rnd(k - len(B0))), L.poly_mul(F, Z1, rnd(k - len(B1)))),
    "ratio constant on a ball (free 0, cheap doubles)": lambda: (lambda d2, e, lam: ([mul(lam, a) ^ b for a, b in zip(d2, L.poly_mul(F, Z0, e))], d2))(rnd(k), rnd(k - len(B0)), 2 + rng.randrange(q - 2)),
    "periodic A(L_U), B(L_U), U = span(b0, b1)": lambda: (comp(rnd(k // 4)), comp(rnd(k // 4))),
}
for name, gen in fam.items():
    res = [count3(sym(a), sym(b)) for a, b in (gen() for _ in range(100))]
    print(f"   B {name}: mean {sum(res)/len(res):.2f} max {max(res)}")
# C. adaptive
mrow = [[0] * k for _ in range(n)]          # c_mu(P)(x) = <mrow[x], coef(P)>
for x in range(n):
    for c, w in zip(mu[x], L.window(x, dirs)):
        for j in range(k):
            mrow[x][j] ^= mul(c, pw[w][j])
zero = [0] * k
cond = lambda t, x: (mrow[x] + zero) if t == 0 else (zero + mrow[x]) if t == 1 else (mrow[x] + mrow[x])
def satisfied(s1, s2):
    out = []
    for x, (a, b) in enumerate(zip(s1, s2)):
        if a == 0 and b == 0: out += [(0, x), (1, x)]
        elif a == 0: out.append((0, x))
        elif b == 0: out.append((1, x))
        elif a == b: out.append((2, x))
    return out
def best_on_pencil(u, v):
    su, sv = (sym(u[:k]), sym(u[k:])), (sym(v[:k]), sym(v[k:]))
    best = (-1, None)
    cands = set()
    for x in range(n):
        for num, den in ((su[0][x], sv[0][x]), (su[1][x], sv[1][x]), (su[0][x] ^ su[1][x], sv[0][x] ^ sv[1][x])):
            if den: cands.add(mul(num, inv(den)))
    for lam in list(cands)[:4000]:
        w = [a ^ mul(lam, b) for a, b in zip(u, v)]
        c = count3(sym(w[:k]), sym(w[k:]))
        if c > best[0] and any(w[:k]) and any(w[k:]) and w[:k] != w[k:]: best = (c, w)
    return best
allc = [(t, x) for t in range(3) for x in range(n)]
cur = rng.sample(allc, 2 * k - 2); best = (-1, None); hist = []
for it in range(iters):
    ker = kernel([cond(t, x) for t, x in cur], 2 * k)
    if len(ker) > 2: ker = rng.sample(ker, 2)
    if len(ker) < 2: cur = rng.sample(allc, 2 * k - 2); continue
    c, w = best_on_pencil(ker[0], ker[1])
    if w is None: cur = rng.sample(allc, 2 * k - 2); continue   # the conditions forced d1 = 0 or d2 = 0
    if c >= best[0]:
        best = (c, w)
    sat = satisfied(sym(best[1][:k]), sym(best[1][k:]))
    cur = rng.sample(sat, min(len(sat), 2 * k - 2 - rng.randrange(0, 3)))
    while len(cur) < 2 * k - 2: cur.append(rng.choice(allc))
    hist.append(best[0])
def npat(C):
    return sum(comb(n, j) * comb(n - j, C - 2 * j) * 3 ** (C - 2 * j) for j in range(0, C // 2 + 1) if C - 2 * j <= n - j)
estar = max(e for e in range(0, 2 * n - 2 * k) if log2(max(1, npat(2 * k - 1 + e))) >= m * e)
print(f"   C adaptive: best u_2+2u_3 = {best[0]} after {iters} iterations (2k-1 = {2*k-1}); trajectory {hist[::max(1, iters//8)]};"
      f" first-moment ceiling 2k-1+e* = {2*k-1+estar} (e* = {estar})")
