"""Note 64, random windows (b): the H_3 search of 64_item3_h3.py for the code c(P)(x) = P(x) + sum_l mu_l(x) P(pi_l(x)).
Usage: python3 64_rw_h3.py m N k d iters seed
A. random pairs. B. d1, d2 both vanishing on the best-interior set Z found (|Z| <= k - 2), free score 2|int Z|.
C. adaptive: 2k - 2 linear conditions, best member of the kernel pencil, re-impose, repeat."""
import importlib.util, os, random, sys
from math import comb, log2

here = os.path.dirname(__file__)
def load(name, f):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, f))
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod); return mod
L, R = load("lib64", "64_lib.py"), load("rw", "64_rw_lib.py")
m, N, k, d, iters, seed = (int(a) for a in sys.argv[1:7])
F, n, rng = L.GF(m), 1 << N, random.Random(seed)
q, mul, inv = F.q, F.mul, F.inv
pw = L.powers(F, n, k)
win = R.rand_windows(n, d, rng)
mu = [[F.rand(rng) for _ in range(d)] for _ in range(n)]
rnd = lambda j: [F.rand(rng) for _ in range(j)]
sym = lambda coef: R.mix_w(F, mu, L.evaluate(F, pw, coef + [0] * (k - len(coef))), win)
count3 = lambda s1, s2: sum(2 if (a == 0 and b == 0) else (1 if (a == 0 or b == 0 or a == b) else 0) for a, b in zip(s1, s2))

def kernel(rows, ncol):
    rows, piv = [r[:] for r in rows], []
    for c in range(ncol):
        p = next((i for i in range(len(piv), len(rows)) if rows[i][c]), None)
        if p is None: continue
        r = len(piv); rows[r], rows[p] = rows[p], rows[r]
        iv = inv(rows[r][c]); rows[r] = [mul(iv, a) for a in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]; rows[i] = [a ^ mul(f, b) for a, b in zip(rows[i], rows[r])]
        piv.append(c)
    out = []
    for c in (c for c in range(ncol) if c not in piv):
        v = [0] * ncol; v[c] = 1
        for r, pc in enumerate(piv): v[pc] = rows[r][c]
        out.append(v)
    return out

A = [count3(sym(rnd(k)), sym(rnd(k))) for _ in range(300)]
ni, Z = R.best_interior(win, k - 2, rng, restarts=40)
ZP = L.vanishing(F, sorted(Z))
Bs = [count3(sym(L.poly_mul(F, ZP, rnd(k - len(Z)))), sym(L.poly_mul(F, ZP, rnd(k - len(Z))))) for _ in range(100)]
print(f"q=2^{m} N={N} k={k} d={d} 2k={2*k}: A random mean {sum(A)/300:.3f} max {max(A)} (3n/q = {3*n/q:.3f});"
      f" B common zeros |Z|={len(Z)} int={ni}: free {2*ni}, mean {sum(Bs)/100:.2f} max {max(Bs)}")
mrow = [pw[x][:] for x in range(n)]
for x in range(n):
    for c, y in zip(mu[x], win[x][1:]):
        for j in range(k): mrow[x][j] ^= mul(c, pw[y][j])
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
    cands, best = set(), (-1, None)
    for x in range(n):
        for num, den in ((su[0][x], sv[0][x]), (su[1][x], sv[1][x]), (su[0][x] ^ su[1][x], sv[0][x] ^ sv[1][x])):
            if den: cands.add(mul(num, inv(den)))
    for lam in cands:
        w = [a ^ mul(lam, b) for a, b in zip(u, v)]
        c = count3(sym(w[:k]), sym(w[k:]))
        if c > best[0] and any(w[:k]) and any(w[k:]) and w[:k] != w[k:]: best = (c, w)
    return best
allc = [(t, x) for t in range(3) for x in range(n)]
cur, best = rng.sample(allc, 2 * k - 2), (-1, None)
for it in range(iters):
    ker = kernel([cond(t, x) for t, x in cur], 2 * k)
    if len(ker) < 2: cur = rng.sample(allc, 2 * k - 2); continue
    if len(ker) > 2: ker = rng.sample(ker, 2)
    c, w = best_on_pencil(ker[0], ker[1])
    if w is None: cur = rng.sample(allc, 2 * k - 2); continue   # the conditions forced d1 = 0 or d2 = 0
    if c >= best[0]: best = (c, w)
    sat = satisfied(sym(best[1][:k]), sym(best[1][k:]))
    cur = rng.sample(sat, min(len(sat), 2 * k - 2 - rng.randrange(0, 3)))
    while len(cur) < 2 * k - 2: cur.append(rng.choice(allc))
npat = lambda C: sum(comb(n, j) * comb(n - j, C - 2 * j) * 3 ** (C - 2 * j) for j in range(0, C // 2 + 1) if C - 2 * j <= n - j)
estar = max(e for e in range(0, 2 * n - 2 * k) if log2(max(1, npat(2 * k - 1 + e))) >= m * e)
print(f"   C adaptive: best u_2+2u_3 = {best[0]} after {iters} iterations (2k-1 = {2*k-1}, ceiling 2k-1+e* = {2*k-1+estar})")
