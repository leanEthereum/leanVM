# 30_orders: order of vanishing of the three-set determinant along each linear form a of D (note 30, section 6.2),
# by interpolation in the basis variable a, against the degree of the determinant (Proposition 4.3).
#   python3 30_orders.py        (a few minutes)
import sys, random
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from importlib import import_module
L = import_module('30_lib')
rng = random.Random(11)
def det(M):
    M = [row[:] for row in M]; n = len(M); d = 1
    for c in range(n):
        r = c
        while r < n and not M[r][c]: r += 1
        if r == n: return 0
        M[c], M[r] = M[r], M[c]
        d = L.gmul(d, M[c][c]); inv = L.ginv(M[c][c])
        for rr in range(c + 1, n):
            if M[rr][c]:
                f = L.gmul(M[rr][c], inv)
                M[rr] = [x ^ L.gmul(f, y) for x, y in zip(M[rr], M[c])]
    return d
def matrix(pts, ms, K):
    cols = []
    for m in ms:
        z = L.locator(pts, m)
        for e in range(K - (len(z) - 1)):
            v = [0] * K
            for l, c in enumerate(z): v[e + l] = c
            cols.append(v)
    return [[cols[c][r] for c in range(K)] for r in range(K)]
def interp_low(xs, ys):
    # lowest nonzero coefficient index of the interpolating polynomial (Newton -> monomial), small sizes
    n = len(xs); coef = [0] * n; basis = [1]
    dd = ys[:]
    for j in range(n):
        if j > 0:
            for i in range(n - 1, j - 1, -1):
                dd[i] = L.gmul(dd[i] ^ dd[i - 1], L.ginv(xs[i] ^ xs[i - j]))
        for i, b in enumerate(basis): coef[i] ^= L.gmul(dd[j], b)
        basis = L.pmul(basis, [xs[j], 1])
    for i, c in enumerate(coef):
        if c: return i
    return None
def valuations(N, ms, delta):
    n = 1 << N; K = delta + 1
    r = [sum(m) for m in ms]; s = [K - x for x in r]
    deg = sum(si * ri + si * (si - 1) // 2 for si, ri in zip(s, r)) - delta * (delta + 1) // 2
    vals = []
    for a in range(1, n):
        # basis containing a: complete a to a basis
        basis = [a]; span = {0, a}
        for e in range(N):
            v = 1 << e
            if v not in span:
                basis.append(v); span |= {x ^ v for x in span}
        bv = [rng.getrandbits(64) for _ in basis]
        def pts_for(eps):
            vals_ = [eps] + bv[1:]
            pts = [None] * n
            for mask in range(n):
                lab = 0; x = 0
                for i in range(N):
                    if mask >> i & 1: lab ^= basis[i]; x ^= vals_[i]
                pts[lab] = x
            return pts
        xs = [rng.getrandbits(64) for _ in range(deg + 2)]
        ys = [det(matrix(pts_for(e), ms, K)) for e in xs]
        vals.append(interp_low(xs, ys))
    return deg, vals
def randpat(N, delta):
    n = 1 << N
    while True:
        r0 = rng.randint(1, delta); r1 = rng.randint(1, delta); r2 = 2 * delta + 2 - r0 - r1
        if 0 <= r2 <= delta and r0 + r1 + r2 <= n: break
    perm = list(range(n)); rng.shuffle(perm)
    ms = [[0] * n for _ in range(3)]
    for j, p in enumerate(perm[:2 * delta + 2]): ms[0 if j < r0 else 1 if j < r0 + r1 else 2][p] = 1
    return ms
for N, delta, cnt in ((3, 2, 12), (3, 3, 12), (4, 3, 6), (4, 5, 4), (4, 7, 3)):
    for _ in range(cnt):
        ms = randpat(N, delta)
        deg, vals = valuations(N, ms, delta)
        if None in vals: print(N, delta, [sum(m) for m in ms], 'det identically zero'); continue
        print(N, delta, [sum(m) for m in ms], 'deg', deg, 'sum of valuations along the linear forms', sum(vals), 'remainder degree', deg - sum(vals))
ms = [[r >> p & 1 for p in range(16)] for r in (0x0357, 0x3c28, 0xc080)]
print('terminal', valuations(4, ms, 7))
