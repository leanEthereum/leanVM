# 30_checks: numerical checks for note 30.
#   python3 30_checks.py
# 1. Frobenius counterexample to Lovett's Conjecture 1.5 in characteristic 2 (three squares, k = 3).
# 2. The Hankel / Cauchy-Binet form of the three-set determinant (Proposition 4.1) against the direct rank, N = 3.
# 3. Degree of the determinant and the sum of the coranks of the merges (Proposition 3.3) on two terminal patterns.
# 4. The conditional list bound of note 17 Theorem 5.1 at N = 25..28, rate 1/2.
import sys, random, itertools, math
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from importlib import import_module
L = import_module('30_lib')
rng = random.Random(30)

# 1
a = [rng.getrandbits(64) for _ in range(3)]
polys = [[L.gmul(x, x), 0, 1] for x in a]  # (X - a_i)^2 = X^2 + a_i^2
ker = L.kernel(polys)
print('1. three squares (X - a_i)^2, k = 3, V(3) holds: kernel dimension', len(ker), '(1 = dependent)')

# 2
def hankel_singular(pts, R0, R1, R2, delta):
    s = delta + 1 - len(R2)
    if s <= 0:
        return None
    z0 = L.locator(pts, [1 if p in R0 else 0 for p in range(len(pts))])
    z1 = L.locator(pts, [1 if p in R1 else 0 for p in range(len(pts))])
    z2 = L.locator(pts, [1 if p in R2 else 0 for p in range(len(pts))])
    dz0 = [z0[i] if i % 2 == 1 else 0 for i in range(1, len(z0))]  # derivative in characteristic 2
    w = {}
    for p in R0:
        x = pts[p]
        w[p] = L.gmul(L.peval(z2, x), L.ginv(L.gmul(L.peval(dz0, x), L.peval(z1, x))))
    mu = []
    for t in range(2 * s - 1):
        v = 0
        for p in R0:
            v ^= L.gmul(L.gpow(pts[p], t), w[p])
        mu.append(v)
    cols = [[mu[i + j] for i in range(s)] for j in range(s)]
    return len(L.kernel(cols)) > 0
P3 = L.subspace(3, rng)
agree = dis = 0
for delta in (2, 3):
    for _ in range(400):
        perm = list(range(8)); rng.shuffle(perm)
        while True:
            r0 = rng.randint(1, delta); r1 = rng.randint(1, delta); r2 = 2 * delta + 2 - r0 - r1
            if 0 <= r2 <= delta: break
        if rng.random() < 0.5:  # periodic patterns half of the time
            aa = rng.randrange(1, 8); cl = {}
            for p in range(8): cl.setdefault(min(p, p ^ aa), []).append(p)
            cls = list(cl.values()); rng.shuffle(cls); perm = [p for c in cls for p in c]
        R0, R1, R2 = perm[:r0], perm[r0:r0 + r1], perm[r0 + r1:r0 + r1 + r2]
        ms = [[1 if p in R else 0 for p in range(8)] for R in (R0, R1, R2)]
        direct = len(L.pattern_kernel(P3, ms, delta + 1)[0]) > 0
        h = hankel_singular(P3, R0, R1, R2, delta)
        if h is None: continue
        if h == direct: agree += 1
        else: dis += 1
print('2. Hankel form against direct rank, N = 3, delta = 2, 3: agree', agree, 'disagree', dis)

# 3
P4 = L.subspace(4, rng); P3b = L.subspace(3, rng)
for R in [(0x0357, 0x3c28, 0xc080), (0x0357, 0x54a8, 0xa800)]:
    delta = 7
    ms = [[r >> p & 1 for p in range(16)] for r in R]
    r = [sum(m) for m in ms]; s = [delta + 1 - x for x in r]
    deg = sum(si * ri + si * (si - 1) // 2 for si, ri in zip(s, r)) - delta * (delta + 1) // 2
    cor = [len(L.pattern_kernel(P3b, [L.push(m, a) for m in ms], delta + 1)[0]) for a in range(1, 16)]
    print('3. terminal pattern sizes', r, 'deg det =', deg, 'sum of coranks of the 15 merges =', sum(cor), 'upstairs corank', len(L.pattern_kernel(P4, ms, delta + 1)[0]))

# 4
def log2_gauss(N, c):
    v = 0.0
    for i in range(c):
        v += math.log2(2 ** (N - i) - 1) - math.log2(2 ** (c - i) - 1)
    return v
print('4. note 17 Theorem 5.1 (conditional on Conjecture P), rate 1/2, log2 of the bound:')
print('   tau      ' + '  '.join('N=%d' % N for N in (25, 26, 27, 28)))
for tau in (0.70, 0.69, 0.6875, 0.68, 0.675, 0.67):
    row = []
    for N in (25, 26, 27, 28):
        n = 2 ** N; k = n // 2; T = math.ceil(tau * n)
        eps = 3 * T - n - 2 * k + 2
        pi = 1 << (eps - 1).bit_length()
        c = N - int(math.log2(pi)); dstar = (k - 1) // pi
        v = log2_gauss(N, c) + sum(math.log2((n - k + i) / (T - k + i)) for i in range(1, dstar + 2))
        row.append('%6.1f' % v)
    print('   %.4f  ' % tau + '  '.join(row))
