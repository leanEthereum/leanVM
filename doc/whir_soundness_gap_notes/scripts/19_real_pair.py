#!/usr/bin/env python3
# Researcher 19. An explicit non-formal coincidence on the real domains D = span(1, x, .., x^(N-1)) in
# K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), N = 25..28 (note 19, Proposition 5.1).
# V  = {f in D : f(0) = f(1) = coefficient of x^(N-1)}   (kernel of the plane pi of D^*),
# V' = {f in D : x^2 + x + 1 divides f}                   (kernel of the plane pi').
# Checks: pi and pi' meet in 0; the six dual points a_phi = 1/delta_phi sum to 0 (formal) and their inverses
# sum to 0 (the coincidence); the sum of the inverse cubes is not 0; and, independently of note 19's Theorem 1,
# c_1(V) = c_1(V') where L_V = X^(n/4) + c_1 X^(n/8) + .., so deg(L_V - L_V') <= n/16.
# For N <= 10 it also multiplies out Z_A and Z_B for A = V minus V', B = V' minus V.
# usage: 19_real_pair.py [N ...] [--field m r]
import sys
def mk(m, r):
    def mul(a, b):
        z = 0
        while b:
            if b & 1: z ^= a
            b >>= 1; a <<= 1
            if a >> m & 1: a ^= (1 << m) | r
        return z
    def inv(a):
        x, s = 1, mul(a, a)
        for _ in range(m - 1): x = mul(x, s); s = mul(s, s)
        return x
    return mul, inv
def par(x): return bin(x).count("1") & 1
def kernel(masks, N):
    # basis (coordinate bitmasks) of {x in F_2^N : par(mask & x) = 0 for all masks}
    rows = []
    for mk_ in masks:
        v = mk_
        for (p, r) in rows:
            if v >> p & 1: v ^= r
        if v: rows.append((v.bit_length() - 1, v))
    rows2 = []
    for i, (p, r) in enumerate(rows):          # full reduction
        for (q, s) in rows[i + 1:]:
            if r >> q & 1: r ^= s
        rows2.append((p, r))
    piv = {p for p, _ in rows2}; basis = []
    for f in range(N):
        if f in piv: continue
        x = 1 << f
        for (p, r) in rows2:
            if r >> f & 1: x |= 1 << p
        basis.append(x)
    for x in basis: assert all(par(mk_ & x) == 0 for mk_ in masks)
    return basis
def subspace_poly(mul, basis):
    # returns (eval, c1): eval(t) = L_V(t), c1 = coefficient of X^(|V|/2)
    steps = []; c1 = 0; vs = list(basis)
    for i in range(len(vs)):
        p = vs[i]; assert p
        for j in range(i + 1, len(vs)): vs[j] = mul(vs[j], vs[j] ^ p)
        steps.append(p); c1 = mul(c1, c1) ^ p
    def ev(t):
        for p in steps: t = mul(t, t ^ p)
        return t
    return ev, c1
def run(N, m, r):
    mul, inv = mk(m, r)
    ev0 = 1; ev1 = (1 << N) - 1; finf = 1 << (N - 1)
    al = sum(1 << i for i in range(N) if i % 3 in (0, 2)); be = sum(1 << i for i in range(N) if i % 3 in (1, 2))
    pi1 = [ev0 ^ finf, ev1 ^ finf, ev0 ^ ev1]; pi2 = [al, be, al ^ be]
    span4 = {0}
    for g in [pi1[0], pi1[1], pi2[0], pi2[1]]: span4 |= {v ^ g for v in span4}
    assert len(span4) == 16, "planes meet"
    def delta(phi):
        H = kernel([phi], N); ev, _ = subspace_poly(mul, H)
        t = next(1 << i for i in range(N) if phi >> i & 1)
        return ev(t)
    d1 = [delta(p) for p in pi1]; d2 = [delta(p) for p in pi2]
    a1 = [inv(d) for d in d1]; a2 = [inv(d) for d in d2]
    assert a1[0] ^ a1[1] == a1[2] and a2[0] ^ a2[1] == a2[2], "a not additive"
    P1 = 0; P3 = 0
    for d in d1 + d2: P1 ^= d; P3 ^= mul(d, mul(d, d))
    _, c1V = subspace_poly(mul, kernel(pi1[:2], N)); _, c1W = subspace_poly(mul, kernel(pi2[:2], N))
    # cross-check of c_1 against the dual formula: c_1(V)^2 = D_1 + iota_2(pi)^(1/2)... only equality is used
    print("N=%d m=%d: sum of 1/a over the six points = %x, sum of 1/a^3 = %x, c1(V) = %016x, c1(V') = %016x  %s" %
          (N, m, P1, P3, c1V, c1W, "COINCIDENCE" if P1 == 0 and c1V == c1W else "no coincidence"))
    if N <= 10: brute(N, mul, kernel(pi1[:2], N), kernel(pi2[:2], N))
    return P1 == 0 and c1V == c1W and P3 != 0
def brute(N, mul, bV, bW):
    # direct check on the sets: A = V minus V', B = V' minus V have 3n/16 points each and Z_A - Z_B is a constant
    def pts(b):
        P = [0]
        for x in b: P += [p ^ x for p in P]
        return set(P)
    V, W = pts(bV), pts(bW); A, B = V - W, W - V
    def Z(S):
        poly = [1]
        for s_ in S:
            new = [0] * (len(poly) + 1)
            for i, c in enumerate(poly): new[i + 1] ^= c; new[i] ^= mul(c, s_)
            poly = new
        return poly
    za, zb = Z(A), Z(B); diff = [x ^ y for x, y in zip(za, zb)]
    assert len(A) == len(B) == 3 * (1 << N) // 16 and all(c == 0 for c in diff[1:]) and diff[0] != 0
    print("   brute force N=%d: |A| = |B| = %d, Z_A - Z_B = %x (a nonzero constant)" % (N, len(A), diff[0]))
if __name__ == "__main__":
    args = sys.argv[1:]; m, r = 64, 0x1b
    if "--field" in args:
        i = args.index("--field"); m, r = int(args[i + 1]), int(args[i + 2], 0); del args[i:i + 3]
    Ns = [int(a) for a in args] or [25, 26, 27, 28]
    ok = all([run(N, m, r) for N in Ns])
    print("all coincidences confirmed, none survives the cubes" if ok else "FAILED")
