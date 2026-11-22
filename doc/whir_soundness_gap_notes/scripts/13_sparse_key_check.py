#!/usr/bin/env python3
# Researcher 13. Check of Proposition 3.1 of 13-real-domain.md (sparse top keys) and of the Witt criterion 3.3.
#  (A) For c in Z^D with sum 0 and Walsh spectrum = 0 mod 2^(e+1), on any subspace domain D of GF(2^m):
#      prod_s (1 - sX)^c(s) = 1 + sum_{i=0..e} theta_i(c) X^(2^(e+1) - 2^(e-i))  mod X^(2^(e+1)),
#      and the theta_i are additive in c.
#  (B) Two T-sets share e_1..e_g iff for every odd j <= g the sums of tau(s)^j over the two sets agree modulo
#      2^(l_j), l_j = 1 + floor(log2(g / j)), tau the Teichmuller lift into the Galois ring W(GF(2^m)) / 2^r.
# usage: 13_sparse_key_check.py
import random
from itertools import combinations

M, MOD = 64, (1 << 64) | 0x1B


def mul(a, b, m=M, mod=MOD):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a >> m & 1:
            a ^= mod
    return r


def inv(a):
    r, e = 1, (1 << M) - 2
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


def smul(p, q, L):
    r = [0] * L
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if i + j >= L:
                    break
                if b:
                    r[i + j] ^= mul(a, b)
    return r


def sinv(p, L):
    assert p[0] == 1
    r = [0] * L
    r[0] = 1
    for k in range(1, L):
        acc = 0
        for i in range(1, k + 1):
            if i < len(p) and p[i]:
                acc ^= mul(p[i], r[k - i])
        r[k] = acc
    return r


def key(c, pts, L):
    num, den = [1] + [0] * (L - 1), [1] + [0] * (L - 1)
    for x, mult in c.items():
        for _ in range(abs(mult)):
            if mult > 0:
                num = smul(num, [1, pts[x]], L)
            else:
                den = smul(den, [1, pts[x]], L)
    return smul(num, sinv(den, L), L)


def check_A(N, shape, trials=12):
    rnd = random.Random(13 + N)
    basis = [1 << i for i in range(N)] if shape == "power" else [rnd.getrandbits(64) for _ in range(N)]
    pts = []
    for x in range(1 << N):
        z = 0
        for i in range(N):
            if x >> i & 1:
                z ^= basis[i]
        pts.append(z)
    bad = 0
    tested = 0
    for e in range(1, N - 1):
        L = 1 << (e + 1)
        allowed = {L - (1 << (e - i)) for i in range(e + 1)}

        def rand_c():
            c = {}
            for _ in range(rnd.randint(1, 4)):
                size = rnd.randint(1, N)
                A = rnd.sample(range(N), size)
                g = rnd.choice([-2, -1, 1, 2, 3]) << max(0, e + 1 - size)
                for sub in range(1 << size):
                    x = 0
                    for t in range(size):
                        if sub >> t & 1:
                            x |= 1 << A[t]
                    sign = 1 if (size - bin(sub).count("1")) % 2 == 0 else -1
                    c[x] = c.get(x, 0) + sign * g
            # mix in a translate, which does not change the Walsh congruence
            return c

        for _ in range(trials):
            c1, c2 = rand_c(), rand_c()
            if sum(abs(v) for v in c1.values()) + sum(abs(v) for v in c2.values()) > 600:
                continue
            k1, k2 = key(c1, pts, L), key(c2, pts, L)
            c12 = dict(c1)
            for x, v in c2.items():
                c12[x] = c12.get(x, 0) + v
            k12 = key(c12, pts, L)
            tested += 1
            for j in range(1, L):
                if j not in allowed and (k1[j] or k2[j] or k12[j]):
                    bad += 1
                if j in allowed and k12[j] != k1[j] ^ k2[j]:
                    bad += 1
    print(f"(A) N={N} {shape}: {tested} pairs of lattice elements, all levels e=1..{N-2}: support and additivity", "ok" if not bad else f"FAILED ({bad})")


# ---- (B) Galois ring GR(2^r, m) = Z_{2^r}[x]/(f), f a monic lift of an irreducible polynomial mod 2
def gr_mul(a, b, f, m, q):
    r = [0] * (2 * m - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % q
    for d in range(2 * m - 2, m - 1, -1):
        t = r[d]
        if t:
            r[d] = 0
            for i in range(m):
                r[d - m + i] = (r[d - m + i] - t * f[i]) % q
    return r[:m]


def check_B(m=8, low=0x1B, r=4, seed=1):
    q = 1 << r
    f = [(low >> i) & 1 for i in range(m)]
    rnd = random.Random(seed)
    N = 4
    while True:
        basis = [rnd.randrange(1, 1 << m) for _ in range(N)]
        pts = []
        for x in range(1 << N):
            z = 0
            for i in range(N):
                if x >> i & 1:
                    z ^= basis[i]
            pts.append(z)
        if len(set(pts)) == 1 << N:
            break
    mod = (1 << m) | low
    tau = []
    for s in pts:
        a = [(s >> i) & 1 for i in range(m)]
        for _ in range(m * (r - 1)):
            a = gr_mul(a, a, f, m, q)
        tau.append(a)
        assert sum((v & 1) << i for i, v in enumerate(a)) == s
    pw = {}
    for j in range(1, 8, 2):
        pw[j] = []
        for t in tau:
            a = [1] + [0] * (m - 1)
            for _ in range(j):
                a = gr_mul(a, t, f, m, q)
            pw[j].append(a)
    bad = 0
    cells = 0
    for T in range(3, 10):
        subsets = list(combinations(range(1 << N), T))
        # e_1..e_7 of every subset
        ekeys, wsums = [], []
        for S in subsets:
            e = [1] + [0] * 7
            for x in S:
                for j in range(7, 0, -1):
                    e[j] ^= mul(e[j - 1], pts[x], m, mod)
            ekeys.append(tuple(e[1:]))
            wsums.append({j: [sum(pw[j][x][i] for x in S) % q for i in range(m)] for j in pw})
        for g in range(1, 8):
            ke = [k[:g] for k in ekeys]
            kw = []
            for w in wsums:
                parts = []
                for j in range(1, g + 1, 2):
                    l = 1
                    while j << l <= g:
                        l += 1
                    parts.append(tuple(v % (1 << l) for v in w[j]))
                kw.append(tuple(parts))
            m1, m2 = {}, {}
            ok = True
            for a, b in zip(ke, kw):
                if m1.setdefault(a, b) != b or m2.setdefault(b, a) != a:
                    ok = False
            cells += 1
            bad += not ok
    print(f"(B) GF(2^{m}), n=16, all T-subsets for T=3..9, depths g=1..7: partition by (e_1..e_g) equals partition by Teichmuller power sums in {cells - bad} of {cells} cells")


if __name__ == "__main__":
    check_A(5, "power")
    check_A(5, "random")
    check_A(6, "power", trials=4)
    check_B()
    check_B(m=10, low=0x9, r=4, seed=2)
