# Researcher 21 (referee). GF(2^m) arithmetic on Python ints, written from scratch for the referee checks.
# Field(m, r): F_2[x]/(x^m + r(x)), r given as the bit mask of the low part. K64 is leanVM's K.
import random


class Field:
    def __init__(self, m, r):
        self.m, self.r, self.mask = m, r, (1 << m) - 1
        self.modulus = (1 << m) | r

    def mul(self, a, b):
        # carry-less product, 4 bits of b at a time
        t = (0, a, a << 1, a ^ (a << 1), a << 2, a ^ (a << 2), (a << 1) ^ (a << 2), a ^ (a << 1) ^ (a << 2))
        p = 0
        sh = 0
        while b:
            d = b & 15
            if d:
                v = t[d & 7]
                if d & 8:
                    v ^= a << 3
                p ^= v << sh
            b >>= 4
            sh += 4
        return self.red(p)

    def red(self, p):
        m, mod = self.m, self.modulus
        while p >> m:
            p ^= mod << (p.bit_length() - 1 - m)
        return p

    def sqr(self, a):
        return self.mul(a, a)

    def pow(self, a, e):
        r = 1
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e >>= 1
        return r

    def inv(self, a):
        assert a
        return self.pow(a, (1 << self.m) - 2)

    def rand(self, rng):
        return rng.getrandbits(self.m)


class Field64(Field):
    # faster reduction for x^64 + x^4 + x^3 + x + 1
    def __init__(self):
        super().__init__(64, 0x1B)

    def red(self, p):
        M = self.mask
        h = p >> 64
        p = (p & M) ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4)
        h = p >> 64
        return (p & M) ^ h ^ (h << 1) ^ (h << 3) ^ (h << 4)


K64 = Field64()
SMALL = {4: 0x3, 5: 0x5, 6: 0x3, 7: 0x3, 8: 0x1B, 9: 0x11, 10: 0x9, 12: 0x53, 13: 0x1B, 16: 0x2B, 20: 0x9}


def small_field(m):
    F = Field(m, SMALL[m])
    # the modulus is irreducible iff x^(2^m) = x and gcd conditions hold; for m <= 16 check that every nonzero element is invertible
    if m <= 12:
        for a in range(1, 1 << m):
            assert F.mul(a, F.inv(a)) == 1, "modulus not irreducible"
    else:
        x = 2
        y = x
        for i in range(1, m + 1):
            y = F.sqr(y)
            if i < m and m % i == 0:
                assert y != x
        assert y == x
    return F


def span(basis):
    pts = [0]
    for b in basis:
        pts += [p ^ b for p in pts]
    return pts  # pts[i] = sum of basis[j] over the bits j of i


def power_basis(N):
    return [1 << i for i in range(N)]


def random_basis(F, N, rng):
    while True:
        b = [F.rand(rng) for _ in range(N)]
        if len(set(span(b))) == 1 << N:
            return b


def lin_poly(F, basis):
    """Coefficients c[j] of L_V(X) = sum_j c[j] X^(2^j), V = span(basis) (independent)."""
    c = [1]
    for b in basis:
        v = lin_eval(F, c, b)
        assert v != 0, "dependent basis"
        # L' = L^2 + v L
        new = [0] * (len(c) + 1)
        for j, cj in enumerate(c):
            new[j + 1] ^= F.sqr(cj)
            new[j] ^= F.mul(v, cj)
        c = new
    return c


def lin_eval(F, c, x):
    r = 0
    p = x
    for cj in c:
        r ^= F.mul(cj, p)
        p = F.sqr(p)
    return r


def top_coeffs(F, pts, t):
    """e_0..e_t of prod (1 + s Z) over s in pts (elementary symmetric functions, characteristic two)."""
    e = [1] + [0] * t
    for s in pts:
        if s == 0:
            continue
        for j in range(t, 0, -1):
            if e[j - 1]:
                e[j] ^= F.mul(s, e[j - 1])
    return e


def poly_mul(F, a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    r[i + j] ^= F.mul(x, y)
    return r


def locator(F, pts):
    """Coefficients (low to high) of prod (X - s)."""
    p = [1]
    for s in pts:
        q = [0] * (len(p) + 1)
        for i, x in enumerate(p):
            q[i + 1] ^= x
            if s:
                q[i] ^= F.mul(s, x)
        p = q
    return p


def poly_eval(F, p, x):
    r = 0
    for c in reversed(p):
        r = F.mul(r, x) ^ c
    return r


def deg(p):
    d = len(p) - 1
    while d >= 0 and p[d] == 0:
        d -= 1
    return d


if __name__ == "__main__":
    rng = random.Random(1)
    F = K64
    for _ in range(200):
        a, b, c = F.rand(rng), F.rand(rng), F.rand(rng)
        assert F.mul(a, b) == F.mul(b, a)
        assert F.mul(a, b ^ c) == F.mul(a, b) ^ F.mul(a, c)
        assert F.mul(F.mul(a, b), c) == F.mul(a, F.mul(b, c))
        if a:
            assert F.mul(a, F.inv(a)) == 1
    # generic reduction agrees with the fast one
    G = Field(64, 0x1B)
    for _ in range(200):
        a, b = F.rand(rng), F.rand(rng)
        assert F.mul(a, b) == G.mul(a, b)
    # x^(2^64) = x and x^(2^32) != x: consistent with an irreducible modulus of degree 64 (not a proof of irreducibility)
    y = 2
    for i in range(64):
        y = F.sqr(y)
        if i == 31:
            assert y != 2
    assert y == 2
    for m in SMALL:
        small_field(m)
    print("21_gf self-test ok")
