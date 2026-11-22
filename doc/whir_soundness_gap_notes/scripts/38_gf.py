"""GF(2^m) on table lookups, for note 38. Domain D_N = span(1, x, .., x^(N-1)): the element with bit pattern i."""
MOD = {6: 0x43, 8: 0x11D, 10: 0x409, 12: 0x1053, 14: 0x402B, 16: 0x1002D}


class GF:
    def __init__(self, m):
        self.m, self.q, poly = m, 1 << m, MOD[m]
        self.exp, self.log = [0] * (2 * self.q), [0] * self.q
        a = 1
        for i in range(self.q - 1):
            self.exp[i], self.log[a] = a, i
            a <<= 1
            if a >> m:
                a ^= poly
        assert a == 1, "modulus not primitive"
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]

    def mul(self, a, b):
        return 0 if a == 0 or b == 0 else self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[self.q - 1 - self.log[a]]

    def locator(self, pts):
        """coefficients (low to high) of prod (X + p)"""
        c = [1]
        for p in pts:
            n = [0] * (len(c) + 1)
            for i, ci in enumerate(c):
                n[i + 1] ^= ci
                n[i] ^= self.mul(ci, p)
            c = n
        return c

    def polymul(self, a, b):
        r = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    r[i + j] ^= self.mul(ai, bj)
        return r

    def ev(self, c, z):
        r = 0
        for ci in reversed(c):
            r = self.mul(r, z) ^ ci
        return r


def deg(c):
    d = len(c) - 1
    while d >= 0 and c[d] == 0:
        d -= 1
    return d


def padd(a, b):
    if len(a) < len(b):
        a, b = b, a
    r = list(a)
    for i, bi in enumerate(b):
        r[i] ^= bi
    return r
