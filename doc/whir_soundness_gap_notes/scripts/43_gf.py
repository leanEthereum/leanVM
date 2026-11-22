#!/usr/bin/env python3
"""GF(2^m) (m <= 16, log tables), polynomials (lists, low degree first) and rational functions over it.
Shared by the 43_*.py scripts of 43-low-rate-residuals.md. Written from scratch."""

PRIM = {3: 0xB, 4: 0x13, 5: 0x25, 6: 0x43, 7: 0x83, 8: 0x11D, 9: 0x211, 10: 0x409, 11: 0x805,
        12: 0x1053, 13: 0x201B, 14: 0x4443, 15: 0x8003, 16: 0x1100B}


class GF:
    def __init__(self, m):
        self.m = m
        self.q = 1 << m
        self.order = self.q - 1
        mod = PRIM[m]
        self.EXP = [0] * (2 * self.order)
        self.LOG = [0] * self.q
        v = 1
        for i in range(self.order):
            self.EXP[i] = v
            self.LOG[v] = i
            v <<= 1
            if v >> m:
                v ^= mod
        assert v == 1 and len(set(self.EXP[:self.order])) == self.order, "modulus not primitive"
        for i in range(self.order, 2 * self.order):
            self.EXP[i] = self.EXP[i - self.order]

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.EXP[self.LOG[a] + self.LOG[b]]

    def inv(self, a):
        assert a
        return self.EXP[self.order - self.LOG[a]]

    def div(self, a, b):
        return self.mul(a, self.inv(b))

    def pow(self, a, e):
        if a == 0:
            return 0 if e else 1
        return self.EXP[(self.LOG[a] * e) % self.order]

    def sqrt(self, a):
        return self.pow(a, self.q >> 1)

    # ---- polynomials ----
    @staticmethod
    def trim(p):
        p = list(p)
        while p and p[-1] == 0:
            p.pop()
        return p

    @staticmethod
    def deg(p):
        d = len(p) - 1
        while d >= 0 and p[d] == 0:
            d -= 1
        return d

    def padd(self, p, q):
        if len(p) < len(q):
            p, q = q, p
        r = list(p)
        for i, b in enumerate(q):
            r[i] ^= b
        return self.trim(r)

    def pmul(self, p, q):
        if not p or not q:
            return []
        r = [0] * (len(p) + len(q) - 1)
        E, L = self.EXP, self.LOG
        for i, a in enumerate(p):
            if a:
                la = L[a]
                for j, b in enumerate(q):
                    if b:
                        r[i + j] ^= E[la + L[b]]
        return self.trim(r)

    def pscale(self, p, c):
        return self.trim([self.mul(a, c) for a in p])

    def psq(self, p):
        r = [0] * (2 * len(p) - 1) if p else []
        for i, a in enumerate(p):
            r[2 * i] = self.mul(a, a)
        return r

    def ppow(self, p, e):
        r = [1]
        b = list(p)
        while e:
            if e & 1:
                r = self.pmul(r, b)
            b = self.pmul(b, b)
            e >>= 1
        return r

    def peval(self, p, x):
        r = 0
        for a in reversed(p):
            r = self.mul(r, x) ^ a
        return r

    def pderiv(self, p):
        return self.trim([p[i] if i & 1 else 0 for i in range(1, len(p))])

    def pdivmod(self, a, b):
        a = self.trim(a)
        b = self.trim(b)
        assert b
        db = len(b) - 1
        ib = self.inv(b[-1])
        q = [0] * max(len(a) - db, 0)
        a = list(a)
        for i in range(len(a) - 1, db - 1, -1):
            c = a[i]
            if c:
                c = self.mul(c, ib)
                q[i - db] = c
                lc = self.LOG[c]
                for j, bj in enumerate(b):
                    if bj:
                        a[i - db + j] ^= self.EXP[lc + self.LOG[bj]]
        return self.trim(q), self.trim(a[:db])

    def pgcd(self, a, b):
        a = self.trim(a)
        b = self.trim(b)
        while b:
            a, b = b, self.pdivmod(a, b)[1]
        if a:
            a = self.pscale(a, self.inv(a[-1]))
        return a

    def is_even(self, p):
        """p in F[X^2] ?"""
        return all(c == 0 for c in p[1::2])

    def psqrt(self, p):
        """square root of a polynomial in F[X^2] (coefficients square-rooted)."""
        assert self.is_even(p)
        return self.trim([self.sqrt(c) for c in p[0::2]])

    def even_odd(self, p):
        """p = g(X^2) + X h(X^2); returns (g, h) as polynomials in t = X^2."""
        return self.trim(p[0::2]), self.trim(p[1::2])

    def subst_sq(self, g):
        """g(t) -> g(X^2)."""
        r = [0] * (2 * len(g) - 1) if g else []
        for i, a in enumerate(g):
            r[2 * i] = a
        return r

    # ---- rational functions (num, den), reduced, den monic ----
    def rat(self, n, d=None):
        if d is None:
            d = [1]
        n = self.trim(n)
        d = self.trim(d)
        assert d
        if not n:
            return ([], [1])
        g = self.pgcd(n, d)
        if len(g) > 1:
            n = self.pdivmod(n, g)[0]
            d = self.pdivmod(d, g)[0]
        c = self.inv(d[-1])
        return (self.pscale(n, c), self.pscale(d, c))

    def radd(self, a, b):
        return self.rat(self.padd(self.pmul(a[0], b[1]), self.pmul(b[0], a[1])), self.pmul(a[1], b[1]))

    def rmul(self, a, b):
        return self.rat(self.pmul(a[0], b[0]), self.pmul(a[1], b[1]))

    def rinv(self, a):
        assert a[0]
        return self.rat(a[1], a[0])

    def rdiv(self, a, b):
        return self.rmul(a, self.rinv(b))

    def rderiv(self, a):
        n, d = a
        return self.rat(self.padd(self.pmul(self.pderiv(n), d), self.pmul(n, self.pderiv(d))), self.pmul(d, d))

    def r_in_Ft(self, a):
        """a in F(X^2) ?"""
        return not self.rderiv(a)[0]

    # ---- subspaces ----
    def subspace_poly(self, basis):
        L = [0, 1]
        for b in basis:
            lb = self.peval(L, b)
            assert lb, "dependent basis"
            L = self.padd(self.psq(L), self.pscale(L, lb))
        return L

    @staticmethod
    def span(basis):
        S = [0]
        for b in basis:
            S = S + [s ^ b for s in S]
        return S
