#!/usr/bin/env python3
"""Researcher 56. GF(2^m) with log tables (m <= 16) and the Galois ring GR(2^L, m) = W(GF(2^m)) / 2^L with
Teichmuller lifts, for the checks of 56-witt-real-field.md. Written from scratch, no dependencies.

GR(2^L, m) is (Z / 2^L)[x] / (f) with f the 0/1 lift of a primitive polynomial of degree m: an element is a list
of m integers modulo 2^L (coefficients of 1, x, ..., x^(m-1)), a unit iff it is nonzero modulo 2, and its 2-adic
valuation is the least valuation of a coefficient. zeta = [x] is the Teichmuller lift of x, of order 2^m - 1,
and [x^i] = zeta^i."""

PRIM = {3: 0xB, 4: 0x13, 5: 0x25, 6: 0x43, 7: 0x83, 8: 0x11D, 9: 0x211, 10: 0x409, 11: 0x805,
        12: 0x1053, 13: 0x201B, 14: 0x4443, 15: 0x8003, 16: 0x1100B}


class GF:
    def __init__(self, m):
        self.m, self.q, self.order, self.mod = m, 1 << m, (1 << m) - 1, PRIM[m]
        self.EXP = [0] * (2 * self.order)
        self.LOG = [0] * self.q
        v = 1
        for i in range(self.order):
            self.EXP[i] = v
            self.LOG[v] = i
            v <<= 1
            if v >> m:
                v ^= self.mod
        assert v == 1 and len(set(self.EXP[:self.order])) == self.order, "modulus not primitive"
        for i in range(self.order, 2 * self.order):
            self.EXP[i] = self.EXP[i - self.order]

    def mul(self, a, b):
        return self.EXP[self.LOG[a] + self.LOG[b]] if a and b else 0

    def inv(self, a):
        return self.EXP[self.order - self.LOG[a]]

    def pow(self, a, e):
        if a == 0:
            return 0 if e else 1
        return self.EXP[(self.LOG[a] * e) % self.order]

    def frob_inv(self, a, u):
        """a^(2^-u)."""
        return self.pow(a, pow(2, (self.m - u) % self.m, self.order) if self.m > 1 else 1)

    # power series modulo X^(G+1), lists of length G+1, low degree first
    def series_mul_lin(self, r, s):
        """r *= (1 + sX), in place."""
        for j in range(len(r) - 1, 0, -1):
            if r[j - 1]:
                r[j] ^= self.mul(s, r[j - 1])

    def series_div_lin(self, r, s):
        """r /= (1 + sX), in place."""
        for j in range(1, len(r)):
            if r[j - 1]:
                r[j] ^= self.mul(s, r[j - 1])

    def lam(self, c, G):
        """prod_s (1 + sX)^c(s) modulo X^(G+1) for c a dict or list of (s, multiplicity)."""
        r = [0] * (G + 1)
        r[0] = 1
        items = c.items() if isinstance(c, dict) else c
        for s, e in items:
            if s == 0:
                continue
            for _ in range(abs(e)):
                (self.series_mul_lin if e > 0 else self.series_div_lin)(r, s)
        return r

    @staticmethod
    def order_of(r):
        """Least j >= 1 with r[j] != 0, or len(r) if r = 1."""
        for j in range(1, len(r)):
            if r[j]:
                return j
        return len(r)

    def poly_mul(self, p, q):
        r = [0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        r[i + j] ^= self.mul(a, b)
        return r

    def locator(self, pts):
        """Z_S = prod (X - s), low degree first."""
        r = [1]
        for s in pts:
            r = [0] + r
            for j in range(len(r) - 1):
                if r[j + 1]:
                    r[j] ^= self.mul(s, r[j + 1])
        return r


class GR:
    """Galois ring over a GF instance, truncated at 2^L, with the table of Teichmuller lifts zeta^i."""

    def __init__(self, F, L):
        self.F, self.m, self.L, self.mask = F, F.m, L, (1 << L) - 1
        self.taps = [i for i in range(F.m) if F.mod >> i & 1]
        z = [0] * self.m
        z[1 % self.m] = 1
        if self.m == 1:
            z = [1]
        for _ in range(self.m * (L - 1)):
            z = self.mul(z, z)
        self.zeta = z
        self.T = [None] * F.order
        v = [1] + [0] * (self.m - 1)
        for i in range(F.order):
            self.T[i] = v
            v = self.mul(v, z)
        assert v == self.T[0], "zeta does not have order 2^m - 1"

    def mul(self, a, b):
        m = self.m
        r = [0] * (2 * m - 1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    if y:
                        r[i + j] += x * y
        for d in range(2 * m - 2, m - 1, -1):
            t = r[d]
            if t:
                for i in self.taps:
                    r[d - m + i] -= t
        return [x & self.mask for x in r[:m]]

    def teich(self, s, k=1):
        """[s]^k for s in GF (as a bit mask), None for s = 0."""
        if s == 0:
            return None
        return self.T[(self.F.LOG[s] * k) % self.F.order]

    def psum(self, c, k):
        """sum_s c(s) [s]^k for c a dict or list of (s, multiplicity)."""
        r = [0] * self.m
        items = c.items() if isinstance(c, dict) else c
        for s, e in items:
            if s == 0 or e == 0:
                continue
            t = self.T[(self.F.LOG[s] * k) % self.F.order]
            for i in range(self.m):
                r[i] += e * t[i]
        return [x & self.mask for x in r]

    def val(self, a):
        """2-adic valuation, L if a = 0 modulo 2^L."""
        v = self.L
        for x in a:
            if x:
                v = min(v, (x & -x).bit_length() - 1)
        return v

    def red(self, a, v=0):
        """(a / 2^v) modulo 2 as an element of GF."""
        r = 0
        for i, x in enumerate(a):
            if x >> v & 1:
                r |= 1 << i
        return r


def wt(k):
    return bin(k).count("1")


def v2(j):
    return (j & -j).bit_length() - 1


def span(F, basis):
    """Elements s(x) = sum x_i b_i indexed by the bit mask x."""
    pts = [0]
    for b in basis:
        pts += [p ^ b for p in pts]
    return pts


def random_basis(F, N, rng):
    while True:
        basis = [rng.randrange(1, F.q) for _ in range(N)]
        pts = span(F, basis)
        if len(set(pts)) == 1 << N:
            return basis


def power_basis(F, N):
    return [1 << i for i in range(N)]


def witt_order(R, c, G):
    """min over odd k <= G of k 2^v2(sum c(s)[s]^k), capped at G + 1: the prediction of Theorem 1."""
    best = G + 1
    for k in range(1, G + 1, 2):
        v = R.val(R.psum(c, k))
        if v < R.L or k << R.L > G:
            best = min(best, k << v)
        else:
            raise ValueError("L too small")
    return min(best, G + 1)
