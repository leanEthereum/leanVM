"""GF(2^m) arithmetic in pure python, subspace domains, locators, subspace polynomials.

Elements are ints (bit i = coefficient of x^i). Addition is XOR.
Used by the other 02_*.py scripts of researcher 02.
"""
import random

# modulus polynomials (bit masks, including the leading term); all checked irreducible by is_irreducible below
MODULI = {
    4: (1 << 4) | 0b11,            # x^4+x+1
    5: (1 << 5) | 0b101,           # x^5+x^2+1
    6: (1 << 6) | 0b11,            # x^6+x+1
    7: (1 << 7) | 0b11,            # x^7+x+1
    8: (1 << 8) | 0b11101,         # x^8+x^4+x^3+x^2+1
    10: (1 << 10) | 0b1001,        # x^10+x^3+1
    12: (1 << 12) | 0b1010011,     # x^12+x^6+x^4+x+1
    16: (1 << 16) | 0b101101,      # x^16+x^5+x^3+x^2+1
    20: (1 << 20) | 0b1001,        # x^20+x^3+1
    32: (1 << 32) | 0b10001101,    # x^32+x^7+x^3+x^2+1
    64: (1 << 64) | 0b11011,       # x^64+x^4+x^3+x+1  (leanVM's K)
}


class GF:
    def __init__(self, m, modulus=None):
        self.m = m
        self.mod = modulus if modulus is not None else MODULI[m]
        self.low = self.mod ^ (1 << m)
        self.size = 1 << m
        self.tab = None
        if m <= 12:
            self._build_tables()

    # carry-less multiply and reduce
    def _mul_slow(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
        m, mod = self.m, self.mod
        for i in range(r.bit_length() - 1, m - 1, -1):
            if (r >> i) & 1:
                r ^= mod << (i - m)
        return r

    def _build_tables(self):
        # find a primitive element, build log/exp tables
        q = self.size
        for g in range(2, q):
            exp = [1] * (q - 1)
            seen = 1
            x = 1
            ok = True
            for i in range(1, q - 1):
                x = self._mul_slow(x, g)
                if x == 1:
                    ok = False
                    break
                exp[i] = x
            if ok:
                break
        self.exp = exp + exp
        self.log = [0] * q
        for i, v in enumerate(exp):
            self.log[v] = i
        self.tab = True

    def mul(self, a, b):
        if self.tab:
            if a == 0 or b == 0:
                return 0
            return self.exp[self.log[a] + self.log[b]]
        return self._mul_slow(a, b)

    def sq(self, a):
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
        assert a != 0
        if self.tab:
            return self.exp[(self.size - 1 - self.log[a]) % (self.size - 1)]
        return self.pow(a, self.size - 2)

    def rand(self, rng=random):
        return rng.getrandbits(self.m)

    # ---- polynomials over the field: lists of coefficients, low degree first ----
    def poly_eval(self, p, x):
        r = 0
        for c in reversed(p):
            r = self.mul(r, x) ^ c
        return r

    def poly_mul(self, p, q):
        r = [0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        r[i + j] ^= self.mul(a, b)
        return r

    def locator(self, pts):
        """prod (X - s), low degree first."""
        p = [1]
        for s in pts:
            q = [0] * (len(p) + 1)
            for i, c in enumerate(p):
                q[i + 1] ^= c
                q[i] ^= self.mul(c, s)
            p = q
        return p

    def interpolate(self, xs, ys):
        """Lagrange interpolation, returns coefficients low first (degree < len(xs))."""
        k = len(xs)
        full = self.locator(xs)
        res = [0] * k
        for i in range(k):
            # full / (X - xs[i]) by synthetic division
            q = [0] * k
            c = 0
            for d in range(k, 0, -1):
                c = full[d] ^ self.mul(c, xs[i])
                q[d - 1] = c
            den = self.poly_eval(q, xs[i])
            s = self.mul(ys[i], self.inv(den))
            if s:
                for d in range(k):
                    res[d] ^= self.mul(q[d], s)
        return res


def span(basis):
    """All elements of the F_2-span, index i = sum of basis[j] over bits j of i."""
    pts = [0]
    for b in basis:
        pts += [p ^ b for p in pts]
    return pts


def rank_f2(vecs):
    """Rank of a list of ints as F_2 vectors; also returns the reduced basis (dict pivot -> vec)."""
    piv = {}
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    return len(piv), piv


def in_span(piv, v):
    while v:
        h = v.bit_length() - 1
        if h in piv:
            v ^= piv[h]
        else:
            return False
    return True


def power_basis(F, N):
    """1, x, ..., x^(N-1): leanVM's domain shape."""
    return [1 << i for i in range(N)]


def random_basis(F, N, rng):
    while True:
        b = [F.rand(rng) for _ in range(N)]
        if rank_f2(b)[0] == N:
            return b


def subspace_poly(F, basis):
    """Coefficients c_0..c_s of L_V(X) = sum c_i X^(2^i) (c_s = 1) for V = span(basis)."""
    c = [1]  # L_{0}(X) = X
    for b in basis:
        # value of current L at b
        v = 0
        p = b
        for ci in c:
            v ^= F.mul(ci, p)
            p = F.sq(p)
        assert v != 0, "basis not independent"
        # L_new = L^2 + v L
        new = [0] * (len(c) + 1)
        for i, ci in enumerate(c):
            new[i + 1] ^= F.sq(ci)
            new[i] ^= F.mul(v, ci)
        c = new
    return c


def lin_eval(F, c, x):
    v = 0
    p = x
    for ci in c:
        v ^= F.mul(ci, p)
        p = F.sq(p)
    return v


def is_irreducible(mod):
    """Rabin test over F_2 for the bit-mask polynomial mod."""
    m = mod.bit_length() - 1
    F = GF(m, mod) if m > 12 else None

    def mulmod(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            b >>= 1
            a <<= 1
        for i in range(r.bit_length() - 1, m - 1, -1):
            if (r >> i) & 1:
                r ^= mod << (i - m)
        return r

    def gcd(a, b):
        while b:
            while a.bit_length() >= b.bit_length() and a:
                a ^= b << (a.bit_length() - b.bit_length())
            a, b = b, a
        return a

    def frob_iter(t):
        x = 2
        for _ in range(t):
            x = mulmod(x, x)
        return x

    if frob_iter(m) != 2:
        return False
    primes = [p for p in range(2, m + 1) if m % p == 0 and all(p % d for d in range(2, p))]
    for p in primes:
        if gcd(mod, frob_iter(m // p) ^ 2) != 1:
            return False
    return True


if __name__ == "__main__":
    for m, mod in MODULI.items():
        assert is_irreducible(mod), m
    print("all moduli irreducible:", sorted(MODULI))
    rng = random.Random(1)
    for m in (4, 8, 16, 64):
        F = GF(m)
        for _ in range(200):
            a, b, c = F.rand(rng), F.rand(rng), F.rand(rng)
            assert F.mul(a, b ^ c) == F.mul(a, b) ^ F.mul(a, c)
            assert F.mul(F.mul(a, b), c) == F.mul(a, F.mul(b, c))
            if a:
                assert F.mul(a, F.inv(a)) == 1
        # subspace polynomial vanishes on the span and is monic linearized
        basis = random_basis(F, min(4, m), rng)
        c = subspace_poly(F, basis)
        assert all(lin_eval(F, c, v) == 0 for v in span(basis))
        loc = F.locator(span(basis))
        assert all((loc[1 << i] == c[i]) for i in range(len(c)))
        assert sum(1 for x in loc if x) <= len(c)
    print("field and subspace polynomial self-tests pass")
