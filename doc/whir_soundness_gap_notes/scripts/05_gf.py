"""Researcher 05: GF(2^m) helpers in pure python (self-contained).

Elements are ints, bit i = coefficient of x^i, addition is XOR. The domain D_N is the F_2-span of 1, x, ..., x^(N-1),
that is the integers 0 .. 2^N - 1.
"""

MODULI = {
    8: (1 << 8) | 0b11101,       # x^8+x^4+x^3+x^2+1 (primitive)
    12: (1 << 12) | 0b1010011,   # x^12+x^6+x^4+x+1 (primitive)
    16: (1 << 16) | 0b101101,    # x^16+x^5+x^3+x^2+1 (primitive)
    32: (1 << 32) | 0b10001101,  # x^32+x^7+x^3+x^2+1
    64: (1 << 64) | 0b11011,     # x^64+x^4+x^3+x+1, leanVM's K
}


class GF:
    def __init__(self, m):
        self.m = m
        self.mod = MODULI[m]
        self.size = 1 << m
        self.exp = None
        if m <= 16:
            # log tables on the generator x (the moduli above are primitive for m <= 16; checked here)
            q = self.size
            exp = [0] * (2 * q)
            log = [0] * q
            v = 1
            for i in range(q - 1):
                exp[i] = v
                log[v] = i
                v <<= 1
                if v >> m:
                    v ^= self.mod
            assert v == 1 and len(set(exp[: q - 1])) == q - 1, "modulus not primitive"
            for i in range(q - 1, 2 * q):
                exp[i] = exp[i - (q - 1)]
            self.exp, self.log = exp, log

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        if self.exp is not None:
            return self.exp[self.log[a] + self.log[b]]
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
        assert a
        if self.exp is not None:
            return self.exp[(self.size - 1 - self.log[a]) % (self.size - 1)]
        return self.pow(a, self.size - 2)

    def sqrt(self, a):
        return self.pow(a, 1 << (self.m - 1))

    # ---- linearized polynomials: list c with c[j] the coefficient of X^(2^j) ----
    def lin_eval(self, c, x):
        r = 0
        for cj in c:
            r ^= self.mul(cj, x)
            x = self.mul(x, x)
        return r

    def subspace_poly(self, basis):
        """Coefficients of L_V for V spanned by `basis` (assumed independent)."""
        c = [1]
        for b in basis:
            d = self.lin_eval(c, b)
            assert d != 0, "dependent basis"
            new = [0] * (len(c) + 1)
            for j, cj in enumerate(c):
                new[j + 1] ^= self.mul(cj, cj)
                new[j] ^= self.mul(d, cj)
            c = new
        return c

    # ---- dense polynomials: list p with p[i] the coefficient of X^i ----
    def poly_mul(self, p, q):
        r = [0] * (len(p) + len(q) - 1)
        mul = self.mul
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        r[i + j] ^= mul(a, b)
        return r

    def locator(self, pts):
        """prod (X - s), by a product tree."""
        polys = [[s, 1] for s in pts]
        if not polys:
            return [1]
        while len(polys) > 1:
            nxt = [self.poly_mul(polys[i], polys[i + 1]) for i in range(0, len(polys) - 1, 2)]
            if len(polys) & 1:
                nxt.append(polys[-1])
            polys = nxt
        return polys[0]

    def poly_eval(self, p, x):
        r = 0
        for a in reversed(p):
            r = self.mul(r, x) ^ a
        return r


def span(basis):
    s = [0]
    for b in basis:
        s += [v ^ b for v in s]
    return s


def rank_reduce(vectors):
    """Echelon basis (dict pivot -> vector) of the F_2-span of ints."""
    piv = {}
    for v in vectors:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    return piv


def subspaces_by_codim(N, r):
    """All subspaces of F_2^N of codimension r, each as a list of r independent functionals (ints, parity masks),
    in reduced row echelon form so every subspace appears once."""
    out = []

    def gen(pivs):
        # pivs decreasing
        def build(idx, rows):
            if idx == len(pivs):
                out.append(tuple(rows))
                return
            p = pivs[idx]
            free = [i for i in range(p) if i not in pivs]
            for mask in range(1 << len(free)):
                row = 1 << p
                for k, i in enumerate(free):
                    if (mask >> k) & 1:
                        row |= 1 << i
                build(idx + 1, rows + [row])
        build(0, [])

    from itertools import combinations
    for pivs in combinations(range(N - 1, -1, -1), r):
        gen(pivs)
    return out


def parity(v):
    return bin(v).count("1") & 1


def kernel_points(N, funcs):
    """Points of F_2^N (ints) killed by all functionals."""
    return [v for v in range(1 << N) if all(parity(v & f) == 0 for f in funcs)]


def kernel_basis(N, funcs):
    """A basis of the common kernel of the functionals (rows in reduced echelon form with distinct pivots)."""
    pivs = [f.bit_length() - 1 for f in funcs]
    basis = []
    for i in range(N):
        if i in pivs:
            continue
        v = 1 << i
        for f, p in zip(funcs, pivs):
            if (f >> i) & 1:
                v |= 1 << p
        basis.append(v)
    return basis
