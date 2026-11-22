"""Note 62: small GF(2^m) arithmetic and linear algebra for the toy checks (pure Python)."""
import random

IRRED = {2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101, 6: 0b1000011, 7: 0b10000011,
         8: 0b100011101, 10: 0b10000001001, 12: 0b1000001010011, 16: 0b10001000000001011}


class GF:
    def __init__(self, m):
        self.m, self.q = m, 1 << m
        poly = IRRED[m]
        self.exp = [0] * (2 * self.q)
        self.log = [0] * self.q
        x = 1
        for i in range(self.q - 1):
            self.exp[i] = x
            self.log[x] = i
            x <<= 1
            if x & self.q:
                x ^= poly
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[(self.q - 1) - self.log[a]]

    def ev(self, coeffs, x):
        """evaluate sum coeffs[i] x^i (Horner)."""
        r = 0
        for c in reversed(coeffs):
            r = self.mul(r, x) ^ c
        return r

    def rank(self, rows):
        return len(self.rref([r[:] for r in rows])[1])

    def rref(self, rows):
        """in-place reduced row echelon form; returns (rows, pivot columns)."""
        piv = []
        r = 0
        ncol = len(rows[0]) if rows else 0
        for c in range(ncol):
            p = None
            for i in range(r, len(rows)):
                if rows[i][c]:
                    p = i
                    break
            if p is None:
                continue
            rows[r], rows[p] = rows[p], rows[r]
            iv = self.inv(rows[r][c])
            rows[r] = [self.mul(iv, v) for v in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c]:
                    f = rows[i][c]
                    rows[i] = [v ^ self.mul(f, w) for v, w in zip(rows[i], rows[r])]
            piv.append(c)
            r += 1
            if r == len(rows):
                break
        return rows, piv

    def nullspace(self, rows, ncol):
        """basis of {v : rows . v = 0}."""
        if not rows:
            return [[1 if i == j else 0 for i in range(ncol)] for j in range(ncol)]
        R, piv = self.rref([r[:] for r in rows])
        free = [c for c in range(ncol) if c not in piv]
        basis = []
        for f in free:
            v = [0] * ncol
            v[f] = 1
            for i, c in enumerate(piv):
                v[c] = R[i][f]
            basis.append(v)
        return basis


def subspace(basis):
    """all elements of the F_2-span of basis, indexed by the bit vector of coordinates."""
    pts = [0]
    for b in basis:
        pts = pts + [p ^ b for p in pts]
    return pts


def independent_basis(F, N, rng):
    """N elements of F linearly independent over F_2."""
    basis, span = [], {0}
    while len(basis) < N:
        b = rng.randrange(1, F.q)
        if b not in span:
            basis.append(b)
            span |= {s ^ b for s in span}
    return basis


def poly_mul(F, a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] ^= F.mul(x, y)
    return r


def subspace_poly(F, pts):
    """coefficients of prod_{w in pts} (X - w)."""
    p = [1]
    for w in pts:
        p = poly_mul(F, p, [w, 1])
    return p
