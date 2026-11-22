"""Note 64: table-based GF(2^m), Reed-Solomon on D = {0..2^N-1} (span of 1, x, .., x^(N-1)), window-mixed code.

Positions are integers v in [0, 2^N); the field element of position v is v itself (bits = coordinates on the
basis b_i = x^i), so the window of v for directions dirs is {v} + {v ^ (1 << i) : i in dirs}.
"""
import random

MODS = {4: 0x13, 8: 0x11D, 16: 0x1100B}


class GF:
    def __init__(self, m):
        self.m, self.q, mod = m, 1 << m, MODS[m]
        self.exp, self.log = [0] * (2 * self.q), [0] * self.q
        a = 1
        for i in range(self.q - 1):
            self.exp[i], self.log[a] = a, i
            a <<= 1
            if a >> m:
                a ^= mod
        assert a == 1 and len(set(self.exp[: self.q - 1])) == self.q - 1, "modulus not primitive"
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[self.q - 1 - self.log[a]]

    def rand(self, rng):
        return rng.randrange(self.q)


def powers(F, n, k):
    """pw[x][j] = x^j for x in D, j < k."""
    pw = []
    for x in range(n):
        row, a = [1] * k, 1
        for j in range(1, k):
            a = F.mul(a, x)
            row[j] = a
        pw.append(row)
    return pw


def evaluate(F, pw, coef):
    """Evaluations on D of the polynomial with coefficient list coef (degree < len(coef))."""
    exp, log = F.exp, F.log
    nz = [(j, log[c]) for j, c in enumerate(coef) if c]
    out = []
    for row in pw:
        s = 0
        for j, lc in nz:
            a = row[j]
            if a:
                s ^= exp[log[a] + lc]
        out.append(s)
    return out


def window(v, dirs):
    return [v] + [v ^ (1 << i) for i in dirs]


def sample_mu(F, n, r, rng):
    return [[F.rand(rng) for _ in range(r)] for _ in range(n)]


def mix(F, mu, ev, dirs):
    """Mixed codeword from the evaluations ev of P."""
    exp, log = F.exp, F.log
    out = []
    for v, row in enumerate(mu):
        s = 0
        for c, w in zip(row, window(v, dirs)):
            a = ev[w]
            if a and c:
                s ^= exp[log[a] + log[c]]
        out.append(s)
    return out


def poly_mul(F, p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] ^= F.mul(a, b)
    return r


def vanishing(F, pts):
    p = [1]
    for z in pts:
        p = poly_mul(F, p, [z, 1])
    return p


def interior(S, N, dirs=None):
    S = set(S)
    dirs = range(N) if dirs is None else dirs
    return [v for v in S if all((v ^ (1 << i)) in S for i in dirs)]


def ball(N, centre, r):
    return [v for v in range(1 << N) if bin(v ^ centre).count("1") <= r]


def rank(F, rows):
    """Rank over GF(2^m) of a list of rows (destroyed)."""
    rows = [r[:] for r in rows]
    rk, ncol = 0, len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        pr, iv = rows[rk], F.inv(rows[rk][c])
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = F.mul(rows[i][c], iv)
                rows[i] = [a ^ F.mul(f, b) for a, b in zip(rows[i], pr)]
        rk += 1
    return rk
