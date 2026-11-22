#!/usr/bin/env python3
"""55_lib.py: arithmetic for the referee report 55-referee-note-53.md. Written from scratch (no import from the
scripts of note 53 or earlier notes).

Fields: GF(2^m) as integers modulo an irreducible polynomial given as an int (bit i = coefficient of x^i).
  GFs(m, mod): m <= 16, log tables.
  GFb(m, mod): any m, shift and xor products; `const_mul(c)` gives a fast multiplication by a fixed element.
Polynomials over a field: lists of field elements, low degree first, no trailing zeros ([] is 0).
Everything is exact.
"""
import random

MOD = {
    4: 0x13, 5: 0x25, 6: 0x43, 7: 0x83, 8: 0x11B, 9: 0x211, 10: 0x409, 11: 0x805, 12: 0x1053, 13: 0x201B,
    14: 0x4443, 15: 0x8003, 16: 0x1002B, 20: (1 << 20) | 0b1001, 24: (1 << 24) | 0b11011,
    32: (1 << 32) | 0b10001101, 64: (1 << 64) | 0b11011,
    127: (1 << 127) | 0b11, 521: (1 << 521) | (1 << 32) | 1, 607: (1 << 607) | (1 << 105) | 1,
}


def clmul(a, b):
    r = 0
    while b:
        low = b & -b
        r ^= a * low
        b ^= low
    return r


def polymod(a, mod, m):
    """reduce the F_2-polynomial a modulo mod (degree m)."""
    while a.bit_length() > m:
        a ^= mod << (a.bit_length() - 1 - m)
    return a


def is_irreducible(mod, m):
    """Rabin test for the F_2-polynomial mod of degree m."""
    def frob(v):
        return polymod(clmul(v, v), mod, m)

    def gcd(a, b):
        while b:
            while a.bit_length() >= b.bit_length():
                a ^= b << (a.bit_length() - b.bit_length())
            a, b = b, a
        return a
    primes = [p for p in range(2, m + 1) if m % p == 0 and all(p % q for q in range(2, p))]
    x = 2
    v = x
    powers = {}
    for i in range(1, m + 1):
        v = frob(v)
        powers[i] = v
    if powers[m] != x:
        return False
    for p in primes:
        if gcd(mod, powers[m // p] ^ x).bit_length() > 1:
            return False
    return True


class _GFbase:
    # ---------- polynomials over the field ----------
    @staticmethod
    def trim(p):
        p = list(p)
        while p and p[-1] == 0:
            p.pop()
        return p

    @staticmethod
    def deg(p):
        return len(p) - 1          # -1 for the zero polynomial (trimmed)

    def padd(self, p, q):
        if len(p) < len(q):
            p, q = q, p
        r = list(p)
        for i, b in enumerate(q):
            r[i] ^= b
        return self.trim(r)

    def pscale(self, p, c):
        return self.trim([self.mul(a, c) for a in p])

    def pmul(self, p, q):
        if not p or not q:
            return []
        r = [0] * (len(p) + len(q) - 1)
        mul = self.mul
        for i, a in enumerate(p):
            if a:
                for j, b in enumerate(q):
                    if b:
                        r[i + j] ^= mul(a, b)
        return self.trim(r)

    def psqr(self, p):
        r = [0] * (2 * len(p) - 1) if p else []
        for i, a in enumerate(p):
            r[2 * i] = self.mul(a, a)
        return r

    def pdivmod(self, a, b):
        a = list(a)
        b = self.trim(b)
        assert b
        db = len(b) - 1
        inv = self.inv(b[-1])
        q = [0] * max(0, len(a) - db)
        for i in range(len(a) - 1, db - 1, -1):
            c = a[i]
            if c:
                c = self.mul(c, inv)
                q[i - db] = c
                for j, bj in enumerate(b):
                    if bj:
                        a[i - db + j] ^= self.mul(c, bj)
        return self.trim(q), self.trim(a[:db])

    def pdiv_exact(self, a, b):
        q, r = self.pdivmod(a, b)
        assert not r, "inexact division"
        return q

    def pgcd(self, a, b):
        a, b = self.trim(a), self.trim(b)
        while b:
            a, b = b, self.pdivmod(a, b)[1]
        return self.pscale(a, self.inv(a[-1])) if a else []

    def pderiv(self, p):
        return self.trim([p[i] if i & 1 else 0 for i in range(1, len(p))])

    def peval(self, p, x):
        r = 0
        for c in reversed(p):
            r = self.mul(r, x) ^ c
        return r

    def ppow(self, p, e):
        r = [1]
        while e:
            if e & 1:
                r = self.pmul(r, p)
            p = self.pmul(p, p)
            e >>= 1
        return r

    def pcompose(self, p, q):
        r = []
        for c in reversed(p):
            r = self.padd(self.pmul(r, q), [c] if c else [])
        return r

    def locator(self, pts):
        L = [1]
        for a in pts:
            L = self.pmul(L, [a, 1])
        return L

    # ---------- characteristic 2 specifics ----------
    def is_square_poly(self, p):
        """p in F[X^2] (F perfect: the squares of F[X])."""
        return all(c == 0 for c in p[1::2])

    def psqrt(self, p):
        assert self.is_square_poly(p)
        return self.trim([self.sqrt(c) for c in p[0::2]])

    def odd_part(self, f):
        """monic squarefree polynomial whose roots are the roots of odd multiplicity of f (f != 0).
        f = g h^2, g squarefree: f' = g' h^2, gcd(f, f') = h^2 gcd(g, g') = h^2."""
        f = self.trim(f)
        assert f
        d = self.pderiv(f)
        if not d:
            return [1]
        q = self.pdiv_exact(f, self.pgcd(f, d))
        return self.pscale(q, self.inv(q[-1]))

    def mult_at(self, f, beta):
        f = self.trim(f)
        assert f
        k = 0
        while True:
            q, r = self.pdivmod(f, [beta, 1])
            if r:
                return k
            f = q
            k += 1

    def rand_poly(self, rnd, d, exact=True):
        p = [rnd.randrange(self.q) for _ in range(d + 1)]
        if exact:
            while p[-1] == 0:
                p[-1] = rnd.randrange(self.q)
        return self.trim(p)

    def span(self, basis):
        pts = [0]
        for b in basis:
            pts += [p ^ b for p in pts]
        return pts

    def rand_basis(self, rnd, N):
        while True:
            basis = [rnd.randrange(1, self.q) for _ in range(N)]
            if f2_rank(basis) == N:
                return basis


class GFs(_GFbase):
    """GF(2^m), m <= 16, with log tables."""

    def __init__(self, m, mod=None):
        mod = mod or MOD[m]
        assert is_irreducible(mod, m)
        self.m, self.mod, self.q = m, mod, 1 << m
        order = self.q - 1

        def slow(a, b):
            return polymod(clmul(a, b), mod, m)
        # find a generator
        g = 2
        while True:
            v, k = g, 1
            while v != 1:
                v = slow(v, g)
                k += 1
            if k == order:
                break
            g += 1
        self.EXP = [0] * (2 * order)
        self.LOG = [0] * self.q
        v = 1
        for i in range(order):
            self.EXP[i] = self.EXP[i + order] = v
            self.LOG[v] = i
            v = slow(v, g)
        self.order = order

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.EXP[self.LOG[a] + self.LOG[b]]

    def inv(self, a):
        assert a
        return self.EXP[self.order - self.LOG[a]]

    def pow(self, a, e):
        if a == 0:
            return 0 if e else 1
        return self.EXP[(self.LOG[a] * e) % self.order]

    def sqrt(self, a):
        return self.pow(a, self.q >> 1)


class GFb(_GFbase):
    """GF(2^m), any m; elements are ints."""

    def __init__(self, m, mod=None, check=True):
        mod = mod or MOD[m]
        if check:
            assert is_irreducible(mod, m)
        self.m, self.mod, self.q = m, mod, 1 << m

    def mul(self, a, b):
        return polymod(clmul(a, b), self.mod, self.m)

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
        return self.pow(a, self.q - 2)

    def sqrt(self, a):
        for _ in range(self.m - 1):
            a = self.mul(a, a)
        return a

    def const_mul(self, c):
        """returns f with f(a) = c * a, using byte tables (for many products by the same c)."""
        m, mod = self.m, self.mod
        nb = (m + 7) // 8
        tabs = []
        base = c
        for _ in range(nb):
            t = [0] * 256
            v = base
            for bit in range(8):
                step = 1 << bit
                for i in range(step):
                    t[step + i] = t[i] ^ v
                v <<= 1
                if v >> m:
                    v ^= mod
            base = v
            tabs.append(t)

        def f(a):
            r = 0
            for t in tabs:
                r ^= t[a & 255]
                a >>= 8
                if not a:
                    break
            return r
        return f


# ---------------- F_2 linear algebra on ints ----------------

def f2_rank(rows):
    piv = {}
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    return len(piv)


def f2_echelon(rows):
    """returns (piv, ker): piv maps leading bit -> reduced row, ker is a basis of the left kernel (ints, bit i = row i)."""
    piv = {}
    ker = []
    for i, v in enumerate(rows):
        comb = 1 << i
        while v:
            h = v.bit_length() - 1
            if h in piv:
                pv, pc = piv[h]
                v ^= pv
                comb ^= pc
            else:
                piv[h] = (v, comb)
                break
        if v == 0:
            ker.append(comb)
    return piv, ker


def rm_dim(r, N):
    from math import comb
    return sum(comb(N, i) for i in range(0, r + 1)) if r >= 0 else 0


def boolean_degree(N, mask):
    """degree of the Boolean function on F_2^N whose truth table is mask (bit a = value at a); -1 for zero."""
    n = 1 << N
    anf = [(mask >> a) & 1 for a in range(n)]
    for i in range(N):
        step = 1 << i
        for a in range(n):
            if a & step:
                anf[a] ^= anf[a ^ step]
    d = -1
    for a in range(n):
        if anf[a]:
            d = max(d, bin(a).count("1"))
    return d


def anf_of(N, mask):
    n = 1 << N
    anf = [(mask >> a) & 1 for a in range(n)]
    for i in range(N):
        step = 1 << i
        for a in range(n):
            if a & step:
                anf[a] ^= anf[a ^ step]
    return anf


def power_sums_profile(F, pts_all, gmax):
    """rows for the profile g -> dim Gamma_inf(g) on the point list pts_all: row = [1 | a^1 | a^3 | ...], every block
    of width 8 * ceil(m / 8) bits, the block of the smallest k in the highest bits. Returns (rows, nblocks, width)."""
    m = F.m
    mb = (m + 7) // 8
    ks = list(range(1, gmax + 1, 2))
    B = len(ks)
    rows = []
    fast = hasattr(F, "const_mul")
    for a in pts_all:
        parts = [b"\x01"]
        if a:
            a2 = F.mul(a, a)
            mulc = F.const_mul(a2) if fast else (lambda t, a2=a2: F.mul(t, a2))
            pw = a
            for _ in ks:
                parts.append(pw.to_bytes(mb, "big"))
                pw = mulc(pw)
        else:
            parts.append(bytes(mb * B))
        rows.append(int.from_bytes(b"".join(parts), "big"))
    return rows, B, 8 * mb


def gamma_inf_profile(F, pts_all, gmax):
    """dict g -> dim_{F_2} Gamma_inf(g) for 0 <= g <= gmax, Gamma_inf(g) = {T : p_k(T) = 0, 0 <= k <= g}.
    One elimination: with the blocks ordered by k from the top bit down, the number of pivots whose leading bit lies
    in the blocks of k <= g is the rank of the conditions k <= g (even k follow from p_2k = p_k^2)."""
    rows, B, w = power_sums_profile(F, pts_all, gmax)
    piv = {}
    for v in rows:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    n = len(pts_all)
    cnt = [0] * (B + 1)       # cnt[0]: parity, cnt[j + 1]: block j (k = 2j + 1)
    for h in piv:
        if h >= B * w:
            cnt[0] += 1
        else:
            cnt[1 + (B - 1 - h // w)] += 1
    out = {}
    rank = cnt[0]
    out[0] = n - rank
    j = 0
    for g in range(1, gmax + 1):
        if g & 1:
            rank += cnt[1 + j]
            j += 1
        out[g] = n - rank
    return out


def stratum_bound(N, m, g):
    """max over d < N of dim RM(d, N) - m #{odd k <= g : wt(k) >= N - d}; returns (value, d)."""
    # count odd k <= g by binary weight with a digit recursion
    bits = g.bit_length()
    hist = [0] * (max(N, bits) + 2)

    from math import comb

    def count_le(x, w):
        """number of integers 0 <= k <= x with k odd and weight w."""
        if x < 1 or w < 1:
            return 0
        # odd k = 2 j + 1, j <= (x - 1) // 2, weight(j) = w - 1
        y = (x - 1) // 2
        # numbers 0 <= j <= y of weight w - 1
        tot = 0
        need = w - 1
        L = y.bit_length()
        for i in range(L - 1, -1, -1):
            if (y >> i) & 1:
                if need >= 0:
                    tot += comb(i, need)
                need -= 1
                if need < 0:
                    break
        else:
            if need == 0:
                tot += 1
        return tot

    for w in range(1, bits + 1):
        hist[w] = count_le(g, w)
    best = None
    for d in range(0, N):
        c = sum(hist[w] for w in range(max(N - d, 1), bits + 1))
        val = rm_dim(d, N) - m * c
        if best is None or val > best[0]:
            best = (val, d, c)
    return best


def count_odd_by_weight_bruteforce(g):
    h = {}
    for k in range(1, g + 1, 2):
        w = bin(k).count("1")
        h[w] = h.get(w, 0) + 1
    return h
