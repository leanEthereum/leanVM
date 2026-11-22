#!/usr/bin/env python3
"""Note 63: small-field tools. GF(2^m) by log tables, Reed-Solomon on a subspace domain, linear algebra.

Positions are the integers 0 .. 2^N - 1; the field element of position v is v itself, so
D = span(1, x, .., x^(N-1)) in the polynomial basis and b_i = 2^i. Pure python, no dependencies.
"""
import random

POLY = {4: 0x13, 6: 0x43, 8: 0x11D, 10: 0x409, 12: 0x1053, 16: 0x1100B}


class GF:
    def __init__(self, m):
        self.m, self.q = m, 1 << m
        p = POLY[m]
        self.exp = [0] * (2 * self.q)
        self.log = [0] * self.q
        x = 1
        for i in range(self.q - 1):
            self.exp[i] = x
            self.log[x] = i
            x <<= 1
            if x >> m:
                x ^= p
        for i in range(self.q - 1, 2 * self.q):
            self.exp[i] = self.exp[i - (self.q - 1)]

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def inv(self, a):
        return self.exp[(self.q - 1) - self.log[a]]

    def div(self, a, b):
        if a == 0:
            return 0
        return self.exp[self.log[a] + (self.q - 1) - self.log[b]]

    def rand(self, rng, nonzero=False):
        return rng.randrange(1 if nonzero else 0, self.q)

    def peval(self, coef, x):
        """coef[0] + coef[1] x + ... (Horner)."""
        acc = 0
        for c in reversed(coef):
            acc = self.mul(acc, x) ^ c
        return acc

    def pmul(self, a, b):
        out = [0] * (len(a) + len(b) - 1)
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    out[i + j] ^= self.mul(ai, bj)
        return out

    def vanishing(self, pts):
        p = [1]
        for z in pts:
            p = self.pmul(p, [z, 1])
        return p

    def interpolate(self, xs, ys):
        """coefficients of the polynomial of degree < len(xs) through the points (Newton)."""
        n = len(xs)
        dd = list(ys)
        for j in range(1, n):
            for i in range(n - 1, j - 1, -1):
                dd[i] = self.div(dd[i] ^ dd[i - 1], xs[i] ^ xs[i - j])
        coef = [dd[n - 1]]
        for i in range(n - 2, -1, -1):
            coef = self.pmul(coef, [xs[i], 1])
            coef[0] ^= dd[i]
        return coef

    def degree(self, coef):
        d = len(coef) - 1
        while d >= 0 and coef[d] == 0:
            d -= 1
        return d

    def rank(self, rows):
        """rank of a list of rows over the field (rows are copied)."""
        M = [list(r) for r in rows]
        rk, ncol = 0, len(M[0]) if M else 0
        for c in range(ncol):
            piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            iv = self.inv(M[rk][c])
            M[rk] = [self.mul(iv, v) for v in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c]:
                    f = M[i][c]
                    M[i] = [a ^ self.mul(f, b) for a, b in zip(M[i], M[rk])]
            rk += 1
            if rk == len(M):
                break
        return rk

    def kernel(self, rows, ncol):
        """basis of {v : rows . v = 0}."""
        M = [list(r) for r in rows]
        pivs, rk = [], 0
        for c in range(ncol):
            piv = next((i for i in range(rk, len(M)) if M[i][c]), None)
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            iv = self.inv(M[rk][c])
            M[rk] = [self.mul(iv, v) for v in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c]:
                    f = M[i][c]
                    M[i] = [a ^ self.mul(f, b) for a, b in zip(M[i], M[rk])]
            pivs.append(c)
            rk += 1
        free = [c for c in range(ncol) if c not in pivs]
        basis = []
        for fc in free:
            v = [0] * ncol
            v[fc] = 1
            for i, pc in enumerate(pivs):
                v[pc] = M[i][fc]
            basis.append(v)
        return basis


def window_cube(N):
    return [0] + [1 << i for i in range(N)]


def window_local(tp):
    return [0] + [1 << i for i in range(tp)]


def sample_mu(F, n, C, rng):
    return [[F.rand(rng) for _ in C] for _ in range(n)]


def encode(F, vals, mu, C):
    """mixed codeword from the evaluation vector vals on D."""
    n = len(vals)
    out = []
    for x in range(n):
        acc = 0
        for j, c in enumerate(C):
            acc ^= F.mul(mu[x][j], vals[x ^ c])
        out.append(acc)
    return out


def free_classes(evals, C, x):
    """free partition at x: classes of members equal on the whole window, as a list of lists."""
    t = len(evals)
    key = {}
    for i in range(t):
        key.setdefault(tuple(evals[i][x ^ c] for c in C), []).append(i)
    return list(key.values())


def free_sum(evals, C):
    """sum over x of (largest free class - 1), and sum of (t - number of free classes)."""
    n, t = len(evals[0]), len(evals)
    single = multi = 0
    for x in range(n):
        cl = free_classes(evals, C, x)
        single += max(len(c) for c in cl) - 1
        multi += t - len(cl)
    return single, multi


def best_word_sum(codewords):
    """sum over x of (largest number of codewords sharing a symbol - 1): the best word for these members."""
    n = len(codewords[0])
    tot = 0
    for x in range(n):
        cnt = {}
        for cw in codewords:
            cnt[cw[x]] = cnt.get(cw[x], 0) + 1
        tot += max(cnt.values()) - 1
    return tot


def window_rank(F, evals, I, C, x):
    """rho_x(I): rank of the differences of the members in I on the window of x."""
    I = list(I)
    if len(I) < 2:
        return 0
    rows = [[evals[i][x ^ c] ^ evals[I[0]][x ^ c] for c in C] for i in I[1:]]
    return F.rank(rows)
