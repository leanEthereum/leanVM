"""Researcher 04. Direct check of the padded-flat lists (section 7 of 04-list-bounds-beyond-johnson.md; a special case of Lemma C of note 01).

D = span(1, x, ..., x^(N-1)) in K = GF(2)[x]/(x^64+x^4+x^3+x+1), D1 = span(1, ..., x^(N-2)), P = the first p points
of D \\ D1. For every v-dimensional subspace V of D1, c_V = Z_P * (L_V - X^(2^v)) / X has degree < k = 2^(v-1) + p
and agrees with the single word w = X^(2^v - 1) * Z_P on (V \\ 0) u P, that is on T = 2^v - 1 + p points.
The script builds every c_V, checks its degree, counts its agreement with w on D point by point, and checks that the
c_V are pairwise distinct. Rate 1/2 means p = n/2 - 2^(v-1).
"""
import sys
from itertools import combinations

MOD = (1 << 64) | 0b11011

def mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
    for i in range(r.bit_length() - 1, 63, -1):
        if (r >> i) & 1:
            r ^= MOD << (i - 64)
    return r

def pmul(f, g):
    h = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                h[i + j] ^= mul(a, b)
    return h

def peval(f, x):
    r = 0
    for a in reversed(f):
        r = mul(r, x) ^ a
    return r

def locator(pts):
    f = [1]
    for s in pts:
        f = pmul(f, [s, 1])
    return f

def subspaces(dim_ambient, v):
    """All v-dimensional subspaces of F_2^dim_ambient, as sorted tuples of ints, via reduced echelon bases."""
    seen = set()
    out = []
    def span(basis):
        s = {0}
        for b in basis:
            s |= {x ^ b for x in s}
        return frozenset(s)
    def rec(basis, start):
        if len(basis) == v:
            s = span(basis)
            if s not in seen:
                seen.add(s)
                out.append(sorted(s))
            return
        cur = span(basis)
        for c in range(start, 1 << dim_ambient):
            if c not in cur:
                rec(basis + [c], c + 1)
    rec([], 1)
    return out

def run(N, v):
    n = 1 << N
    k = n // 2
    p = k - (1 << (v - 1))
    T = (1 << v) - 1 + p
    D = list(range(n))                      # the integer b is the field element sum b_i x^i (N <= 6, no reduction)
    D1 = [b for b in D if b < n // 2]
    P = [b for b in D if b >= n // 2][:p]
    assert len(P) == p
    ZP = locator(P)
    w = [0] * ((1 << v) - 1) + ZP           # X^(2^v - 1) * Z_P
    wv = [peval(w, x) for x in D]
    Vs = subspaces(N - 1, v)
    seen = set()
    worst = n
    for V in Vs:
        LV = locator(V)                      # degree 2^v, linearized
        assert LV[0] == 0 and LV[-1] == 1
        Q = LV[1:-1]                         # (L_V - X^(2^v)) / X
        while Q and Q[-1] == 0:
            Q.pop()
        assert len(Q) - 1 <= (1 << (v - 1)) - 1
        c = pmul(Q, ZP)
        assert len(c) - 1 < k, (len(c) - 1, k)
        agr = sum(1 for x, y in zip(D, wv) if peval(c, x) == y)
        worst = min(worst, agr)
        seen.add(tuple(c))
    assert len(seen) == len(Vs)
    print(f"N={N} n={n} k={k} (rate 1/2): {len(Vs)} distinct codewords of degree < {k}, each agreeing with one word on >= {worst} points"
          f" (T = {T} = n/2 + n/2^{N - v + 1} - 1); Johnson needs T > {(n * (k - 1)) ** 0.5:.2f}")
    assert worst >= T

for (N, v) in [(4, 2), (5, 3), (5, 2), (6, 4), (6, 3)]:
    run(N, v)
