"""Check the flats lemma of 00-lead-notes.md on a small field.

GF(2^m), D = span(1, x, ..., x^{N-1}), rate 1/4 (k = n/4). The word w(x) = x^(n/2 - 1) should agree with a
polynomial of degree < k on V minus 0 for every hyperplane V of D, with distinct polynomials for distinct V.
"""
import itertools, sys

M_BITS, MOD = 8, 0x11B  # GF(2^8)
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        a <<= 1
        if a >> M_BITS: a ^= MOD
        b >>= 1
    return r
def power(a, e):
    r = 1
    while e:
        if e & 1: r = mul(r, a)
        a = mul(a, a); e >>= 1
    return r
def inv(a): return power(a, (1 << M_BITS) - 2)

def poly_mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] ^= mul(a, b)
    return r
def poly_eval(p, x):
    r = 0
    for c in reversed(p): r = mul(r, x) ^ c
    return r
def locator(S):
    p = [1]
    for s in S: p = poly_mul(p, [s, 1])
    return p

N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
n, k = 1 << N, 1 << (N - 2)
D = list(range(n))  # bit patterns below 2^N are the span of 1, x, ..., x^{N-1}
polys = set()
for mask in range(1, n):  # hyperplane = kernel of the linear form v -> parity(v & mask)
    V = [v for v in D if bin(v & mask).count("1") % 2 == 0]
    L = locator(V)
    assert all(c == 0 for i, c in enumerate(L) if i & (i - 1) or i == 0), "locator is not linearized"
    Q = L[1 : n // 2]  # (L_V - X^(n/2)) / X
    while Q and Q[-1] == 0: Q.pop()
    assert len(Q) - 1 < k, "not a genuine codeword"
    agree = sum(1 for v in D if v and poly_eval(Q, v) == power(v, n // 2 - 1))
    assert agree >= n // 2 - 1
    polys.add(tuple(Q))
johnson = n * k  # A^2 > n*(k-1) is the Johnson condition for degree < k
print(f"N={N} n={n} k={k}: {len(polys)} distinct codewords of degree < k at agreement >= {n//2 - 1}; "
      f"(n/2-1)^2 = {(n//2-1)**2} vs n(k-1) = {n*(k-1)}")
