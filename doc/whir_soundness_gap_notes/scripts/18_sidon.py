#!/usr/bin/env python3
"""Researcher 18. The Sidon tangent-line lists with lifting and anti-shortening, checked with the exact list oracle.

Construction (note 18, section 5.1). D = span(1, x, .., x^{N-1}) in GF(2^64), V = span of the first v basis vectors,
labels y = L_V(x) (a linear map D -> Lambda with kernel V, M' = n/|V| labels). Take a Sidon set A in Lambda with
|A| = L and a set P' of p' labels disjoint from A + A. The word is
    w = Z_{P'}(y) * a a'  on the fibre of y = a + a',   0 on the fibres of P',   random elsewhere,
and the L codewords are Z_{P'}(y) (a y + a^2), of degree (p' + 1)|V| in x. So k = (p' + 2)|V| and each codeword agrees
with w on (p' + L - 1)|V| points.

usage: 18_sidon.py <path to 18_sub binary> N v pprime L
prints the list size found by `18_sub ... word` at agreement T = (p' + L - 1)|V| in degree < k = (p' + 2)|V|.
       18_sidon.py max r
prints the largest size of a Sidon set in F_2^r by exhaustive search (4, 6, 7 for r = 3, 4, 5; seconds).
"""
import random
import subprocess
import sys

MOD = (1 << 64) | 0x1B


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


def max_sidon(r):
    n, best = 1 << r, [0]

    def rec(A, sums, start):
        best[0] = max(best[0], len(A))
        for c in range(start, n):
            new = {c ^ a for a in A}
            if not (new & sums):
                rec(A + [c], sums | new, c + 1)

    rec([0, 1, 2], {1, 2, 3}, 3)  # any three elements can be moved to 0, 1, 2 by an affine map
    return best[0]


def main():
    if sys.argv[1] == "max":
        print("largest Sidon set in F_2^%s: %d" % (sys.argv[2], max_sidon(int(sys.argv[2]))))
        return
    binary, N, v, pp, L = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    n = 1 << N
    V = range(1 << v)  # indices 0..2^v-1: span of the first v basis vectors

    def lam(x):  # L_V at the point with index x (the point is the integer x itself on the real shape)
        r = 1
        for u in V:
            r = mul(r, x ^ u)
        return r

    # cosets of V are indexed by x >> v; a Sidon set of coset indices, greedily, in a random order
    Mp = n >> v
    random.seed(18)
    for _ in range(2000):
        order = list(range(Mp))
        random.shuffle(order)
        A, sums = [], set()
        for c in order:
            new = {c ^ a for a in A}
            if 0 in new or new & sums or len(new) < len(A):
                continue
            A.append(c)
            sums |= new
            if len(A) == L:
                break
        free = [c for c in range(Mp) if c not in sums]
        if len(A) == L and len(free) >= pp:
            break
    else:
        print("no Sidon set of size", L, "with", pp, "labels left over among", Mp, "labels")
        return
    P = free[:pp]
    lab = {c: lam(c << v) for c in range(Mp)}
    w = [random.getrandbits(64) for _ in range(n)]
    for c in P:
        for u in V:
            w[(c << v) | u] = 0
    for i in range(L):
        for j in range(i + 1, L):
            c = A[i] ^ A[j]
            y = lab[c]
            z = 1
            for p in P:
                z = mul(z, y ^ lab[p])
            val = mul(z, mul(lab[A[i]], lab[A[j]]))
            for u in V:
                w[(c << v) | u] = val
    k = (pp + 2) << v
    T = (pp + L - 1) << v
    cmd = [binary, str(N), str(k), str(T), "real64", "0", "2", "word"] + ["%x" % t for t in w]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    res = [l for l in out.splitlines() if l.startswith("RESULT")]
    print("n=%d |V|=%d labels=%d p'=%d L=%d: k=%d T=%d (rate %.4f, agreement %.4f) ->" % (n, 1 << v, Mp, pp, L, k, T, k / n, T / n), res[0] if res else out)


main()
