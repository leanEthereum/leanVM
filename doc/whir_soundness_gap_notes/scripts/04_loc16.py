"""Researcher 04. Exact locator-class list sizes for n = 16.

Locator class: words w of degree exactly T. Members of the list of w at agreement T are the
T-subsets S of D whose locator Z_S has the same coefficients as w in degrees k..T-1, that is the
same (e_1(S), ..., e_{T-k}(S)). So the largest list in the class is the largest fibre of
S -> (e_1, ..., e_{T-k}).

Domain: D = span(1, x, x^2, x^3). For N = 4 every e_j(S) is a polynomial in x of degree <= 3j <= 48 < 64,
so no reduction happens and the result is exact in K = GF(2)[x]/(x^64+x^4+x^3+x+1) (and in GF(2)(x)).
With --generic, D is instead a random 4-dimensional subspace of K (reduction used).
"""
import sys, random
from itertools import combinations
from collections import Counter
from math import comb

MOD = (1 << 64) | 0b11011

def mulK(a, b):
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

def main():
    N = 4
    n = 1 << N
    generic = "--generic" in sys.argv
    if generic:
        random.seed(4)
        basis = [random.getrandbits(64) for _ in range(N)]
    else:
        basis = [1 << i for i in range(N)]
    D = []
    for b in range(n):
        v = 0
        for i in range(N):
            if (b >> i) & 1:
                v ^= basis[i]
        D.append(v)
    assert len(set(D)) == n
    # all subsets by DFS, e[j] = e_j(S), kept in full
    res = {}
    for T in range(1, n):
        prof = []
        for S in combinations(range(n), T):
            e = [1] + [0] * T
            for idx, i in enumerate(S):
                s = D[i]
                for j in range(idx + 1, 0, -1):
                    e[j] ^= mulK(e[j - 1], s)
            prof.append(tuple(e[1:]))
        for k in range(1, T):
            m = T - k
            c = Counter(p[:m] for p in prof)
            mx = max(c.values())
            nmax = sum(1 for v in c.values() if v == mx)
            res[(k, T)] = (mx, nmax, len(c))
    print("n=16, D =", "generic subspace of K" if generic else "span(1,x,x^2,x^3)")
    print("rows k (codewords of degree < k), columns T; entry = largest fibre; J marks T^2 > n(k-1) (Johnson regime)")
    print("k\\T " + " ".join(f"{T:6d}" for T in range(2, n)))
    for k in range(1, 13):
        row = []
        for T in range(2, n):
            if T <= k:
                row.append("     .")
            else:
                mx = res[(k, T)][0]
                j = "J" if T * T > n * (k - 1) else " "
                row.append(f"{mx:5d}{j}")
        print(f"{k:3d} " + " ".join(row))
    print()
    print("Johnson bound floor(n(T-k+1)/(T^2-n(k-1))) where it applies, for comparison")
    for k in range(1, 13):
        row = []
        for T in range(2, n):
            if T <= k or T * T <= n * (k - 1):
                row.append("     .")
            else:
                row.append(f"{(n*(T-k+1))//(T*T-n*(k-1)):6d}")
        print(f"{k:3d} " + " ".join(row))

main()
