#!/usr/bin/env python3
"""Researcher 18. Proposition 5.5 of note 18: orbit lists of translation-invariant words, built and checked.

For k and a random set S of T = k + |J(k)| - 1 points of D = span(1, x, .., x^{N-1}) in GF(2^64), solves for a word
w = sum_{j in J(k)} a_j X^j and a codeword c (degree < k) with w = c on S, and asks the exact oracle (`18_sub word`)
for the list of w at agreement T. Expected: the n translates of S, n codewords.

usage: 18_orbit.py <path to 18_sub binary> N k [seed]
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


def inv(a):
    r, e = 1, (1 << 64) - 2
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


def power(a, e):
    r = 1
    for _ in range(e):
        r = mul(r, a)
    return r


def main():
    binary, N, k = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 18)
    n = 1 << N
    J = [j for j in range(k, n) if all((i & j) != i for i in range(k, j))]  # binom(j, i) even: i not a submask of j
    T = k + len(J) - 1
    S = random.sample(range(n), T)
    # unknowns: a_j (j in J), then c_0..c_{k-1}; equations: sum a_j x^j + sum c_i x^i = 0 for x in S
    cols = J + list(range(k))
    A = [[power(x, e) for e in cols] for x in S]
    # kernel vector by Gaussian elimination
    rows, m = len(A), len(cols)
    piv = []
    r = 0
    for c in range(m):
        p = next((i for i in range(r, rows) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = inv(A[r][c])
        A[r] = [mul(v, iv) for v in A[r]]
        for i in range(rows):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [v ^ mul(f, u) for v, u in zip(A[i], A[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(m) if c not in piv][0]
    sol = [0] * m
    sol[free] = 1
    for i, c in enumerate(piv):
        sol[c] = A[i][free]
    w = []
    for x in range(n):
        v = 0
        for a, j in zip(sol[:len(J)], J):
            v ^= mul(a, power(x, j))
        w.append(v)
    cmd = [binary, str(N), str(k), str(T), "real64", "0", "2", "word"] + ["%x" % t for t in w]
    out = subprocess.run(cmd, capture_output=True, text=True).stdout
    res = [l for l in out.splitlines() if l.startswith("RESULT") or "cofactors" in l or "translations" in l]
    print("n=%d k=%d J=%s T=%d:" % (n, k, J, T))
    for l in res:
        print("  " + l.strip())


main()
