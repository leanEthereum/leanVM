#!/usr/bin/env python3
"""Exact first moments for a uniformly random linear code [n, k] over F_q (uniform generator matrix).
Two members: E[number of (zero set of size z, nonzero codeword up to scalar)] = binom(n, z) (q^k - 1)/(q - 1) q^-z.
Three members: E[number of lists {0, d1, d2} up to a common scalar whose balanced agreement is >= a], from the exact
law of the leaf types (none, 01, 02, 12, 012) for independent d1, d2 (dependent pairs are added: only type 012 occurs).
Prints the largest z, and the largest a, with expectation >= 1."""
from fractions import Fraction as Fr
from math import comb

def zeros_threshold(n, k, q):
    best = None
    for z in range(k - 1, n + 1):
        e = Fr(comb(n, z) * (q ** k - 1), (q - 1) * q ** z)
        if e >= 1:
            best = (z, float(e))
    return best

def balanced3(n0, n01, n02, n12, n012):
    c = sorted([n01 + n02 + n012, n01 + n12 + n012, n02 + n12 + n012])
    for _ in range(n0):
        c[0] += 1
        c.sort()
    return c[0]

def three_threshold(n, k, q):
    # exact integers: leaf-type probabilities times q^2 are 1 (type 012), q - 1 (each pair type), pn (no agreement)
    pn = q * q - 3 * (q - 1) - 1
    tail = [0] * (n + 2)
    for n012 in range(0, n + 1):
        for npair in range(0, n - n012 + 1):
            n0 = n - n012 - npair
            base = comb(n, n012) * comb(n - n012, npair) * (q - 1) ** npair * pn ** n0
            for n01 in range(npair + 1):
                c1 = comb(npair, n01)
                for n02 in range(npair - n01 + 1):
                    tail[balanced3(n0, n01, n02, npair - n01 - n02, n012)] += base * c1 * comb(npair - n01, n02)
    dep = [0] * (n + 2)
    for t in range(n + 1):  # dependent pairs d2 = c d1: t leaves of type 012 (probability 1/q each), the rest free
        dep[t + (n - t) // 3] += comb(n, t) * (q - 1) ** (n - t)
    nind, ndep = (q ** k - 1) * (q ** k - q), (q ** k - 1) * (q - 2)   # both over (q - 1)
    acc_i, acc_d = 0, 0
    for a in range(n, -1, -1):
        acc_i += tail[a]; acc_d += dep[a]
        num = nind * acc_i + ndep * acc_d * q ** n      # E = num / ((q - 1) q^(2n))
        if num >= (q - 1) * q ** (2 * n):
            return (a, float(Fr(num, (q - 1) * q ** (2 * n))) if num < (q - 1) * q ** (2 * n) * 10 ** 300 else float("inf"))
    return None

def main():
    print("field  (k, n)   two members: largest zero set with E >= 1 (k-1 is MDS)   three members: largest balanced agreement with E >= 1 (gS value)")
    for qb in (8, 16, 64):
        q = 2 ** qb
        for k, n in ((8, 16), (16, 32), (32, 64), (8, 32), (16, 64), (64, 128)):
            z = zeros_threshold(n, k, q)
            t = three_threshold(n, k, q) if n <= 64 else None
            gs = (n + 2 * k - 1) // 3
            print(f"2^{qb:<3d} ({k:3d},{n:3d})   z = {z[0]} (k-1 = {k-1}, excess {z[0]-k+1} = {(z[0]-k+1)/n:.3f} n, E = {z[1]:.2g})" + (f"   a = {t[0]} (gS {gs}, E = {t[1]:.2g})" if t else ""))

main()
