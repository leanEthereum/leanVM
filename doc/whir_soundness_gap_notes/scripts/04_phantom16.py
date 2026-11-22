"""Researcher 04. Check of Theorem 2.4 of the report (04-list-bounds-beyond-johnson.md) with one phantom root anywhere in K, n = 16.

D is spanned by four random elements of K = GF(2^64). A word of degree T + 1 has a list member with agreement set S
(|S| = T) iff w - c = Z_S(X) (X - z) for some z in K (the phantom root, in D or not). Two T-sets S, S' are in a
common list at degree bound k iff there are z, z' with Z_S (X - z) = Z_S' (X - z') in all degrees >= k, that is
  e_j(S) + z e_{j-1}(S) = e_j(S') + z' e_{j-1}(S')   for j = 1 .. m + 1,   m = T - k.
For each pair the script solves j = 1, 2 for (z, z') and tests the remaining equations, then checks the conclusion of
the theorem on every pair found: for every nonzero functional phi, n_phi(S) - n_phi(S') mod A lies in {-1, 0, 1},
where A = 4 is the modulus the theorem gives for r = 1: part 2 with a = 1 when m = 2, part 3 when m = 3.
Pairs with e_1(S) = e_1(S') are the strict common tops (z = z'), counted separately.
"""
import random, sys
from itertools import combinations

MOD = (1 << 64) | 0b11011
N, n = 4, 16

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

random.seed(41)
basis = [random.getrandbits(64) for _ in range(N)]
D = []
for b in range(n):
    v = 0
    for i in range(N):
        if (b >> i) & 1:
            v ^= basis[i]
    D.append(v)
INV = {d: inv(d) for d in D if d}
hmask = [sum(1 << x for x in range(n) if bin(x & phi).count("1") & 1) for phi in range(n)]

def profiles(T, jmax):
    out = []
    for S in combinations(range(n), T):
        e = [1] + [0] * jmax
        for i in S:
            s = D[i]
            for j in range(jmax, 0, -1):
                e[j] ^= mul(e[j - 1], s)
        out.append((e, sum(1 << i for i in S)))
    return out

for T, k in [(12, 10), (12, 9), (13, 11), (13, 10), (4, 2), (4, 1), (5, 3)]:
    m = T - k
    A = 4
    prof = profiles(T, m + 1)
    strict = phantom = bad = 0
    worst = 0
    for (e, A_mask), (f, B_mask) in combinations(prof, 2):
        d1 = e[1] ^ f[1]
        if d1 == 0:
            if all(e[j] == f[j] for j in range(2, m + 1)):
                strict += 1
            continue
        # j = 1: z' = z + d1.  j = 2: z * d1 = e2 + f2 + d1 * f1
        z = mul(e[2] ^ f[2] ^ mul(d1, f[1]), INV[d1])
        zp = z ^ d1
        if all(e[j] ^ mul(z, e[j - 1]) == f[j] ^ mul(zp, f[j - 1]) for j in range(3, m + 2)):
            phantom += 1
            for phi in range(1, n):
                d = bin(A_mask & hmask[phi]).count("1") - bin(B_mask & hmask[phi]).count("1")
                dm = ((d + A // 2) % A) - A // 2
                worst = max(worst, abs(dm)) if abs(dm) <= A // 2 else worst
                if dm not in (-1, 0, 1):
                    bad += 1
                    break
    print(f"T={T} k={k} m={m}: pairs with a common strict top {strict}, pairs joined by one phantom root {phantom}, "
          f"of which violating |d mod {A}| <= 1: {bad}")
