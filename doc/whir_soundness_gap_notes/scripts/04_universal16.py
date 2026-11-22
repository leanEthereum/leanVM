"""Researcher 04. Check of Corollary 2.5 of the report (04-list-bounds-beyond-johnson.md) for n = 16.

Generic mode: D is spanned by four random elements of K = GF(2)[x]/(x^64+x^4+x^3+x+1). The script first checks that
the monomials of degree 1, 2 and 4 in the basis are F_2-linearly independent in K (4, 10 and 35 monomials), which is
the hypothesis "4-generic". Then for every T and every m = T - k in 1..7 it groups the T-subsets of D by
(e_1..e_m) and checks, for every pair S, S' in a class:
  (A) n_phi(S) = n_phi(S') mod 2^(a+1) for the 15 nonzero functionals phi, where 2^a <= m < 2^(a+1)
      (counted as the number of pairs of a class with different residue vectors);
  (B) if m >= n/8 = 2 and T != 8: |S ^ S'| = 8 and S ^ S' is an affine hyperplane; class size <= 1/(2T/n - 1)^2.
Poly mode (--poly): the same checks on D = span(1, x, x^2, x^3), which is not generic; violations are counted.
"""
import sys, random
from itertools import combinations, combinations_with_replacement
from collections import defaultdict

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

def rank(vs):
    vs = list(vs); r = 0
    while vs:
        v = vs.pop()
        if v == 0:
            continue
        r += 1
        hb = v.bit_length() - 1
        vs = [w ^ v if (w >> hb) & 1 else w for w in vs]
    return r

poly = "--poly" in sys.argv
random.seed(16)
basis = [1 << i for i in range(N)] if poly else [random.getrandbits(64) for _ in range(N)]
for j in (1, 2, 4):
    mons = []
    for c in combinations_with_replacement(range(N), j):
        v = 1
        for i in c:
            v = mul(v, basis[i])
        mons.append(v)
    print(f"degree {j}: {len(mons)} monomials, F_2-rank {rank(mons)}")
D = []
for b in range(n):
    v = 0
    for i in range(N):
        if (b >> i) & 1:
            v ^= basis[i]
    D.append(v)
par = [[bin(x & phi).count("1") & 1 for x in range(n)] for phi in range(n)]
hmask = [sum(1 << x for x in range(n) if par[phi][x]) for phi in range(n)]
hyperplanes = set()
for phi in range(1, n):
    for c in (0, 1):
        hyperplanes.add(sum(1 << x for x in range(n) if par[phi][x] == c))

print("columns: T, k, m, modulus 2^(a+1), classes of size >= 2, largest class, pairs, pairs violating the congruence"
      + ", [window] non-hyperplane differences, bound 1/(2T/n-1)^2")
for T in range(2, n):
    prof = []
    for S in combinations(range(n), T):
        e = [1] + [0] * 7
        for i in S:
            s = D[i]
            for j in range(7, 0, -1):
                if e[j - 1]:
                    e[j] ^= mul(e[j - 1], s)
        prof.append((tuple(e[1:]), sum(1 << i for i in S)))
    for m in range(1, min(7, T - 1) + 1):
        a = m.bit_length() - 1
        modulus = 2 << a
        cl = defaultdict(list)
        for p, mask in prof:
            cl[p[:m]].append(mask)
        big = [v for v in cl.values() if len(v) >= 2]
        pairs = bad = badh = 0
        for v in big:
            pairs += len(v) * (len(v) - 1) // 2
            # (A) holds for all pairs of the class iff the residue vector is constant on the class
            res = defaultdict(int)
            for A in v:
                res[tuple(bin(A & hmask[phi]).count("1") % modulus for phi in range(1, n))] += 1
            same = sum(c * (c - 1) // 2 for c in res.values())
            bad += len(v) * (len(v) - 1) // 2 - same
            if a == N - 3 and T != n // 2:
                for A, B in combinations(v, 2):
                    if (A ^ B) not in hyperplanes:
                        badh += 1
        line = f"T={T:2d} k={T-m:2d} m={m} mod {modulus:2d}: classes {len(big):5d}, largest {max((len(v) for v in big), default=1):4d}, pairs {pairs:7d}, congruence failures {bad}"
        if a == N - 3 and T != n // 2:
            line += f", non-hyperplane {badh}, bound {1 / (2 * T / n - 1) ** 2:.1f}"
        print(line)
