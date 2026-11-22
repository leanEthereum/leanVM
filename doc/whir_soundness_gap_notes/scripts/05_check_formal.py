"""Researcher 05: formal (universal) common-top classes and the quantization lemma of 05-constructions.md, section 6.

A formal class is a set of m-subsets of F_2^N whose reversed locators prod (1 + s X), s = sum_a s_a b_a with b_1..b_N
commuting indeterminates over F_2, agree modulo X^g. Such a class shares its top on every F_2-subspace of every field
of characteristic two. This script computes all formal classes for N = 4 (and N = 5 for small m) exactly, and checks
  1. Lemma 6.2: within a class, the counts |S ∩ {phi = 1}| agree modulo 2^(e+1) for every nonzero functional phi,
     where 2^e < g <= 2^(e+1);
  2. Theorem 6.3 at rate 1/2: for T > 5n/8 (g = T - n/2 > n/8) every class has at most n^2 / (4 g^2) members and any
     two members differ by exchanging two cosets of one codimension-2 subspace;
  3. the class sizes themselves (for the report's table).
Run: python3 05_check_formal.py   (about a minute)
"""
import sys
from collections import defaultdict
from itertools import combinations


def formal_key(points, N, g):
    """(e_1, .., e_{g-1}) of the set as polynomials over F_2 in b_1..b_N, each a frozenset of exponent tuples."""
    zero = (0,) * N
    e = [frozenset([zero])] + [frozenset()] * (g - 1)
    for z in points:
        bits = [a for a in range(N) if (z >> a) & 1]
        new = list(e)
        for j in range(1, g):
            acc = set(e[j])
            for a in bits:
                for t in e[j - 1]:
                    u = t[:a] + (t[a] + 1,) + t[a + 1:]
                    if u in acc:
                        acc.remove(u)
                    else:
                        acc.add(u)
            new[j] = frozenset(acc)
        e = new
    return tuple(e[1:])


def parity(v):
    return bin(v).count("1") & 1


def classes(N, m, g):
    out = defaultdict(list)
    for U in combinations(range(1 << N), m):
        out[formal_key(U, N, g)].append(U)
    return out


def check(N, m, g, rate_half_bound=False):
    n = 1 << N
    cl = classes(N, m, g)
    e = 0
    while (1 << (e + 1)) < g:
        e += 1
    mod = 1 << (e + 1)
    sizes = defaultdict(int)
    lemma_ok = True
    swap_ok = True
    for members in cl.values():
        sizes[len(members)] += 1
        if len(members) < 2:
            continue
        sigs = set()
        for U in members:
            sigs.add(tuple(sum(parity(u & phi) for u in U) % mod for phi in range(1, n)))
        if len(sigs) != 1:
            lemma_ok = False
        if rate_half_bound:
            for A, B in combinations(members, 2):
                d1 = sorted(set(A) - set(B))
                d2 = sorted(set(B) - set(A))
                ok = len(d1) == n // 4 and len(d2) == n // 4
                if ok:
                    # both are cosets of the same codimension-2 subspace
                    dir1 = {x ^ d1[0] for x in d1}
                    dir2 = {x ^ d2[0] for x in d2}
                    ok = dir1 == dir2 and all((x ^ y) in dir1 for x in dir1 for y in dir1)
                swap_ok = swap_ok and ok
    largest = max(sizes)
    msg = f"N={N} m={m} g={g}: {len(cl)} formal classes, sizes {dict(sorted(sizes.items()))}; Lemma 6.2 (mod {mod}): {lemma_ok}"
    if rate_half_bound:
        bound = n * n // (4 * g * g)
        msg += f"; Theorem 6.3: largest {largest} <= {bound}: {largest <= bound}, swaps: {swap_ok}"
    print(msg)


if __name__ == "__main__":
    # N = 4, rate 1/2 (K = 8): T = m, g = m - 8
    check(4, 10, 2)
    check(4, 11, 3, rate_half_bound=True)
    check(4, 12, 4, rate_half_bound=True)
    # N = 4, other shapes (the lemma only)
    check(4, 5, 3)
    check(4, 6, 4)
    check(4, 7, 3)
    check(4, 8, 4)
    # N = 5, small sets (low rates): m = 5, 6 with g = 3, 4, 5
    check(5, 5, 3)
    check(5, 6, 4)
    check(5, 6, 5)
