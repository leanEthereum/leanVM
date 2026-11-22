"""Researcher 04. The binary code B_m of Proposition 3.1 of the report (04-list-bounds-beyond-johnson.md).

B_m = { v in F_2^D : sum_x v_x x^j = 0 in K for 0 <= j <= m }. The sum of the indicators of two members of a
common-top class with T - k = m lies in B_m. Lower bound (Proposition 3.1 (ii)):
    dim B_m >= max_{w0} [ sum_{w > w0} C(N, w) - e * #{odd j <= m : wt(j) > w0} ],      e = [K : F_2].
Part 1 validates the bound against the exact dimension (rank over F_2) on analogues with a small field:
       K = GF(2^e), D = span(1, x, .., x^(N-1)).
Part 2 evaluates the bound for leanVM's size, N = 25, e = 64.
"""
from math import comb

def gf_tables(e, modulus):
    exp = [0] * (2 * (1 << e)); log = [0] * (1 << e)
    x = 1
    for i in range((1 << e) - 1):
        exp[i] = x; log[x] = i
        x <<= 1
        if x >> e:
            x ^= modulus
    for i in range((1 << e) - 1, 2 * (1 << e)):
        exp[i] = exp[i - ((1 << e) - 1)]
    return exp, log

def rank(vs):
    piv = {}
    r = 0
    for v in vs:
        while v:
            hb = v.bit_length() - 1
            if hb in piv:
                v ^= piv[hb]
            else:
                piv[hb] = v; r += 1
                break
    return r

def count_odd_heavy(m, w0):
    return sum(1 for j in range(1, m + 1, 2) if bin(j).count("1") > w0)

def count_odd_heavy_fast(m, w0, bits):
    # number of odd j <= m with popcount > w0, by a digit recursion (m < 2^bits)
    from functools import lru_cache
    @lru_cache(None)
    def rec(pos, ones, tight):
        if pos < 0:
            return 1 if ones > w0 else 0
        tot = 0
        top = (m >> pos) & 1 if tight else 1
        for b in range(top + 1):
            if pos == 0 and b == 0:
                continue          # odd
            tot += rec(pos - 1, ones + b, tight and b == top)
        return tot
    return rec(bits - 1, 0, True)

def bound(N, e, m):
    best = (0, None)
    for w0 in range(N + 1):
        val = sum(comb(N, w) for w in range(w0 + 1, N + 1)) - e * count_odd_heavy_fast(m, w0, max(m.bit_length(), 1))
        if val > best[0]:
            best = (val, w0)
    return best

print("Part 1: exact dim B_m against the bound, K = GF(2^e), D = span(1, .., x^(N-1))")
for e, modulus, N in [(12, (1 << 12) | 0b1010011, 10), (10, (1 << 10) | 0b1001, 10), (16, (1 << 16) | 0b101101, 9)]:
    exp, log = gf_tables(e, modulus)
    n = 1 << N
    for m in [n // 16 - 1, n // 16, n // 8 - 1, n // 8, 3 * n // 16, n // 4 - 1]:
        cols = []
        for x in range(n):                      # the integer x < 2^N is the field element sum x_i X^i (N <= e)
            v = 1                               # j = 0
            for j in range(1, m + 1, 2):
                y = 0 if x == 0 else exp[(log[x] * j) % ((1 << e) - 1)]
                v = (v << e) | y
            cols.append(v)
        dimB = n - rank(cols)
        b, w0 = bound(N, e, m)
        assert count_odd_heavy(m, 3) == count_odd_heavy_fast(m, 3, m.bit_length())
        assert dimB >= b
        rm = None
        v0 = (m + 1).bit_length()               # 2^(v0-1) <= m+1 < 2^v0
        dim_rm = sum(comb(N, i) for i in range(0, N - v0 + 1))
        print(f"  e={e:2d} N={N} m={m:4d} (m/n={m/n:.4f}): dim B_m = {dimB:4d}, bound {b:4d} (w0={w0}), "
              f"dim RM(N-v0,N) = {dim_rm} (the value on a generic domain)")

print("Part 2: N = 25, e = 64 (leanVM level 0 at rate 1/2)")
N, e = 25, 64
n = 1 << N
for label, m in [("n/8 - 1", n // 8 - 1), ("n/8", n // 8), ("0.15 n", int(0.15 * n)), ("3n/16", 3 * n // 16), ("0.2 n", n // 5), ("n/4 - 1", n // 4 - 1)]:
    b, w0 = bound(N, e, m)
    v0 = (m + 1).bit_length()
    dim_rm = sum(comb(N, i) for i in range(0, N - v0 + 1))
    print(f"  m = {label:8s}: dim B_m >= {b} (w0 = {w0}); on a generic domain dim = dim RM({N - v0},{N}) = {dim_rm}")
