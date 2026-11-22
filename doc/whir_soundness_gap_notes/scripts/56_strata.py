#!/usr/bin/env python3
"""Researcher 56. Exact stratum counts over all 2-adic digits at the real sizes (56-witt-real-field.md, Section 3).

The coefficient e_j, j = k 2^v (k odd), is the digit-v condition of the odd power sum k.
 Walsh level r (all hyperplane counts of the difference divisible by 2^(r-1)):
     e_j is active iff wt(k) + v >= r, that is wt(j - 1) >= r - 1;   C_g(r) = #{j <= g active}.
 Boolean degree d (both indicators of degree <= d):
     e_j can be active only if wt(k) + d (v + 1) >= N;                R_d(g) = #{j <= g active}.
Each active condition is one element of K: m = 64 bits on the real field.
usage: 56_strata.py"""
from math import comb, log2

M = 64


def wt(k):
    return bin(k).count("1")


def count_below(limit, nbits_min_weight):
    """#{0 <= i < limit : wt(i) >= w} for all w, as a list indexed by w (exact, digit DP on the bits of limit)."""
    nb = max(1, limit.bit_length())
    res = [0] * (nb + 2)
    ones = 0
    for b in range(nb - 1, -1, -1):
        if limit >> b & 1:
            # prefix equal to limit above bit b, bit b set to 0, lower b bits free
            for t in range(b + 1):
                res[min(ones + t, nb + 1)] += comb(b, t)
            ones += 1
    # res[w] = number with weight exactly w; turn into >= w
    for w in range(nb, -1, -1):
        res[w] += res[w + 1]
    return res


def C_table(g):
    """C_g(r) for all r: #{0 <= i < g : wt(i) >= r - 1}."""
    ge = count_below(g, 0)
    return lambda r: ge[r - 1] if 0 <= r - 1 < len(ge) else 0


def R_digits(N, d, g):
    """List over v of #{odd k <= g / 2^v : wt(k) + d (v + 1) >= N}."""
    out = []
    v = 0
    while (1 << v) <= g:
        lim = g >> v                       # odd k <= lim  <=>  k = 2 i + 1, i < ceil(lim / 2)
        need = N - d * (v + 1)             # wt(k) = wt(i) + 1 >= need
        ge = count_below((lim + 1) // 2, 0)
        w = max(0, need - 1)
        out.append(ge[w] if w < len(ge) else 0)
        v += 1
    return out


def rm_dim(d, N):
    return sum(comb(N, t) for t in range(d + 1))


def H(a):
    return -a * log2(a) - (1 - a) * log2(1 - a)


WINDOWS = [  # rate, N, lower end, Theorem S threshold (note 49), Johnson radius
    ("1/2", 25, 0.5, 0.66, 0.700840, 0.70710678),
    ("1/4", 26, 0.25, 0.44, 0.488109, 0.5),
    ("1/8", 27, 0.125, 0.31, 0.340086, 0.35355339),
    ("1/16", 28, 0.0625, 0.22, 0.237478, 0.25),
]


def main():
    print("== 1. Walsh levels: C_g(r) = #{j <= g : wt(j-1) >= r-1}, field elements needed for a non-formal pair")
    print("      whose difference has all hyperplane counts divisible by 2^(r-1) and not all by 2^r ==")
    for rate, N, rho, alo, aS, aJ in WINDOWS:
        n = 1 << N
        print(f"\n rate {rate}, N = {N}:  g = (a - rho) n")
        gs = [(a, int((a - rho) * n)) for a in (alo, aS, aJ)]
        hdr = "   c = N - r | " + " | ".join(f"a = {a:.4f} (g/n = {g / n:.4f})" for a, g in gs)
        print(hdr + " | log2 #candidates <=")
        Ct = [C_table(g) for _, g in gs]
        # the difference of two sets of size a n has weight at most W n
        W = 2 * (1 - alo) if alo > 0.5 else 2 * aJ
        worst = None
        for c in range(1, N):
            r = N - c
            cand = min((N + 2) * (4 ** c) * W + 1, n * log2(3))
            row = [Ct[i](r) for i in range(3)]
            margin = M * row[0] - cand
            if c >= 3 and (worst is None or margin / (M * row[0]) < worst[1]):
                worst = (c, margin / (M * row[0]), margin)
            if c <= 12 or c in (N - 1, N - 2) or c % 4 == 0:
                print(f"   {c:9d} | " + " | ".join(f"{x:12d} = {M * x:11d} bits" for x in row)
                      + f" | {cand:14.0f}   margin at the lower end: {margin:14.0f} bits")
        print(f"   smallest relative margin over c >= 3: c = {worst[0]}, 64 C exceeds the candidate bound by "
              f"{100 * worst[1]:.1f}% ({worst[2]:.0f} bits)")
        # the plain pigeonhole over all sets of size a n, with the best level
        for a, g in gs[:1]:
            best = min(M * C_table(g)(r) + sum(comb(N, t) * (r - t) for t in range(r)) for r in range(1, N))
            print(f"   all sets of size {a} n: log2 #sets = {H(a) * n:.0f}; min over r of [64 C_g(r) + formal bits of "
                  f"level r] = {best} = {best / n:.2f} n")

    print("\n== 2. Boolean degree d: R_d(g) by 2-adic digit (number of field elements), against dim RM(d, N) ==")
    for rate, N, rho, alo, aS, aJ in WINDOWS:
        n = 1 << N
        g = int((aS - rho) * n)
        print(f"\n rate {rate}, N = {N}, a = {aS} (Theorem S threshold), g = {g} = {g / n:.4f} n")
        print("   d | dim RM(d,N) | digit 0 | digit 1 | digit 2 | digit 3 | digit 4 | all digits | 64 * all / dim | "
              "digit 0 alone leaves dim >=")
        for d in range(1, 7):
            dig = R_digits(N, d, g)
            tot = sum(dig)
            dim = rm_dim(d, N)
            print(f"   {d} | {dim:11d} | " + " | ".join(f"{x:7d}" for x in dig[:5])
                  + f" | {tot:10d} | {M * tot / dim:14.1f} | {max(0, dim - M * dig[0]):d}")
        # first digit at which the cumulative count exceeds the number of configurations (pairs of sets)
        for d in range(2, 7):
            dig = R_digits(N, d, g)
            dim = rm_dim(d, N)
            cum = 0
            for v, x in enumerate(dig):
                cum += M * x
                if cum > 2 * dim:
                    print(f"   d = {d}: 64 * (digits 0..{v}) = {cum} > 2 dim RM = {2 * dim}: pairs are overdetermined "
                          f"from digit {v} on")
                    break

    print("\n== 3. Sanity: toy values quoted in the note ==")
    print("   N = 25, g = 0.2 n: C_g(N-2), C_g(N-3) =", C_table(int(0.2 * 2 ** 25))(23), C_table(int(0.2 * 2 ** 25))(22))
    print("   N = 25, g = 0.16 n: C_g(N-2), C_g(N-3) =", C_table(int(0.16 * 2 ** 25))(23), C_table(int(0.16 * 2 ** 25))(22))
    # brute force cross-check of the DP
    for g in (37, 100, 1000, 5000):
        for r in range(1, 12):
            assert C_table(g)(r) == sum(1 for i in range(g) if wt(i) >= r - 1)
        for d in (1, 2, 3):
            for N in (8, 10, 13):
                dig = R_digits(N, d, g)
                brute = [0] * len(dig)
                for j in range(1, g + 1):
                    v = (j & -j).bit_length() - 1
                    if wt(j >> v) + d * (v + 1) >= N:
                        brute[v] += 1
                assert dig == brute, (g, d, N, dig, brute)
    print("   digit DP agrees with brute force")


if __name__ == "__main__":
    main()
