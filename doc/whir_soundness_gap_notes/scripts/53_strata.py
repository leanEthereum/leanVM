#!/usr/bin/env python3
"""53_strata.py: size of the code at infinity Gamma_inf(g) on subspace domains (Section 5 of
53-goppa-structure-degenerate.md).

A  Stratum (pigeonhole) lower bound, valid for EVERY N-dimensional F_2-subspace D of GF(2^m):
       dim Gamma_inf(g) >= max_d [ dim RM(d, N) - m * c_g(d) ],   c_g(d) = #{odd k <= g : wt_2(k) >= N - d},
   because a Boolean function of degree <= d is orthogonal to alpha -> alpha^k unless wt_2(k) >= N - d, and each k
   is one condition in GF(2^m). In the formal model (algebraically independent basis) the code is exactly
   RM(N - 1 - w, N), w = max wt_2(k) for k <= g. Exact numbers at N = 25..28, m = 64 and 128, for the values of g
   at the four rates.
B  With the path of the compiled 53_codes as first argument: exact dimensions at toy sizes (N = 8, 10, 12; fields
   GF(2^m), m from N + 2 to 64; D = span(1, x, .., x^(N-1)) and random subspaces), against the stratum bound and
   the formal value.
C  With it: the dimension on field domains GF(2^N) (the BCH code), N = 10..24 (and 25..28 with the flag big).

Run: python3 53_strata.py                       (A only, 1 s)
     cc -O2 -o /tmp/53_codes 53_codes.c; python3 53_strata.py /tmp/53_codes [big]     (A, B, C; 1 minute, big: 3 more)
"""
import subprocess
import sys
from math import comb, log2


def odd_by_weight(g, nbits):
    """cnt[w] = number of odd k in [1, g] with binary weight w."""
    cnt = [0] * (nbits + 2)
    if g < 1:
        return cnt
    pre = 0
    for pos in range(g.bit_length() - 1, 0, -1):
        if g >> pos & 1:
            # prefix of g above pos, 0 at pos, bit 0 = 1, bits 1..pos-1 free
            for j in range(pos):
                cnt[pre + 1 + j] += comb(pos - 1, j)
            pre += 1
    if g & 1:
        cnt[pre + 1] += 1
    return cnt


def rm_dim(d, N):
    return sum(comb(N, i) for i in range(d + 1))


def stratum(N, m, g):
    """(lower bound on dim Gamma_inf(g), the d that attains it, formal dimension)."""
    cnt = odd_by_weight(g, N + 1)
    best, bd = 0, -1
    c = 0
    for d in range(0, N):
        # c_g(d) = odd k <= g of weight >= N - d
        c = sum(cnt[w] for w in range(N - d, N + 2))
        v = rm_dim(d, N) - m * c
        if v > best:
            best, bd = v, d
    w = max((k for k in range(N + 2) if cnt[k]), default=0)
    return best, bd, rm_dim(N - 1 - w, N)


def brute_check():
    for g in (1, 2, 5, 37, 100, 845, 1023):
        ref = [0] * 16
        for k in range(1, g + 1, 2):
            ref[bin(k).count("1")] += 1
        assert odd_by_weight(g, 14) == ref, g


RATES = [("1/2", 0.5, [0.700840, 0.7065]), ("1/4", 0.25, [0.488109, 0.496622]),
         ("1/8", 0.125, [0.340086, 0.349696]), ("1/16", 0.0625, [0.237478, 0.246371])]


def part_A():
    print("# A. stratum lower bound on dim_F2 Gamma_inf(g), g = A - Delta - 1, Delta = rho n + 5, every subspace of GF(2^m)")
    print("#    rate  A/n       N   g/n      formal (RM)   m=64: bound (degree)   m=128: bound (degree)   m=256")
    for (name, rho, As) in RATES:
        for a in As:
            for N in (25, 28):
                n = 1 << N
                A = -(-int(a * 10 ** 6) * n // 10 ** 6)
                Delta = int(rho * n) + 5
                g = A - Delta - 1
                b64, d64, formal = stratum(N, 64, g)
                b128, d128, _ = stratum(N, 128, g)
                b256, d256, _ = stratum(N, 256, g)
                print(f"     {name:5s} {a:.6f}  {N}  {g / n:.4f}   {formal:6d}        {b64:8d} ({d64})          "
                      f"{b128:8d} ({d128})          {b256:8d} ({d256})")
    print("#    smallest m for which the stratum bound does not exceed the formal value (rate 1/2, a = 0.7065):")
    for N in (25, 26, 27, 28):
        n = 1 << N
        g = -(-7065 * n // 10000) - (n // 2 + 5) - 1
        formal = stratum(N, 64, g)[2]
        lo, hi = 1, 1 << 20
        while lo < hi:
            mid = (lo + hi) // 2
            if stratum(N, mid, g)[0] <= formal:
                hi = mid
            else:
                lo = mid + 1
        print(f"     N = {N}: m >= {lo}")


def profile(binary, N, m, kind, seed=0):
    out = subprocess.run([binary, "inf", str(N), str(m), kind, str(seed)], capture_output=True, text=True).stdout
    prof = []
    for line in out.splitlines():
        if line and line[0] != "#":
            k, d = line.split()
            prof.append((int(k), int(d)))
    return prof


def dim_at(prof, g):
    d = None
    for k, dd in prof:
        if k <= g:
            d = dd
    return d


def part_B(binary):
    fr = [0.175, 0.19, 0.2065, 0.238, 0.25]
    print("# B. exact dim Gamma_inf(g) at toy sizes: value / stratum bound; formal value in the header")
    for N in (8, 10, 12):
        n = 1 << N
        gs = [int(f * n) for f in fr]
        print(f"   N = {N}, n = {n}; g = {gs} (g/n = {fr}); formal: {[stratum(N, 64, g)[2] for g in gs]}")
        for kind in ("span", "rand"):
            for m in (N + 2, 16, 20, 24, 32, 40, 48, 64):
                if m < N + 2:
                    continue
                prof = profile(binary, N, m, kind, 1)
                row = []
                for g in gs:
                    row.append(f"{dim_at(prof, g)}/{stratum(N, m, g)[0]}")
                print(f"      {kind} m = {m:2d}: " + "  ".join(row))
        sys.stdout.flush()


def part_C(binary, big):
    print("# C. field domains D = GF(2^N): dim of the same code (BCH), log_n of it")
    Ns = [10, 12, 14, 16, 18, 20, 22, 24] + ([25, 28] if big else [])
    for N in Ns:
        n = 1 << N
        row = []
        for f in (0.175, 0.2008, 0.2065, 0.238, 0.25):
            g = int(f * n)
            out = subprocess.run([binary, "bch", str(N), str(g)], capture_output=True, text=True).stdout
            d = int(out.split("dim =")[1])
            row.append(f"g/n={f}: {d} (n^{log2(d) / N:.3f})")
        print(f"   N = {N}: " + "; ".join(row))
        sys.stdout.flush()


if __name__ == "__main__":
    brute_check()
    part_A()
    if len(sys.argv) > 1:
        part_B(sys.argv[1])
        part_C(sys.argv[1], len(sys.argv) > 2)
