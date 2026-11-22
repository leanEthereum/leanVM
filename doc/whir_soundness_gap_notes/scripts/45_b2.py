#!/usr/bin/env python3
"""45_b2.py: first integrals with Y1-degree b <= 2 and contact order >= 4 on all lines of a word, by linear algebra,
for 45-rate-half-second-attempt.md, Section 5.

Normal form (note 43, Section 6.2): G = p + r v + s v^2 + u (t + w v), with p, r, s, t, w in F[tau, q],
q = u^2 + tau v^2 (= Y0^2 in jet coordinates), u = Y0 + X Y1, v = Y1.  b <= 1 is s = w = 0 (p = C, r = A, t = B).
Contact >= 4 on the line of (alpha, y), i.e. G in I_alpha^2, is the 10 linear conditions at the point
P = (alpha^2, y^2) of the (tau, q)-plane (Proposition 5.1 of the note):
    p = r = s = t = w = 0,
    p_tau + y t_tau = 0,   r_tau + alpha t_tau + y w_tau = 0,   r_q + alpha t_q + y w_q = 0,   s_q + alpha w_q = 0,
    p_q + y t_q + s_tau + alpha w_tau = 0.
Weighted degree of the jet form for the weights (1, D, D): tau^i q^j in p: 2i + 2jD; in r: 2i + (2j+1)D;
in t: 2i + (2j+1)D + 1; in s: 2i + (2j+2)D; in w: 2i + (2j+2)D + 1.

With (u, v)-degree <= 5 (q-degree <= 2 in p, r, t and <= 1 in s, w) the solutions form an F[tau]-lattice of rank 13
and colength 10 n, so the successive minima satisfy  sum = 36 D + 5 + 20 n  (rank 9, sum 24 D + 3 + 14 n for b <= 1).
The script prints the minima of both lattices, checks the two conservation laws, and prints the minima of the
quotient (the first weighted degrees at which a solution with (s, w) != 0 exists that is not a b <= 1 solution).

Run: python3 45_b2.py [N] [word ...]    N = 4, 5;  word = fam | rand | zero | mono:<e> | flat     default: fam rand
"""
import sys
import random
from importlib import import_module

lib = import_module("40_lib")
mul, fpow, fsqrt = lib.mul, lib.fpow, lib.fsqrt

QMAX = {"p": 2, "r": 2, "t": 2, "s": 1, "w": 1}
OFF = {"p": (0, 0), "r": (1, 0), "t": (1, 1), "s": (2, 0), "w": (2, 1)}   # weight = 2i + (2j + a) D + c


def support(W, Dc, blocks):
    out = []
    for blk in blocks:
        a, c = OFF[blk]
        for j in range(QMAX[blk] + 1):
            base = (2 * j + a) * Dc + c
            i = 0
            while 2 * i + base <= W:
                out.append((blk, i, j))
                i += 1
    return out


def weight(mo, Dc):
    blk, i, j = mo
    a, c = OFF[blk]
    return 2 * i + (2 * j + a) * Dc + c


def rows_for(monos, pts):
    rows = []
    for (al, y) in pts:
        t0, z = mul(al, al), mul(y, y)

        def val(i, j):
            return mul(fpow(t0, i), fpow(z, j))

        def dtau(i, j):
            return mul(fpow(t0, i - 1), fpow(z, j)) if i & 1 else 0

        def dq(i, j):
            return mul(fpow(t0, i), fpow(z, j - 1)) if j & 1 else 0

        R = [bytearray(len(monos)) for _ in range(10)]
        for idx, (blk, i, j) in enumerate(monos):
            v, dt, dqq = val(i, j), dtau(i, j), dq(i, j)
            k = "prstw".index(blk)
            R[k][idx] = v                       # the five values
            if blk == "p":
                R[5][idx] ^= dt
                R[9][idx] ^= dqq
            elif blk == "t":
                R[5][idx] ^= mul(y, dt)
                R[6][idx] ^= mul(al, dt)
                R[7][idx] ^= mul(al, dqq)
                R[9][idx] ^= mul(y, dqq)
            elif blk == "r":
                R[6][idx] ^= dt
                R[7][idx] ^= dqq
            elif blk == "w":
                R[6][idx] ^= mul(y, dt)
                R[7][idx] ^= mul(y, dqq)
                R[8][idx] ^= mul(al, dqq)
                R[9][idx] ^= mul(al, dt)
            elif blk == "s":
                R[8][idx] ^= dqq
                R[9][idx] ^= dt
        rows += [bytes(r) for r in R]
    return rows


def nullities(pts, Dc, blocks, W_lo, W_hi):
    monos_hi = support(W_hi, Dc, blocks)
    rows_hi = rows_for(monos_hi, pts)
    out = {}
    for W in range(W_lo, W_hi + 1):
        cols = [i for i, mo in enumerate(monos_hi) if weight(mo, Dc) <= W]
        sub = [bytes(r[c] for c in cols) for r in rows_hi]
        out[W] = len(cols) - lib.rank(sub, len(cols))
    return out


def minima_from(nu, W_lo, W_hi, rank):
    mins = []
    for W in range(W_lo + 3, W_hi + 1):
        new = (nu[W] - nu[W - 2]) - (nu[W - 1] - nu[W - 3])
        mins += [W] * new
        if len(mins) >= rank:
            break
    return mins


def run(name, pts, Dc, n):
    W_lo, W_hi = Dc - 3, int(4.2 * n)
    nu1 = nullities(pts, Dc, "prt", W_lo, W_hi)
    nu2 = nullities(pts, Dc, "prstw", W_lo, W_hi)
    m1 = minima_from(nu1, W_lo, W_hi, 9)
    m2 = minima_from(nu2, W_lo, W_hi, 13)
    diff = {W: nu2[W] - nu1[W] for W in nu1}
    mq = minima_from(diff, W_lo, W_hi, 4)
    law1, law2 = 24 * Dc + 3 + 14 * n, 36 * Dc + 5 + 20 * n
    print(f"  {name}:")
    print(f"    b <= 1: minima {m1}, sum {sum(m1)} (law {law1}) {'OK' if sum(m1) == law1 and len(m1) == 9 else 'incomplete or mismatch'}")
    print(f"    b <= 2: minima {m2}, sum {sum(m2)} (law {law2}) {'OK' if sum(m2) == law2 and len(m2) == 13 else 'incomplete or mismatch'}")
    print(f"    quotient (genuine b = 2): minima {mq} = {[round(x / n, 3) for x in mq]} n; "
          f"sum {sum(mq)} (law {law2 - law1}); window of note 41 for b = 2 ends at 2.613 n = {2.613 * n:.1f}")
    sys.stdout.flush()


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    words = sys.argv[2:] or ["fam", "rand"]
    n = 1 << N
    Dc = n // 2 - 1
    D = lib.subspace_domain(N, seed=3)
    rng = random.Random(9)
    print(f"n = {n}, D = {Dc}, GF(2^8), subspace domain")
    for wd in words:
        if wd == "fam":
            y = [fpow(al, 3 * n // 4 - 1) for al in D]
        elif wd == "rand":
            y = [rng.randrange(256) for _ in D]
        elif wd == "zero":
            y = [0 for _ in D]
        elif wd == "flat":
            y = [fpow(al, n // 2 - 1) for al in D]
        elif wd.startswith("mono:"):
            y = [fpow(al, int(wd[5:])) for al in D]
        else:
            continue
        run(wd, list(zip(D, y)), Dc, n)


if __name__ == "__main__":
    main()
