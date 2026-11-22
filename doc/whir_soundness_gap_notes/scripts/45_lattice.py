#!/usr/bin/env python3
"""45_lattice.py: the F[tau]-lattice M_5 of quintic potentials E (mod squares) whose total derivative dE has
contact order >= 4 on all lines of a word, for 45-rate-half-second-attempt.md.

A. Successive minima W_1 <= ... <= W_9 of M_5 for the weighted degree of dE, read from the nullities
   nu(W) = dim {E in M_5 : wdeg(dE) <= W}:  #{i : W_i <= W} = nu(W) - nu(W - 2).
   Conservation law (Theorem 2 of the note):  sum_i W_i = 24 D + 3 + 14 n.
B. The square-root normal form (Proposition 1): E = Y A^2 + X C^2 + X Y B^2 (mod squares) with A, B, C conics in Y,
   and contact 4 at (alpha, y) iff  B(p) = 0,  A + sqrt(alpha) B in m_p^2,  C + sqrt(y) B in m_p^2.
   Checked on every basis vector of the solution space at the smallest W, and conversely by a rank comparison.

Run: python3 45_lattice.py [N] [word]     N = 4, 5 (default 5); word = fam | rand | mono:<e> | all (default all)
Field GF(2^8), subspace domain of 40_lib (seed 3), code degree D = n/2 - 1 as in note 40.
"""
import sys
import random
from importlib import import_module

lib = import_module("40_lib")
mul, inv, fpow, fsqrt = lib.mul, lib.inv, lib.fpow, lib.fsqrt

KMAX = 5


def support(W, Dc):
    return [(i, k) for (i, k) in lib.support_b1(W, Dc) if k <= KMAX]


def rows_for(monos, pts):
    conds = lib.contact_conditions(2)
    return [lib.taylor_row(monos, al, be, r, q) for (al, be) in pts for (r, q) in conds]


def nullity_table(pts, Dc, W_lo, W_hi):
    monos_hi = support(W_hi, Dc)
    rows_hi = rows_for(monos_hi, pts)
    idx = {mo: i for i, mo in enumerate(monos_hi)}
    out = {}
    for W in range(W_lo, W_hi + 1):
        cols = [idx[mo] for mo in support(W, Dc)]
        sub = [bytes(r[c] for c in cols) for r in rows_hi]
        out[W] = len(cols) - lib.rank(sub, len(cols))
    return out


def minima(pts, Dc, n):
    W_lo, W_hi = 2 * Dc, 5 * n
    nu = nullity_table(pts, Dc, W_lo - 2, W_hi)
    mins = []
    for W in range(W_lo, W_hi + 1):
        cnt = nu[W] - nu[W - 2]
        prev = nu[W - 1] - nu[W - 3] if W - 3 in nu else 0
        # number of minima equal to W: those with W_i <= W minus those with W_i <= W - 1
        new = cnt - prev
        mins += [W] * new
        if len(mins) >= 9:
            break
    return mins


def split_sqrt(monos, vec):
    """E = sum e_ik X^i Y^k (not both even) -> coefficient dicts of the conics A, B, C with
    E = Y A^2 + X C^2 + X Y B^2: A^2 collects (i even, k odd), C^2 (i odd, k even), B^2 (i odd, k odd)."""
    A, B, C = {}, {}, {}
    for (i, k), e in zip(monos, vec):
        if not e:
            continue
        s = fsqrt(e)
        if i % 2 == 0 and k % 2 == 1:
            A[(i // 2, (k - 1) // 2)] = s
        elif i % 2 == 1 and k % 2 == 0:
            C[((i - 1) // 2, k // 2)] = s
        else:
            B[((i - 1) // 2, (k - 1) // 2)] = s
    return A, B, C


def taylor(P, al, be, r, q):
    """coefficient of T^r S^q of P(al + T, be + S), P a dict (i, k) -> coefficient."""
    t = 0
    for (i, k), c in P.items():
        if i >= r and k >= q and lib.binom2(i, r) and lib.binom2(k, q):
            t ^= mul(c, mul(fpow(al, i - r), fpow(be, k - q)))
    return t


def tangency_ok(A, B, C, al, be):
    xi, ze = fsqrt(al), fsqrt(be)
    if taylor(B, al, be, 0, 0):
        return False
    for (r, q) in ((0, 0), (1, 0), (0, 1)):
        if taylor(A, al, be, r, q) ^ mul(xi, taylor(B, al, be, r, q)):
            return False
        if taylor(C, al, be, r, q) ^ mul(ze, taylor(B, al, be, r, q)):
            return False
    return True


def tangency_rows(monos, pts):
    """the 7 conditions of Proposition 1 as linear forms in the square roots of the coefficients of E.
    Unknown vector: s_ik = sqrt(e_ik), indexed like monos."""
    rows = []
    for (al, be) in pts:
        xi, ze = fsqrt(al), fsqrt(be)

        def row(kind, r, q, scale=1):
            out = bytearray(len(monos))
            for idx, (i, k) in enumerate(monos):
                if kind == "A" and i % 2 == 0 and k % 2 == 1:
                    ii, kk = i // 2, (k - 1) // 2
                elif kind == "C" and i % 2 == 1 and k % 2 == 0:
                    ii, kk = (i - 1) // 2, k // 2
                elif kind == "B" and i % 2 == 1 and k % 2 == 1:
                    ii, kk = (i - 1) // 2, (k - 1) // 2
                else:
                    continue
                if ii >= r and kk >= q and lib.binom2(ii, r) and lib.binom2(kk, q):
                    out[idx] = mul(scale, mul(fpow(al, ii - r), fpow(be, kk - q)))
            return out

        rows.append(bytes(row("B", 0, 0)))
        for (r, q) in ((0, 0), (1, 0), (0, 1)):
            a, b = row("A", r, q), row("B", r, q, xi)
            rows.append(bytes(x ^ y for x, y in zip(a, b)))
            c, b = row("C", r, q), row("B", r, q, ze)
            rows.append(bytes(x ^ y for x, y in zip(c, b)))
    return rows


def run_word(name, D, y, Dc, n):
    pts = list(zip(D, y))
    mins = minima(pts, Dc, n)
    tot = sum(mins)
    law = 24 * Dc + 3 + 14 * n
    print(f"  {name:10s}: minima {mins}  sum = {tot}  (24 D + 3 + 14 n = {law})  {'OK' if tot == law else 'MISMATCH'}"
          f"   W_1/n = {mins[0] / n:.4f}, mean = {tot / 9 / n:.4f}")
    # part B on the solution space at W_1 and at W_1 + 6
    for W in (mins[0], mins[0] + 6):
        monos = support(W, Dc)
        rows = rows_for(monos, pts)
        basis = lib.nullspace(rows, len(monos))
        ok = all(tangency_ok(*split_sqrt(monos, v), al, be) for v in basis for (al, be) in pts)
        # converse: the tangency conditions, linear in the square roots, have the same nullity
        nul2 = len(monos) - lib.rank(tangency_rows(monos, pts), len(monos))
        print(f"      W = {W}: nullity {len(basis)}; tangency criterion holds on all basis vectors: {ok}; "
              f"nullity of the tangency system: {nul2}")
    return mins


def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    which = sys.argv[2] if len(sys.argv) > 2 else "all"
    n = 1 << N
    Dc = n // 2 - 1
    D = lib.subspace_domain(N, seed=3)
    rng = random.Random(5)
    print(f"n = {n}, D = {Dc}, GF(2^8), subspace domain; lattice M_5 of rank 9, colength 7 n = {7 * n}")
    words = []
    if which in ("all", "fam"):
        words.append((f"X^{3 * n // 4 - 1}", [fpow(al, 3 * n // 4 - 1) for al in D]))
    if which in ("all", "rand"):
        for s in range(2):
            words.append((f"random{s}", [rng.randrange(256) for _ in D]))
    if which.startswith("mono:"):
        e = int(which[5:])
        words.append((f"X^{e}", [fpow(al, e) for al in D]))
    if which == "all":
        words.append(("zero", [0 for _ in D]))
        # a random evaluation set (not a subspace), random word
        pts_al = rng.sample(range(256), n)
        words.append(("rand-set", None))
    for name, y in words:
        if name == "rand-set":
            y = [rng.randrange(256) for _ in pts_al]
            run_word(name, pts_al, y, Dc, n)
        else:
            run_word(name, D, y, Dc, n)
        sys.stdout.flush()


if __name__ == "__main__":
    main()
