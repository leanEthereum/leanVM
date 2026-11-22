#!/usr/bin/env python3
"""50_local.py: the local structure of a polynomial of bounded Y1-degree in a contact ideal, by exact linear algebra.
For 50-residual-b-at-least-2.md, Section 2.

Local coordinates at a received point: T = X - alpha, S = Y0 - y_alpha, w = S - T Y1 (in characteristic 2: S + T Y1).
The contact ideal c_m is spanned by T^i w^l Y1^e, i + 2 l >= m.  First integrals (characteristic 2) are the elements of
F[T^2, w, Y1], and G in I^j iff only T^(2c) w^d Y1^e with c + d >= j occur.  Everything is homogeneous for the grading
by the (T, S)-degree N (T, S, w of degree 1, Y1 of degree 0), so the questions are finite-dimensional per degree N.

Part A (characteristic 2, first integrals): for b <= 5, j <= 6 and every N <= 2 j + 1
    V(b, j, N) = { H in F2[Y1][T^2, w] homogeneous of degree N, in I^j, deg_Y1 H <= b }.
  Checks: (A1) dim V equals the formula of Proposition 2.2 (the graded structure theorem);
          (A2) the support of V: for every coefficient index c the smallest N with a nonzero Y1^c-coefficient
               (the table ord(b, j, c) of Corollary 2.3);
          (A3) the number of conditions "G in I^j" on first integrals of Y1-degree <= b (Corollary 2.4).
Part B (every characteristic, arbitrary Q in c_m): for p in {2, 3, 10007}, m <= 9, b <= 5, N <= m + 1,
    U(b, m, N) = { Q homogeneous of degree N in c_m, deg_Y1 Q <= b };
  Checks: every monomial T^r S^q Y1^c in the support of U satisfies
               r + q >= m - b,   2 r + q >= m - (b - c),   r + 2 q >= m - c        (Lemma 2.1),
          and each inequality is attained (so the lemma is sharp as a statement about supports).
Part C: Lemma 2.5 (translation): for Q in c_m and a power series P through the point, Q(X, P, P' + Y1) lies in (T, Y1)^m.
        Checked for random Q over GF(10007) and GF(2) with random P.
Run: python3 50_local.py [A] [B] [C]      (about 20 s)
"""
import sys
import random
from math import comb
from itertools import product


# ------------------------------------------------------------------ linear algebra mod p on sparse dict vectors
def reduce_space(vectors, p, is_high):
    """vectors: list of dicts monomial -> coeff mod p (linearly independent or not).
    Returns a basis (list of dicts) of the subspace of span(vectors) of the elements all of whose 'high' monomials
    (is_high(mon) true) have coefficient 0."""
    # Gaussian elimination pivoting on high monomials first
    rows = [dict(v) for v in vectors if v]
    piv = {}          # high monomial -> row
    low_rows = []
    for v in rows:
        v = dict(v)
        while True:
            hm = None
            for mon in v:
                if is_high(mon):
                    if mon in piv:
                        hm = mon
                        break
            if hm is None:
                break
            pr = piv[hm]
            f = v[hm] * pow(pr[hm], p - 2, p) % p
            for mon, c in pr.items():
                nv = (v.get(mon, 0) - f * c) % p
                if nv:
                    v[mon] = nv
                else:
                    v.pop(mon, None)
        highs = [mon for mon in v if is_high(mon)]
        if highs:
            piv[min(highs)] = v
        elif v:
            low_rows.append(v)
    # make low_rows independent
    basis = []
    lp = {}
    for v in low_rows:
        v = dict(v)
        while v:
            mon = min(v)
            if mon in lp:
                pr = lp[mon]
                f = v[mon] * pow(pr[mon], p - 2, p) % p
                for mo, c in pr.items():
                    nv = (v.get(mo, 0) - f * c) % p
                    if nv:
                        v[mo] = nv
                    else:
                        v.pop(mo, None)
            else:
                lp[mon] = v
                basis.append(v)
                break
    return basis


def expand(i, l, e, p):
    """T^i w^l Y1^e with w = S - T Y1, as a dict (r, q, k) -> coeff of T^r S^q Y1^k mod p."""
    out = {}
    for t in range(l + 1):
        c = comb(l, t) * (-1) ** t % p
        if c:
            out[(i + t, l - t, e + t)] = c
    return out


# ------------------------------------------------------------------ Part A
def dim_formula(b, j, N):
    if N % 2 == 0:
        e = max(0, j - N // 2)
        return max(b - 2 * e + 1, 0) * max(N // 2 - e + 1, 0)
    e = max(0, j - (N + 1) // 2)
    return max(b - 2 * e, 0) * max((N - 1) // 2 - e + 1, 0)


def V_space(b, j, N):
    gens = []
    for c in range(0, N // 2 + 1):
        d = N - 2 * c
        if c + d < j:
            continue
        for e in range(0, b + N + 1):
            gens.append(expand(2 * c, d, e, 2))
    return reduce_space(gens, 2, lambda mon: mon[2] > b)


def part_A():
    print("A. characteristic 2, first integrals of Y1-degree <= b in I^j, graded by the (T, S)-degree N")
    bad = 0
    ordtab = {}
    for b in range(0, 6):
        for j in range(1, 7):
            for N in range(0, 2 * j + 2):
                V = V_space(b, j, N)
                if len(V) != dim_formula(b, j, N):
                    bad += 1
                    print(f"   MISMATCH b={b} j={j} N={N}: dim {len(V)} formula {dim_formula(b, j, N)}")
                supp = set()
                for v in V:
                    supp |= set(v)
                for (r, q, k) in supp:
                    key = (b, j, k)
                    if key not in ordtab or N < ordtab[key]:
                        ordtab[key] = N
                    # Lemma 2.1 with m = 2j, and the fibre statement
                    assert r + q >= max(j, 2 * j - b) and 2 * r + q >= 2 * j - (b - k) and r + 2 * q >= 2 * j - k, (b, j, N, r, q, k)
    print(f"   (A1) dim V(b, j, N) = formula for all b <= 5, j <= 6, N <= 2j + 1: {'OK' if bad == 0 else str(bad) + ' mismatches'}")
    print("   (A2) order at the received point of the coefficient of Y1^c of a first integral with contact 2j (smallest N with a")
    print("        nonzero Y1^c-part), as an offset from 2j;  Lemma N of note 40 gives 2j - b for every c:")
    for b in range(1, 6):
        for j in range(max(2, b), 7):
            offs = [ordtab[(b, j, c)] - 2 * j for c in range(b + 1)]
            if j == max(2, b) or offs != prev:
                print(f"        b = {b}, j >= {j}: ord(c) - 2j for c = 0..{b}: {offs}")
            prev = offs
    print("   (A3) number of conditions 'contact >= 2j on one line' on first integrals of Y1-degree <= b")
    print("        (sum over N < 2j of dim{all} - dim{in I^j}); b = 1: (3j^2 + j)/2, b = 2, j = 2: 10 (note 45):")
    for b in range(1, 6):
        row = []
        for j in range(1, 7):
            tot = 0
            for N in range(0, 2 * j):
                allN = (b + 1) * (N // 2 + 1) if N % 2 == 0 else b * ((N - 1) // 2 + 1)
                tot += allN - dim_formula(b, j, N)
            row.append(tot)
        print(f"        b = {b}: j = 1..6: {row}")
    assert [sum(((1 + 1) * (N // 2 + 1) if N % 2 == 0 else 1 * ((N - 1) // 2 + 1)) - dim_formula(1, j, N) for N in range(2 * j)) for j in (1, 2, 3)] == [2, 7, 15]


# ------------------------------------------------------------------ Part B
def part_B():
    print("B. every characteristic: supports of the polynomials of Y1-degree <= b in the contact ideal c_m (Lemma 2.1)")
    for p in (2, 3, 10007):
        viol = 0
        tight = [0, 0, 0]
        cases = 0
        for m in range(1, 10):
            for b in range(0, 6):
                seen = {0: False, 1: False, 2: False}
                for N in range(0, m + 2):
                    gens = []
                    for l in range(0, N + 1):
                        i = N - l
                        if i + 2 * l < m:
                            continue
                        for e in range(0, b + N + 1):
                            gens.append(expand(i, l, e, p))
                    U = reduce_space(gens, p, lambda mon: mon[2] > b)
                    supp = set()
                    for v in U:
                        supp |= set(v)
                    cases += 1
                    for (r, q, c) in supp:
                        if not (r + q >= m - b and 2 * r + q >= m - (b - c) and r + 2 * q >= m - c):
                            viol += 1
                        if r + q == m - b:
                            seen[0] = True
                        if 2 * r + q == m - (b - c):
                            seen[1] = True
                        if r + 2 * q == m - c:
                            seen[2] = True
                for t in range(3):
                    tight[t] += 1 if seen[t] else 0
        print(f"   p = {p}: {cases} spaces (m <= 9, b <= 5, N <= m + 1), violations {viol}; "
              f"each inequality attained in {tight} of 54 pairs (m, b)")


# ------------------------------------------------------------------ Part C
def part_C():
    print("C. translation: Q in c_m, P a polynomial through the point  =>  Q(X, P, P' + Y1) in (T, Y1)^m (Lemma 2.5)")
    rnd = random.Random(50)
    for p in (2, 10007):
        bad = 0
        tests = 0
        for _ in range(200):
            m = rnd.randrange(1, 8)
            # random Q in c_m: sum of a_{i l e} T^i w^l Y1^e with i + 2l >= m, small degrees
            Q = {}
            for _t in range(6):
                l = rnd.randrange(0, m // 2 + 2)
                i = max(m - 2 * l, 0) + rnd.randrange(0, 3)
                e = rnd.randrange(0, 4)
                co = rnd.randrange(1, p)
                for mon, c in expand(i, l, e, p).items():
                    Q[mon] = (Q.get(mon, 0) + co * c) % p
            # P - y = c1 T + c2 T^2 + ... (degree 6), P' its formal derivative
            cs = [0] + [rnd.randrange(p) for _ in range(6)]
            dP = [(k * cs[k]) % p for k in range(1, 7)]          # coefficients of P' in T
            # substitute S = P - y, Y1 -> P' + Y1 ; result as dict (r, k) -> coeff of T^r Y1^k, truncated at r + k < m
            def polymul(a, bb):
                out = {}
                for (r1, k1), c1 in a.items():
                    for (r2, k2), c2 in bb.items():
                        if r1 + r2 + k1 + k2 < m:
                            key = (r1 + r2, k1 + k2)
                            out[key] = (out.get(key, 0) + c1 * c2) % p
                return out
            Sser = {(k, 0): cs[k] for k in range(1, 7) if cs[k]}
            Yser = {(k, 0): dP[k] for k in range(6) if dP[k]}
            Yser[(0, 1)] = 1
            res = {}
            for (r, q, k), c in Q.items():
                if not c:
                    continue
                term = {(r, 0): 1} if r < m else {}
                for _q in range(q):
                    term = polymul(term, Sser)
                for _k in range(k):
                    term = polymul(term, Yser)
                for key, cc in term.items():
                    res[key] = (res.get(key, 0) + c * cc) % p
            tests += 1
            if any(v for v in res.values()):
                bad += 1
        print(f"   p = {p}: {tests} random (Q, P), terms of (T, Y1)-order < m that survive: {bad}")


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C"]
    for wh in which:
        {"A": part_A, "B": part_B, "C": part_C}[wh]()
