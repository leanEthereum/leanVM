#!/usr/bin/env python3
"""Researcher 56. Checks of the low-level rigidity theorem (56-witt-real-field.md, Theorem 4), which holds on
every subspace domain of every field of characteristic two.

 A  The widening lemma. For a q-form omega on F_2^N (coefficients omega_A, |A| = q) and the Frobenius twists
    b^(t) = (b_i^(2^t))_i of a basis of D: if <omega, b^(t_1) ^ .. ^ b^(t_q)> = 0 for all t_1 < .. < t_q with
    t_q - t_1 <= L and 2^(q-1) (N - 1 - L) <= N - 1, then omega = 0. Tested as the injectivity of an explicit
    F_2-linear map, in fields of degree m = N (D = K), N + 1, N + 3 and 16, power and random bases; the rank
    deficiency just below the threshold is printed.
 B  n = 16, all pairs of T-sets (T = 6, 7, 8) of a 4-dimensional subspace of GF(2^m): a pair that shares
    e_1..e_g with g >= 5 has all hyperplane counts congruent modulo 4 (no pair of Walsh level 1 or 2).
 C  The thresholds of Theorem 4 at the real sizes.
 D  Theorem 4 end to end: at the least depth g at which the theorem excludes level r, the whole leading-digit
    map (class of level r) -> (sum_A gbar_A M_A(j))_j, j <= g with wt(j-1) = r-1, is injective over F_2
    (all degrees of the class together, not stratum by stratum), in the smallest fields; and its kernel
    dimension one unit of depth below the first depth at which it is injective.
usage: 56_lowlevel.py [A|B|C|D|all]"""
import importlib.util
import os
import random
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lib56", os.path.join(HERE, "56_lib.py"))
lib = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lib)
GF, wt = lib.GF, lib.wt


def det(F, M):
    """Determinant over GF(2^m) (Gaussian elimination)."""
    M = [row[:] for row in M]
    n = len(M)
    d = 1
    for c in range(n):
        p = next((r for r in range(c, n) if M[r][c]), None)
        if p is None:
            return 0
        M[c], M[p] = M[p], M[c]
        d = F.mul(d, M[c][c])
        inv = F.inv(M[c][c])
        for r in range(c + 1, n):
            if M[r][c]:
                f = F.mul(M[r][c], inv)
                M[r] = [x ^ F.mul(f, y) for x, y in zip(M[r], M[c])]
    return d


def rank_f2(rows):
    piv = {}
    rk = 0
    for v in rows:
        while v:
            b = v.bit_length() - 1
            if b in piv:
                v ^= piv[b]
            else:
                piv[b] = v
                rk += 1
                break
    return rk


def top_form_rank(F, basis, q, L):
    """F_2-rank of omega -> (<omega, b^(T)>)_T over the q-subsets T = {0 = t_1 < .. < t_q}, t_q <= L."""
    N = len(basis)
    tw = [[F.pow(b, 1 << t) for b in basis] for t in range(L + 1)]
    subsets = list(combinations(range(N), q))
    # one column per subset A; entries are the minors det[b_i^(2^t)]_{i in A, t in T}; rank over F_2 of the
    # m-bit columns stacked over all T
    cols = [0] * len(subsets)
    shift = 0
    for rest in combinations(range(1, L + 1), q - 1):
        T = (0,) + rest
        for ai, A in enumerate(subsets):
            d = det(F, [[tw[t][i] for i in A] for t in T])
            cols[ai] |= d << shift
        shift += F.m
    return rank_f2(cols), len(subsets)


def check_A(rng):
    print("== A. Widening lemma: injectivity of the top-form map when 2^(q-1) (N - 1 - L) <= N - 1 ==")
    print("   N  q  L (threshold)  field: rank / unknowns, per domain")
    bad = 0
    for N in (5, 6, 7, 8, 9):
        for q in (2, 3, 4):
            if q > N - 1:
                continue
            # least L with 2^(q-1) (N - 1 - L) <= N - 1
            Lmin = next(L for L in range(q - 1, N) if (1 << (q - 1)) * (N - 1 - L) <= N - 1)
            for L in (Lmin - 1, Lmin):
                if L < q - 1:
                    continue
                out = []
                for m in sorted({N, N + 1, N + 3, 16}):
                    if m > 16:
                        continue
                    F = GF(m)
                    for kind in ("power", "random"):
                        basis = lib.power_basis(F, N) if kind == "power" else lib.random_basis(F, N, rng)
                        rk, unk = top_form_rank(F, basis, q, L)
                        out.append(f"GF(2^{m}) {kind[0]}: {rk}/{unk}")
                        if L >= Lmin and rk != unk:
                            bad += 1
                tag = "at the threshold" if L == Lmin else "one below    "
                print(f"   {N}  {q}  {L} ({tag})  " + "; ".join(out))
    print("   violations of the lemma:", bad)
    assert bad == 0


def excluded(N, r, g):
    """True if Theorem 4 excludes Walsh level exactly r at depth g on every N-dimensional subspace domain."""
    for v in range(r):
        q = r - v
        G = g >> v
        if G < 1:
            return False
        if q == 1:
            continue
        # largest L such that every q-subset of spread <= L has value <= G: 2^(L+1) - 2^(L-q+2) + 1 <= G
        L = q - 2
        while (1 << (L + 2)) - (1 << (L - q + 3)) + 1 <= G:
            L += 1
        if L < q - 1 or (1 << (q - 1)) * (N - 1 - L) > N - 1:
            return False
    return True


def check_B(rng):
    print("== B. n = 16: pairs of T-sets sharing e_1..e_g, g >= 5, have Walsh level >= 3 ==")
    assert excluded(4, 1, 5) and excluded(4, 2, 5) and not excluded(4, 2, 4)
    total = 0
    for m in (4, 5, 6, 7, 8):
        F = GF(m)
        for trial in range(3 if m > 4 else 1):
            basis = [1, 2, 4, 8] if trial == 0 else lib.random_basis(F, 4, rng)
            pts = lib.span(F, basis)
            hm = [[bin(phi & x).count("1") & 1 for x in range(16)] for phi in range(16)]
            for T in (6, 7, 8):
                classes = {}
                for S in combinations(range(16), T):
                    r = [1] + [0] * 5
                    for x in S:
                        if pts[x]:
                            F.series_mul_lin(r, pts[x])
                    classes.setdefault(tuple(r[1:]), []).append(S)
                low = pairs = 0
                for cls in classes.values():
                    if len(cls) < 2:
                        continue
                    keys = [tuple(sum(hm[phi][x] for x in S) & 3 for phi in range(1, 16)) for S in cls]
                    for i in range(len(cls)):
                        for j in range(i + 1, len(cls)):
                            pairs += 1
                            low += keys[i] != keys[j]
                total += pairs
                assert low == 0, (m, basis, T)
    print(f"   fields GF(2^4)..GF(2^8), 13 domains, T = 6, 7, 8: {total} pairs share e_1..e_5, none of level 1 or 2")
    print("   (the decisive test is 56_acc32: about 6.5e13 pairs of level 2 at n = 32, none shares e_1..e_5)")


def check_C():
    print("== C. Theorem 4 at the real sizes: Walsh levels excluded on every subspace domain ==")
    for N, frac in ((25, 0.16), (25, 0.2), (26, 0.19), (27, 0.185), (28, 0.1575), (33, 0.2), (49, 0.2), (64, 0.2)):
        g = int(frac * (1 << N))
        ex = [r for r in range(1, N) if excluded(N, r, g)]
        top = max(ex) if ex else 0
        assert ex == list(range(1, top + 1))
        print(f"   N = {N}, g = {frac} n: levels 1..{top} excluded: a common top to depth g forces all hyperplane "
              f"counts congruent modulo 2^{top} (the formal model: modulo 2^{g.bit_length()})")


def compositions_pow2(M, parts):
    if parts == 0:
        if M == 0:
            yield ()
        return
    if M < parts:
        return
    t = 0
    while (1 << t) <= M - (parts - 1):
        for rest in compositions_pow2(M - (1 << t), parts - 1):
            yield (t,) + rest
        t += 1


def leading_rank(F, basis, r, g):
    """F_2-rank of the leading-digit map on the classes of level r, and the number of unknowns."""
    N = len(basis)
    subsets = [A for q in range(1, r + 1) for A in combinations(range(N), q)]
    js = [j for j in range(1, g + 1) if wt(j - 1) == r - 1]
    tw = {}
    cols = [0] * len(subsets)
    shift = 0
    for j in js:
        comps = {q: list(compositions_pow2(j, q)) for q in range(1, r + 1)}
        for ai, A in enumerate(subsets):
            acc = 0
            for t in comps[len(A)]:
                p = 1
                for i, ti in zip(A, t):
                    key = (i, ti)
                    if key not in tw:
                        tw[key] = F.pow(basis[i], 1 << ti)
                    p = F.mul(p, tw[key])
                acc ^= p
            cols[ai] |= acc << shift
        shift += F.m
    return rank_f2(cols), len(subsets)


def check_D(rng):
    print("== D. Theorem 4 end to end: the leading-digit map of level r at the depth where the theorem applies ==")
    for N, r in ((5, 2), (6, 2), (7, 2), (8, 2), (9, 2), (7, 3), (8, 3), (9, 3)):
        g0 = next(g for g in range(1, 1 << N) if excluded(N, r, g))
        out = []
        for m in (N, N + 1, N + 2):
            if m > 16:
                continue
            F = GF(m)
            for kind in ("power", "random"):
                basis = lib.power_basis(F, N) if kind == "power" else lib.random_basis(F, N, rng)
                rk, unk = leading_rank(F, basis, r, g0)
                assert rk == unk, (N, r, m, kind, rk, unk)
                # the first depth at which the map is injective on this domain
                g1 = g0
                while g1 > 1 and leading_rank(F, basis, r, g1 - 1)[0] == unk:
                    g1 -= 1
                out.append(f"GF(2^{m}) {kind[0]}: injective from g = {g1}")
        print(f"   N = {N}, level {r}: Theorem 4 applies from g = {g0} ({unk} unknowns); " + "; ".join(out))


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = random.Random(561)
    if which in ("D", "all"):
        check_D(rng)
    if which in ("A", "all"):
        check_A(rng)
    if which in ("B", "all"):
        check_B(rng)
    if which in ("C", "all"):
        check_C()
