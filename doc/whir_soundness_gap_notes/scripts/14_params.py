#!/usr/bin/env python3
"""Note 14: the numbers of the theorem card. Standard library only, exact integer and rational arithmetic.

  T1  the interleaving reduction (Theorem I, the tree bound N; Proposition R2', the projection bound) at the
      thresholds of interest, for single-lane K-valued list bounds L = 2^10, 2^40, 2^70, 2^100;
  T2  the same at the list sizes note 13 predicts on the real domain (its final table);
  T3  points per level as a function of the interleaved list bound (Theorem D', point message);
  T4  the error budget of one configuration.

Conventions: level 0 of the mu = 30 ladder (kappa = 24, ell = 6, n = 2^(24 + R)), d = 2^kappa - 1 + ell,
A^(0,0) = ceil(tau n) is where the list bound is assumed, A_0 = A^(0,0) + ell is what the queries see.
"""
from fractions import Fraction
from functools import lru_cache
from math import ceil, comb, log2

Q = 1 << 128  # |E|
KSIZE = 1 << 64  # |K|
SEC = 125
G_QUERY, G_FOLD, G_POINT, G_BATCH = 17, 7, 15, 7
K0 = (1 << 9) * Q  # fold round: (K0 - 1)/q^2 + tau < 2^-118
TAU = Fraction(1, 1 << 119)
MCLS = 2 * Q  # M = max(2q, C(n, 2)), and C(n, 2) < 2q for n <= 2^64


def tree_bound(L, n, d, A):
    """N_{L,g}(n - d) of Theorem I: N(P) = 1 if P < 2g, else N(P - g) + (L - 1) N(P // 2)."""
    g = A - d
    assert g >= 1

    # P - g steps are too many to recurse on at real sizes; group them: N is a step function of floor(P / g) only
    # through the two recursions, so memoise on P and take the P - g chain iteratively.
    @lru_cache(maxsize=None)
    def N(P):
        if P < 2 * g:
            return 1
        # unroll the chain P, P - g, P - 2g, ... down to below 2g
        total, cur = 1, P
        steps = []
        while cur >= 2 * g:
            steps.append(cur // 2)
            cur -= g
        for half in steps:
            total += (L - 1) * N(half)
        return total

    return N(n - d)


def closed_form(L, n, d, A):
    """sum_{k <= min(b, r)} C(b, k) (L - 1)^k, b = floor((n - A)/(A - d)), r = floor(log2((n - d)/(A - d)))."""
    g = A - d
    b = (n - A) // g
    r = ((n - d) // g).bit_length() - 1
    return b, r, sum(comb(b, k) * (L - 1) ** k for k in range(min(b, r) + 1))


def projection_bound(L, lanes=1):
    """Proposition R2' (note 13, Proposition 3.4, sharpened): if every `lanes`-lane K-valued word has at most L
    members and L <= |K|^lanes / 4, every word over any K-vector space has at most L / (1 - L/|K|^lanes)."""
    size = KSIZE**lanes
    if 4 * L > size:
        return None
    return int(Fraction(L) / (1 - Fraction(L, size)))


def eps(kappa, ell):
    return Fraction((1 << kappa) - 1 + ell + (1 << ell) - 1, Q)  # (d + 2^ell - 1)/q


def point_error(L, kappa, ell, s):
    nest = sum(TAU ** (-j) for j in range(ell))
    exc = Fraction(L**3 * Q**6, K0 * (K0 - 1) * (K0 - MCLS))
    return (comb(L, 2) + exc * nest) * eps(kappa, ell) ** s


def points_needed(L, kappa, ell):
    target = Fraction(1, 1 << (SEC - G_POINT))
    s = 1
    while point_error(L, kappa, ell, s) > target:
        s += 1
    return s


def queries_needed(n, A_top, s):
    target = Fraction(1, 1 << (SEC - G_QUERY))
    t = 1
    while Fraction(A_top - 1, n) ** t + Fraction(s + t, Q) > target:
        t += 1
    return t


def lg(x):
    if not x:
        return float("-inf")
    x = Fraction(x)
    return log2(x.numerator) - log2(x.denominator)


def level0(R, tau):
    kappa, ell = 24, 6
    n = 1 << (kappa + R)
    d = (1 << kappa) - 1 + ell
    A = ceil(Fraction(tau) * n)
    return kappa, ell, n, d, A


def best_interleaved(L, n, d, A):
    """The best bound for all lane counts and extensions from a single-lane K-valued bound L alone."""
    tree = tree_bound(L, n, d, A)
    proj = projection_bound(L)
    if proj is not None and proj < tree:
        return proj, "R2'"
    return tree, "tree"


def row(R, tau, tau_name, bK):
    kappa, ell, n, d, A = level0(R, tau)
    L = int(2**bK) if not isinstance(bK, int) else 1 << bK
    b, r, cf = closed_form(L, n, d, A)
    tree = tree_bound(L, n, d, A)
    assert tree <= cf
    proj = projection_bound(L)
    best, which = best_interleaved(L, n, d, A)
    s = points_needed(best, kappa, ell)
    t = queries_needed(n, A + ell, s)
    phi = (n - d) / (A - d)
    proj_s = f"{lg(proj):.2f}" if proj is not None else "n/a"
    return f"| 1/{1 << R} | {tau_name} | {phi:.3f} | {b} | {r} | {bK:g} | {lg(tree):.2f} | {lg(cf):.2f} | {proj_s} | {lg(best):.2f} ({which}) | {s} | {t} |"


def main():
    print("T1. Interleaving reduction at level 0 (mu = 30), single-lane K-valued bound 2^b assumed at A = ceil(tau n), degree d.")
    print("    phi = (n - d)/(A - d); b_br, r as in the closed form; log2 of: the tree bound N, its closed form, the projection bound;")
    print("    then the best of the two, the points s_0 it needs and the level-0 queries t_0.")
    print("| rate | tau | phi | b_br | r | b | tree N | closed form | projection | best | s_0 | t_0 |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    grid = [
        (1, [("0.66", Fraction(66, 100)), ("0.64", Fraction(64, 100)), ("5/8", Fraction(5, 8)), ("9/16", Fraction(9, 16))]),
        (2, [("7/16", Fraction(7, 16)), ("3/8", Fraction(3, 8)), ("5/16", Fraction(5, 16))]),
        (3, [("5/16", Fraction(5, 16)), ("1/4", Fraction(1, 4)), ("3/16", Fraction(3, 16))]),
        (4, [("3/16", Fraction(3, 16)), ("1/8", Fraction(1, 8)), ("3/32", Fraction(3, 32))]),
    ]
    for R, taus in grid:
        for name, tau in taus:
            for bK in (10, 40, 70, 100):
                print(row(R, tau, name, bK))
    print()
    print("T2. The same at note 13's predicted single-lane K-valued lists on the real domain (its final table).")
    print("| rate | tau | phi | b_br | r | b | tree N | closed form | projection | best | s_0 | t_0 |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    predicted = [
        (1, "0.64", Fraction(64, 100), 10),
        (1, "0.632", Fraction(632, 1000), 10),
        (1, "5/8", Fraction(5, 8), 30.8),
        (1, "9/16 + 2^-10", Fraction(9, 16) + Fraction(1, 1024), 38.7),
        (1, "9/16", Fraction(9, 16), 102.7),
        (2, "3/8 + 2^-10", Fraction(3, 8) + Fraction(1, 1024), 27),
        (2, "3/8", Fraction(3, 8), 34.5),
        (3, "17/64", Fraction(17, 64), 5),
        (3, "1/4", Fraction(1, 4), 53.4),
        (4, "0.153", Fraction(153, 1000), 6),
        (4, "1/8 + 2^-10", Fraction(1, 8) + Fraction(1, 1024), 15.6),
        (4, "1/8", Fraction(1, 8), 79.6),
    ]
    for R, name, tau, bK in predicted:
        print(row(R, tau, name, bK))
    print()
    print("    Two-lane route for the two cells above 2^62 (Proposition 3.5 of note 13, then R2' with two K-lanes):")
    for R, name, tau, bK, b2 in [(1, "9/16", Fraction(9, 16), 102.7, 30.8), (4, "1/8", Fraction(1, 8), 79.6, 6)]:
        kappa, ell, n, d, A = level0(R, tau)
        L, L2 = int(2**bK), int(2**b2)
        two = L * (1 + L2)
        allb = projection_bound(two, lanes=2)
        if allb is None:
            print(f"    rate 1/{1 << R}, tau = {name}: Lambda_K(A) = 2^{bK}, Lambda_K(2A - d) = 2^{b2} (predicted): two K-lanes <= 2^{lg(two):.2f}, above the cap 2^126 of the two-lane projection: no bound for all lanes by this route")
            continue
        s = points_needed(allb, kappa, ell)
        print(f"    rate 1/{1 << R}, tau = {name}: Lambda_K(A) = 2^{bK}, Lambda_K(2A - d) = 2^{b2} (predicted): two K-lanes <= 2^{lg(two):.2f}, all lanes <= 2^{lg(allb):.2f}, s_0 = {s}")
    print()
    print("T3. Points per level against the interleaved list bound 2^b (deployed grinds, K0 = 2^9 q, tau = 2^-119).")
    print("| kappa | ell | log2(1/eps) | bits needed at L = 1 | s for b = 7, 10, 40, 70, 100, 130, 340 |")
    print("| --- | --- | --- | --- | --- |")
    for kappa, ell in [(24, 6), (20, 4), (16, 4), (12, 4), (8, 4), (4, 4), (2, 4), (20, 1)]:
        need = lg(point_error(1, kappa, ell, 0) * (1 << (SEC - G_POINT)))
        ss = ", ".join(str(points_needed(1 << b, kappa, ell)) for b in (7, 10, 40, 70, 100, 130, 340))
        print(f"| {kappa} | {ell} | {-lg(eps(kappa, ell)):.2f} | {need:.1f} | {ss} |")
    print()
    print("T4. Budget of one configuration: mu = 30, rate 1/2, single-lane K-valued bound 2^10 at 0.64 n (note 13's prediction).")
    kappa, ell, n, d, A = level0(1, Fraction(64, 100))
    best, which = best_interleaved(1 << 10, n, d, A)
    s = points_needed(best, kappa, ell)
    t = queries_needed(n, A + ell, s)
    print(f"    interleaved bound 2^{lg(best):.2f} ({which}); s_0 = {s}; t_0 = {t}")
    print(f"    points of level 0: log2 error {lg(point_error(best, kappa, ell, s)):.2f}, after the {G_POINT}-bit grind {lg(point_error(best, kappa, ell, s)) - G_POINT:.2f}")
    print(f"    ring switch and batching (J_0 = 512): log2 {(log2(513) - 128):.2f}, after the {G_BATCH}-bit grind {(log2(513) - 128 - G_BATCH):.2f}")
    fold = Fraction(K0 - 1, Q * Q) + TAU
    print(f"    fold round: log2 {lg(fold):.4f}, after the {G_FOLD}-bit grind {lg(fold) - G_FOLD:.4f}; last round of a level {lg(Fraction(K0 - 1, Q * Q)) - G_FOLD:.2f}")
    qe = Fraction(A + ell - 1, n) ** t + Fraction(s + t, Q)
    print(f"    queries of level 0: log2 {lg(qe):.2f}, after the {G_QUERY}-bit grind {lg(qe) - G_QUERY:.2f}")
    print(f"    tail round: log2 {1 - 128}")
    # selftests
    assert tree_bound(5, 100, 50, 80) == 1  # unique decoding: n - A < A - d
    assert tree_bound(7, 16, 11, 13) == 7 and tree_bound(7, 8, 1, 3) == 13  # the cases of 14_interleave.c
    for L in (2, 3, 10):
        for n, d, A in [(64, 31, 40), (64, 15, 20), (64, 7, 9), (128, 9, 20)]:
            assert tree_bound(L, n, d, A) <= closed_form(L, n, d, A)[2]
    print("selftests passed")


if __name__ == "__main__":
    main()
