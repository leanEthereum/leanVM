#!/usr/bin/env python3
"""Referee arithmetic for note 20: point counts and per-message errors of Protocol D and of the ladder D_S.

Written from scratch, exact integer and rational arithmetic (fractions), standard library only, under a second.
It does not import 14_params.py, 15_schedules.py or 16_params.py; the last section compares with the numbers
those notes print.

Tables:
  P1  points per level, one batch (Theorem D' of note 14), mu = 30, list budgets 2^40 and 2^100
  P2  ladder schedules (Theorem D_S of note 15 with note 14's constant), same budgets
  P3  per-message errors of the final statement at these choices (log2, before and after the grind)
  P4  where note 16's term s C(L,2) eps^(s-1) would bind: the proved bound against the floor, and the point
      counts of the hypothetical "no q^3" and "no nesting" variants with the corrected term
  P5  costs of the attack paths of note 20, section 5, in hash evaluations (log2), as a function of the number of
      points of a single batch
  P6  Theorem B of note 16 with its unconditional input |T_un| <= L q^2: the same counts as Lemma F; and the
      corrected hypothetical ladder (single-round constant s C(L,2) eps^(s-1), nothing proves it)
"""
from fractions import Fraction
from math import comb, log2

Q = 1 << 128
MU30 = [(24, 6), (20, 4), (16, 4), (12, 4), (8, 4), (4, 4)]  # (kappa_i, ell_i), derive_config(30, R) for every R
K0 = (1 << 9) * Q
TAU = Fraction(1, 1 << 119)
THETA = K0 * (K0 - 1) * (K0 - 2 * Q)  # note 14, Lemma F with M = 2q
BUDGET_PT = Fraction(1, 1 << 110)  # 15-bit grind
GRIND = dict(pt=15, batch=7, fold=7, query=17, tail=0)


def lg(x):
    """log2 of a positive Fraction or int, without overflow."""
    x = Fraction(x)
    return log2(x.numerator) - log2(x.denominator) if x.numerator.bit_length() < 900 and x.denominator.bit_length() < 900 else (
        x.numerator.bit_length() - x.denominator.bit_length()
    )


def eps(kappa, ell):
    d = (1 << kappa) - 1 + ell
    return Fraction(d + (1 << ell) - 1, Q)


def c1(L):
    """The single-round constant of Lemma F(1): Pr[Exc] <= c1 * eps^s."""
    return Fraction(L**3 * Q**6, THETA)


def nest(ell):
    return sum(TAU ** (-j) for j in range(ell))


def pt_error_one_batch(L, kappa, ell, s):
    e = eps(kappa, ell)
    return (comb(L, 2) + c1(L) * nest(ell)) * e**s


def points_one_batch(L, kappa, ell, budget=BUDGET_PT):
    s = 1
    while pt_error_one_batch(L, kappa, ell, s) > budget:
        s += 1
    return s


def pt_error_ladder(L, kappa, ell, sigma):
    e = eps(kappa, ell)
    return comb(L, 2) * e ** sigma[0] + c1(L) * sum(TAU ** (-(j)) * e ** sigma[j] for j in range(ell))


def ladder(L, kappa, ell, budget=BUDGET_PT):
    """Least sigma_1 <= ... <= sigma_ell (points available at round j) with the ladder's point error within budget.
    Greedy: the least value of each term alone, then raise the latest round whose term is largest until the sum fits,
    then lower any entry that can be lowered (earliest first, since early points cost the prover most)."""
    e = eps(kappa, ell)
    sigma = []
    for j in range(ell):
        s = 1
        while c1(L) * TAU ** (-j) * e**s > budget:
            s += 1
        sigma.append(max(s, sigma[-1] if sigma else 1))
    while comb(L, 2) * e ** sigma[0] > budget:
        sigma[0] += 1
    sigma = [max(sigma[: j + 1]) for j in range(ell)]
    while pt_error_ladder(L, kappa, ell, sigma) > budget:
        terms = [c1(L) * TAU ** (-j) * e ** sigma[j] for j in range(ell)]
        terms[0] += comb(L, 2) * e ** sigma[0]
        j = max(range(ell), key=lambda i: (terms[i], i))
        sigma[j] += 1
        for i in range(j + 1, ell):
            sigma[i] = max(sigma[i], sigma[j])
    changed = True
    while changed:
        changed = False
        for j in range(ell):
            trial = list(sigma)
            trial[j] -= 1
            if trial[j] >= 1 and (j == 0 or trial[j] >= trial[j - 1]) and pt_error_ladder(L, kappa, ell, trial) <= budget:
                sigma, changed = trial, True
    return sigma


def scalars_one_batch(s, ell):
    return s * (ell + 1)


def scalars_ladder(sigma):
    ell = len(sigma)
    batches = [sigma[0]] + [sigma[j] - sigma[j - 1] for j in range(1, ell)]
    # a point of batch b (1-based) costs one answer and one phi per round b..ell
    return sum(b_pts * (ell - b + 2) for b, b_pts in enumerate(batches, start=1)), batches


def table_p1_p2():
    print("P1/P2. Points per level at mu = 30 (kappa, ell) = " + ", ".join(f"({k},{l})" for k, l in MU30))
    print("       K0 = 2^9 q, tau = 2^-119, point budget 2^-110 (15-bit grind). Valid for every level-0 rate: n_i <= 2^28 enters only through C(n,2) <= 2q.")
    for b in (40, 100):
        L = 1 << b
        one = [points_one_batch(L, k, l) for k, l in MU30]
        lad = [ladder(L, k, l) for k, l in MU30]
        print(f"  list budget 2^{b}:")
        print(f"    one batch (Theorem D'): s_i = {one}   scalars {sum(scalars_one_batch(s, l) for s, (_, l) in zip(one, MU30))}")
        tot = 0
        for (k, l), sg in zip(MU30, lad):
            sc, batches = scalars_ladder(sg)
            tot += sc
            print(f"    ladder kappa={k:2d}: available per round {sg}, batches {'+'.join(map(str, batches))}, scalars {sc},"
                  f" log2 error {lg(pt_error_ladder(L, k, l, sg)):.1f}")
        print(f"    ladder scalars in all: {tot}")
        for (k, l), s in zip(MU30, one):
            print(f"    one batch kappa={k:2d}: log2 eps = {lg(eps(k, l)):.3f}, log2 point error at s={s}: {lg(pt_error_one_batch(L, k, l, s)):.1f},"
                  f" at s-1: {lg(pt_error_one_batch(L, k, l, s - 1)):.1f}")


def table_p3():
    print("\nP3. Per-message errors of the final statement (log2; after the grind in brackets)")
    j0 = 512
    batch = Fraction(j0 + 1, Q)
    fold = Fraction(K0 - 1, Q * Q) + TAU
    fold_last = Fraction(K0 - 1, Q * Q)
    print(f"  ring switch and lambda_0, (J0+1)/q with J0 = 512: {lg(batch):.3f} [{lg(batch) - GRIND['batch']:.3f}]")
    print(f"  fold round j < ell: (K0-1)/q^2 + tau = {lg(fold):.3f} [{lg(fold) - GRIND['fold']:.3f}]; j = ell: {lg(fold_last):.3f} [{lg(fold_last) - GRIND['fold']:.3f}]")
    print(f"  tail round: 2/q = {lg(Fraction(2, Q)):.1f} [no grind]")
    # query message: ((A-1)/n)^t + (sigma + t)/q, at rate 1/2 level 0 for three thresholds
    for name, frac, n_log in (("rate 1/2, A_0 - 1 = 0.64 n", Fraction(64, 100), 25), ("rate 1/2, A_0 - 1 = 5n/8", Fraction(5, 8), 25),
                              ("rate 1/4, A_0 - 1 = 3n/8", Fraction(3, 8), 26), ("rate 1/2, Johnson, deployed t = 218, (A_0-1)/n = 0.70931", Fraction(70931, 100000), 25)):
        t = 1
        while frac**t + Fraction(14 + t, Q) > Fraction(1, 1 << 108):
            t += 1
        err = frac**t + Fraction(14 + t, Q)
        print(f"  queries of level 0, {name}: t = {t}, error {lg(err):.2f} [{lg(err) - GRIND['query']:.2f}]")


def table_p4():
    print("\nP4. Note 16's term s C(L,2) eps^(s-1) against the proved bound, and corrected hypothetical counts")
    for b in (40, 100):
        L = 1 << b
        print(f"  list budget 2^{b}:")
        for k, l in MU30:
            e = eps(k, l)
            s = points_one_batch(L, k, l)
            proved = pt_error_one_batch(L, k, l, s)
            floor = s * comb(L, 2) * e ** (s - 1)
            # counts if the single-round constant were only the structured terms (hypothetical; nothing proves it)
            def need(fn):
                x = 1
                while fn(x) > BUDGET_PT:
                    x += 1
                return x
            wrong_nonest = need(lambda x: l * comb(L, 2) * e**x)  # note 10's conjecture, union over rounds
            right_nonest = need(lambda x: l * (x * comb(L, 2) * e ** (x - 1) + comb(L, 2) * e**x) if x > 1 else 1)
            wrong_nest = need(lambda x: comb(L, 2) * e**x * nest(l))  # note 15, section 7, last table (one batch)
            right_nest = need(lambda x: (x * comb(L, 2) * e ** (x - 1)) * nest(l) + comb(L, 2) * e**x if x > 1 else 1)
            print(f"    kappa={k:2d}: s = {s}; log2 proved bound {lg(proved):8.1f}; log2 [s C(L,2) eps^(s-1)] = {lg(floor):8.1f}"
                  f" (ratio 2^{lg(proved) - lg(floor):.0f});  hypothetical counts: no q^3, no nesting: {wrong_nonest} with eps^s, {right_nonest} corrected;"
                  f" no q^3, with nesting: {wrong_nest} with eps^s, {right_nest} corrected")


def table_p5():
    print("\nP5. Attack paths against a single batch of s points (log2 hash evaluations; the path cost is the largest step)")
    print("    level 0, mu = 30. Steps: wait for special points (15-bit grind), win a fold round (7-bit grind), pass the queries.")
    kappa, ell = MU30[0]
    d = (1 << kappa) - 1 + ell
    rows = []
    for s in (1, 2, 3):
        # (a) flats at rate 1/4, uniform points: all s points in D, then the clique of flats through them
        n = 1 << 26
        wait = 15 + s * (128 - 26)
        clique = 26 - s
        fold = 7 + 128 - clique
        rows.append((f"s={s}  flats, rate 1/4, all s points in D (uniform points)", wait, fold, max(wait, fold)))
        # (b) k members sharing a factor R of degree r = d/4 (needs a list of 2^11 members at degree 3d/4 beyond the threshold)
        r = d // 4
        wait = 15 + s * (128 - log2(r))
        fold = 7 + 128 - 11
        rows.append((f"s={s}  2^11 members U_1 + R H_a, deg R = d/4, all s points at roots of R", wait, fold, max(wait, fold)))
        # (c) note 16's lines: s-1 special points, then k lines for (p) but the running claim aligns at most two of them
        wait = 15 + (s - 1) * (128 - log2(d)) - log2(s)
        fold = 7 + 127  # 2q of q^2 challenges
        rows.append((f"s={s}  members sharing s-1 answers, in general position, false claim: two lines", wait, fold, max(wait, fold)))
        # (d) the same with k members on one affine line G + h Delta: all k lines (Proposition R3), k <= (n-d)/(A-d)
        for kk, where in ((15, "k = 15 (rate 1/16, A = 2d)"), (1 << 11, "k = 2^11 (needs A - d < (n-d)/2^11)")):
            fold_k = 7 + 128 - log2(kk)
            rows.append((f"s={s}  the same on one affine line, {where}: k lines", wait, fold_k, max(wait, fold_k)))
    rows.append(("any s  one member with a false claim (its conic)", 0, 7 + 127, 7 + 127))
    rows.append(("any s  one pole line", 0, 7 + 128, 7 + 128))
    rows.append(("any s  batching escape, (J0+1)/q, 7-bit grind", 0, 7 + 128 - log2(513), 7 + 128 - log2(513)))
    rows.append(("any s  queries against a word at agreement A_0 - 1 (the baseline)", 0, 125, 125))
    for name, wait, fold, cost in rows:
        print(f"    {name:86s} wait {wait:6.1f}  escape {fold:6.1f}  path >= {cost:6.1f}  {'REAL (below 125)' if cost < 125 else ''}")


def table_p6():
    print("\nP6. Theorem B of note 16, unconditional input, and the corrected hypothetical ladder")
    for b in (40, 100):
        L = 1 << b
        counts, hyp = [], []
        for k, l in MU30:
            e = eps(k, l)
            x = 2
            while True:
                ku = K0 - x * Q - L  # K* = max(2q, sq) + N_P + K_u <= K0
                third = Fraction((L * Q * Q) ** 3, ku * (ku - 1) * (ku - Q)) * e**x
                err = comb(L, 2) * e**x + Fraction(comb(x, 2), Q) + (x * comb(L, 2) * e ** (x - 1) + third) * nest(l)
                if err <= BUDGET_PT:
                    break
                x += 1
            counts.append(x)
            # hypothetical ladder: term_j = sigma_j C(L,2) eps^(sigma_j - 1) tau^-(j-1), each within budget / ell
            sg = []
            for j in range(l):
                y = 2
                while y * comb(L, 2) * e ** (y - 1) * TAU ** (-j) > BUDGET_PT / l:
                    y += 1
                sg.append(max(y, sg[-1] if sg else 2))
            hyp.append("+".join(map(str, [sg[0]] + [sg[j] - sg[j - 1] for j in range(1, l)])))
        print(f"  list budget 2^{b}: Theorem B with |T_un| <= L q^2 and K_u = K0 - s q - L: s_i = {counts} (Lemma F: {[points_one_batch(L, k, l) for k, l in MU30]})")
        print(f"    hypothetical ladders with the corrected structured term only: {', '.join(hyp)}")


def selftest():
    # the two closed forms quoted in note 14, section 7.4: 3b + 1062 at level 0 and 3b + 824 at ell = 4
    for b in (7, 40, 100):
        L = 1 << b
        for (k, l), const in ((MU30[0], 1062), (MU30[1], 824)):
            s = points_one_batch(L, k, l)
            need_bits = 3 * b + const
            assert (s - 1) * -lg(eps(k, l)) < need_bits + 1 and s * -lg(eps(k, l)) >= need_bits - 1, (b, k, s)
    # numbers printed by notes 14 (T3), 15 (section 7) and 16 (section 8)
    assert [points_one_batch(1 << 40, k, l) for k, l in MU30] == [12, 9, 9, 9, 8, 8]
    assert [points_one_batch(1 << 100, k, l) for k, l in MU30] == [14, 11, 11, 10, 10, 10]
    print("selftest: closed forms 3b + 1062 and 3b + 824, and the one-batch counts of notes 14 to 16, reproduced")


if __name__ == "__main__":
    selftest()
    table_p1_p2()
    table_p3()
    table_p4()
    table_p5()
    table_p6()
