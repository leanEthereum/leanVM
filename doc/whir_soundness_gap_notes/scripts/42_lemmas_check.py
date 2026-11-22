#!/usr/bin/env python3
"""Note 42: the two combinatorial lemmas on explicit set families, by exhaustive enumeration.

Lemma 1 of note 36 (averaging): among M sets of size A in [n] some ordered t-tuple of distinct members has
    Psi = alpha * W_D + beta * g >= n psi_cc(A/n) - C(t,2) n (alpha (t-1) + beta) / M
for the canonical star labeling (W_D = sum over the coordinates of I_1 of the number of other members
containing them, g = number of coordinates outside I_1 in at least two of the others).
Checked here with the exact maximum over all ordered triples and quadruples, on families built to be
irregular: random, two populations with different cores, a common core, a two-point density profile,
nested populations.

Lemma R of note 42 (one pigeonhole step): if every member of a family of N sets has y elements in a region X,
there are a member I*, a value v >= y^2/|X| - y/(N-1) - 1 and at least (N-1)/(n(n+1)) other members I with
|I cap I* cap X| = v. Checked on the same families, with X = [n] and with X = the complement of a member
(after restricting to the members with a common count in it).

Usage: python3 42_lemmas_check.py   (about a minute)
"""
import importlib.util
import itertools
import math
import os
import random
from collections import Counter

spec = importlib.util.spec_from_file_location("tb", os.path.join(os.path.dirname(os.path.abspath(__file__)), "42_theoremB.py"))
tb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tb)


def families(rng, n, A, M):
    full = list(range(n))
    yield "uniform random", [frozenset(rng.sample(full, A)) for _ in range(M)]
    core = rng.sample(full, A // 3)
    rest = [i for i in full if i not in core]
    yield "common core of A/3", [frozenset(core + rng.sample(rest, A - len(core))) for _ in range(M)]
    c1, c2 = rng.sample(full, A // 2), rng.sample(full, A // 2)
    fam = []
    for j in range(M):
        c = c1 if j % 2 else c2
        r = [i for i in full if i not in c]
        fam.append(frozenset(c + rng.sample(r, A - len(c))))
    yield "two populations, cores of A/2", fam
    low = full[: n // 2]
    high = full[n // 2:]
    fam = []
    for _ in range(M):
        a_high = min(len(high), max(0, int(round(0.8 * A))))
        fam.append(frozenset(rng.sample(high, a_high) + rng.sample(low, A - a_high)))
    yield "two-point profile (80% of each set in half of the coordinates)", fam
    fam = []
    for j in range(M):
        b = [core[: len(core) // 2], c1[: A // 4], c2[: A // 4]][j % 3]
        b = list(dict.fromkeys(b + (c1 if (j // 3) % 2 else c2)[: A // 3]))[: A - 1]
        r = [i for i in full if i not in b]
        fam.append(frozenset(b + rng.sample(r, A - len(b))))
    yield "nested populations", fam


def star_psi(sets, order, alpha, beta):
    I1 = sets[order[0]]
    others = [sets[j] for j in order[1:]]
    W = sum(len(I1 & S) for S in others)
    cnt = Counter()
    for S in others:
        for i in S:
            if i not in I1:
                cnt[i] += 1
    g = sum(1 for v in cnt.values() if v >= 2)
    return alpha * W + beta * g


def main():
    rng = random.Random(42)
    worst = math.inf
    cases = 0
    for n, A, M, t in ((24, 12, 30, 3), (30, 18, 40, 3), (40, 12, 40, 3), (20, 10, 16, 4), (30, 9, 18, 4)):
        for alpha, beta in ((64.0, 40.0), (128.0, 104.0), (10.0, 60.0)):
            p = tb.Psi(t, alpha, beta)
            guarantee = n * p.cc(A / n) - math.comb(t, 2) * n * (alpha * (t - 1) + beta) / M
            for name, fam in families(rng, n, A, M):
                fam = list(dict.fromkeys(fam))
                best = max(star_psi(fam, order, alpha, beta) for order in itertools.permutations(range(len(fam)), t))
                g2 = n * p.cc(A / n) - math.comb(t, 2) * n * (alpha * (t - 1) + beta) / len(fam)
                assert best >= g2 - 1e-9, (name, n, A, M, t, best, g2)
                worst = min(worst, best - g2)
                cases += 1
    print(f"Lemma 1: {cases} families (n <= 40, M <= 40, t = 3, 4, three weightings), exact maximum over all ordered tuples >= the bound in all; smallest slack {worst:.2f}")

    ok = 0
    for n, A, M in ((16, 8, 3000), (20, 6, 4000), (24, 12, 4000)):
        for name, fam in families(rng, n, A, M):
            fam = list(dict.fromkeys(fam))
            # step 1: X = [n]
            N = len(fam)
            found = None
            for Istar in fam:
                vals = Counter(len(I & Istar) for I in fam if I is not Istar)
                mu = A * A / n - A / (N - 1) - 1
                for v, c in vals.items():
                    if v >= mu and c >= (N - 1) / (n * (n + 1)):
                        if found is None or v > found[1]:
                            found = (Istar, v, c)
                if found:
                    break
            assert found, (name, n, A, M)
            I1, c1, _ = found
            L1 = [I for I in fam if I is not I1 and len(I & I1) == c1]
            # step 2: X = complement of I1, y = A - c1
            X = frozenset(range(n)) - I1
            y, N1 = A - c1, len(L1)
            if N1 >= 2 and len(X) > 0:
                found2 = None
                mu = y * y / len(X) - y / (N1 - 1) - 1
                for Istar in L1:
                    vals = Counter(len(I & Istar & X) for I in L1 if I is not Istar)
                    if any(v >= mu and c >= (N1 - 1) / (n * (n + 1)) for v, c in vals.items()):
                        found2 = Istar
                        break
                assert found2 is not None, (name, n, A, M, c1, N1)
            ok += 1
    print(f"Lemma R: {ok} families, the member, the value and the class exist at both steps in all")


if __name__ == "__main__":
    main()
