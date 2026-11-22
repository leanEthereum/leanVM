#!/usr/bin/env python3
"""Note 42, Lemma M (sequential count) with four members, exactly, on a toy field.

GF(7), lines (k = 2), n = 5 points, members f_1 = 0, f_2, f_3, f_4 pairwise distinct. For every point
tuple (normalized to a_1 = 0, a_2 = 1 by the affine symmetry) and every triple (f_2, f_3, f_4) the script
records, at each coordinate, the partition of the four members into classes of equal value. A labeling
gives each coordinate nothing, F(p, U) (f_j = f_p there for j in U, U nonempty, U > p) or R(p, p', U)
(f_p = f_p' = f_j there for j in U, p < p' < U). The expected number of triples satisfying a labeling is
computed exactly and compared with

    m^n/(m)_n * q^(sum_j (k - c_j)_+) * (h/m)^g,    c_j = number of labels with j in U, g = number of R labels.

All 23 labels occur. The labelings tested: 3000 random ones, and every labeling of the shape used in
Theorem C (centre 1, second parent 2, leaves 3 and 4) with at most one label of each kind per coordinate.

Usage: python3 42_lemmaM_t4.py     (about a minute)
"""
import itertools
import random
from collections import Counter
from fractions import Fraction as Fr

P, K, N, T = 7, 2, 5, 4


def labels():
    out = [("0", None, None, frozenset())]
    for p in range(1, T):
        later = list(range(p + 1, T + 1))
        for r in range(1, len(later) + 1):
            for U in itertools.combinations(later, r):
                out.append(("F", p, None, frozenset(U)))
    for p in range(1, T):
        for pp in range(p + 1, T + 1):
            later = list(range(pp + 1, T + 1))
            for r in range(0, len(later) + 1):
                for U in itertools.combinations(later, r):
                    out.append(("R", p, pp, frozenset(U)))
    return out


LABELS = labels()


def needs(label):
    """pairs of members that must be equal at the coordinate."""
    kind, p, pp, U = label
    if kind == "0":
        return []
    req = [(p, j) for j in U]
    if kind == "R":
        req.append((p, pp))
    return req


def main():
    polys = list(itertools.product(range(P), repeat=K))
    hist = Counter()
    tuples = 0
    for rest in itertools.permutations([x for x in range(P) if x > 1], N - 2):
        a = (0, 1) + rest
        tuples += 1
        vals = [tuple((c0 + c1 * x) % P for x in a) for c0, c1 in polys]
        zero = vals[0]
        for i2 in range(1, len(polys)):
            v2 = vals[i2]
            for i3 in range(1, len(polys)):
                if i3 == i2:
                    continue
                v3 = vals[i3]
                for i4 in range(1, len(polys)):
                    if i4 == i2 or i4 == i3:
                        continue
                    v4 = vals[i4]
                    sig = tuple((zero[i], v2[i], v3[i], v4[i]) for i in range(N))
                    # canonical form of the equality pattern at each coordinate
                    key = tuple(tuple(s.index(x) for x in s) for s in sig)
                    hist[key] += 1
    corr = Fr(P ** N)
    for i in range(N):
        corr /= (P - i)
    patterns = {}
    for key in hist:
        for pat in key:
            if pat not in patterns:
                patterns[pat] = {lab: all(pat[u - 1] == pat[v - 1] for u, v in needs(lab)) for lab in LABELS}

    def check(lab_tuple):
        total = 0
        for key, cnt in hist.items():
            if all(patterns[key[i]][lab_tuple[i]] for i in range(N)):
                total += cnt
        expect = Fr(total, tuples)
        c = [0] * (T + 1)
        g = 0
        for lab in lab_tuple:
            for j in lab[3]:
                c[j] += 1
            g += lab[0] == "R"
        bound = corr * Fr(P) ** sum(max(K - c[j], 0) for j in range(2, T + 1)) * Fr(K - 1, P) ** g
        return expect, bound

    rng = random.Random(42)
    viol = 0
    best = Fr(0)
    used = set()
    window = 0
    for _ in range(3000):
        lt = tuple(rng.choice(LABELS) for _ in range(N))
        used.update(lt)
        e, b = check(lt)
        viol += e > b
        if Fr(1, 100) <= b <= 100 and e > 0:
            window += 1
            best = max(best, e / b)
    print(f"GF({P}), k = {K}, n = {N}, t = {T}: {tuples} point tuples, {sum(hist.values())} configurations, {len(LABELS)} labels")
    print(f"3000 random labelings ({len(used)} distinct labels used): violations of Lemma M: {viol}; "
          f"{window} have a bound in [0.01, 100] and a nonzero expectation, largest expectation/bound among them {float(best):.3f}")
    # the alphabet of Theorem C: F(1,U), F(2,U), R(1,3,U), R(2,3,U), R(3,4,0)
    alphaC = [lab for lab in LABELS if lab[0] == "0" or (lab[0] == "F" and lab[1] in (1, 2)) or (lab[0] == "R" and lab[2] == 3 and lab[1] in (1, 2)) or (lab[0] == "R" and (lab[1], lab[2]) == (3, 4))]
    viol = cnt = 0
    best = Fr(0)
    for lt in itertools.combinations_with_replacement(alphaC, N):
        e, b = check(lt)
        cnt += 1
        viol += e > b
        if 0 < b <= 100 and e > 0:
            best = max(best, e / b)
    print(f"alphabet of Theorem C ({len(alphaC)} labels), all {cnt} multisets of {N} labels: violations: {viol}; largest expectation/bound where the bound is at most 100: {float(best):.3f}")


if __name__ == "__main__":
    main()
