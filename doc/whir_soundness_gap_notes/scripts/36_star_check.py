#!/usr/bin/env python3
"""Note 36, Lemma B1 (star counting): exhaustive check on toy fields.

For a prime p, polynomials of degree < k over GF(p), n evaluation points drawn as ordered tuples of
distinct field elements, and t sets I_1..I_t of [n], count exactly the tuples a for which there are
pairwise distinct polynomials f_1..f_t with
    f_j(a_i) = f_1(a_i)   for i in I_1 and j in S_i = {j >= 2 : i in I_j}      (label D)
    f_j(a_i) = f_j'(a_i)  for i not in I_1, j < j' the two smallest of S_i      (label C)
and compare with the bound  p^(n - g) * (k-1)^g * p^(sum_j (k - c_j)),  zero if some c_j >= k,
where g is the number of C coordinates and c_j = |I_1 cap I_j|.

By translation f_1 = 0. Usage: python3 36_star_check.py   (a few seconds)
"""
import itertools
import random


def polys(p, k):
    return list(itertools.product(range(p), repeat=k))


def ev(f, x, p):
    r = 0
    for c in reversed(f):
        r = (r * x + c) % p
    return r


def check(p, k, n, sets, rng):
    t = len(sets)
    I1 = sets[0]
    D = []  # (i, members)
    C = []  # (i, j, j')
    for i in range(n):
        S = [j for j in range(1, t) if i in sets[j]]
        if i in I1 and S:
            D.append((i, S))
        elif i not in I1 and len(S) >= 2:
            C.append((i, S[0], S[1]))
    c = [0] * t
    for i, S in D:
        for j in S:
            c[j] += 1
    g = len(C)
    if any(c[j] >= k for j in range(1, t)):
        bound = 0
    else:
        bound = p ** (n - g) * (k - 1) ** g * p ** sum(k - c[j] for j in range(1, t))
    P = [f for f in polys(p, k) if any(f)]
    table = {f: [ev(f, x, p) for x in range(p)] for f in P}
    bad = 0
    for a in itertools.permutations(range(p), n):
        # candidates for each member: nonzero polynomials vanishing on its D points
        cands = []
        for j in range(1, t):
            pts = [a[i] for i, S in D if j in S]
            cands.append([f for f in P if all(table[f][x] == 0 for x in pts)])
        found = False
        for tup in itertools.product(*cands):
            if len(set(tup)) < len(tup):
                continue
            if all(table[tup[j - 1]][a[i]] == table[tup[jj - 1]][a[i]] for i, j, jj in C):
                found = True
                break
        bad += found
    return bad, bound, c[1:], g


def averaging_check(rng):
    """Lemma 1 for the star functional: for column counts m_i (coordinate i lies in m_i of the M sets),
    the exact expectation of Psi over ordered t-tuples of distinct members is at least
    n psi_cc(mean density) - C(t,2)/M n (alpha (t-1) + beta)."""
    from math import comb

    worst = float("inf")
    for trial in range(400):
        n = rng.choice((50, 200))
        M = rng.choice((40, 200, 1000))
        t = rng.choice((2, 3, 5, 8, 16))
        alpha, beta = rng.choice(((64.0, 40.0), (128.0, 104.0), (64.0, 60.0), (1.0, 50.0)))
        kind = rng.randrange(4)
        if kind == 0:
            ms = [rng.randrange(0, M + 1) for _ in range(n)]
        elif kind == 1:
            ms = [M if rng.random() < 0.3 else rng.randrange(0, M // 10 + 1) for _ in range(n)]
        elif kind == 2:
            ms = [rng.randrange(0, M // 5 + 1) for _ in range(n)]
        else:
            c0 = rng.randrange(0, M + 1)
            ms = [c0] * n
        tau = sum(ms) / (M * n)

        def exact(mi):
            # first member contains i, then the number of the other t-1 containing i
            p1 = mi / M
            d_part = p1 * (t - 1) * (mi - 1) / (M - 1) if M > 1 else 0.0
            # first member misses i, at least two of the other t-1 (drawn from M-1, mi of them contain i) contain it
            tot = comb(M - 1, t - 1)
            p0 = comb(M - 1 - mi, t - 1) / tot if M - 1 - mi >= t - 1 else 0.0
            p1h = mi * comb(M - 1 - mi, t - 2) / tot if (M - 1 - mi >= t - 2 and t >= 2) else 0.0
            c_part = (1 - p1) * max(0.0, 1.0 - p0 - p1h)
            return alpha * d_part + beta * c_part

        lhs = sum(exact(mi) for mi in ms)
        G = 2000
        xs = [g / G for g in range(G + 1)]
        T = t - 1
        ys = [alpha * T * x * x + beta * (1 - x) * (1 - (1 - x) ** T - T * x * (1 - x) ** (T - 1)) if x < 1 else alpha * T for x in xs]
        hull = []
        for pt in zip(xs, ys):
            while len(hull) >= 2:
                (x1, y1), (x2, y2) = hull[-2], hull[-1]
                if (x2 - x1) * (pt[1] - y1) - (y2 - y1) * (pt[0] - x1) <= 0:
                    hull.pop()
                else:
                    break
            hull.append(pt)
        cc = None
        for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
            if x1 <= tau <= x2:
                cc = y1 + (y2 - y1) * (tau - x1) / (x2 - x1)
        rhs = n * cc - comb(t, 2) / M * n * (alpha * T + beta)
        assert lhs >= rhs - 1e-6 * (1 + abs(rhs)), (n, M, t, alpha, beta, kind, lhs, rhs)
        worst = min(worst, lhs - rhs)
    print(f"averaging lemma: 400 random column-count profiles, exact expectation >= bound in all (smallest slack {worst:.3f})")


def main():
    rng = random.Random(36)
    worst = 0.0
    cases = 0
    nontrivial = 0
    for p, k, n, t, reps in ((5, 2, 4, 3, 40), (5, 2, 5, 3, 25), (7, 2, 4, 3, 25), (5, 2, 4, 4, 12), (5, 3, 5, 3, 10), (7, 3, 5, 3, 3)):
        for _ in range(reps):
            sets = [set(i for i in range(n) if rng.random() < 0.6) for _ in range(t)]
            bad, bound, c, g = check(p, k, n, sets, rng)
            cases += 1
            total = 1
            for u in range(n):
                total *= p - u
            nontrivial += bound < total
            assert bad <= bound, (p, k, n, sets, bad, bound)
            if bound:
                worst = max(worst, bad / bound)
        print(f"p={p} k={k} n={n} t={t}: {reps} random set systems, count <= bound in all", flush=True)
    print(f"{cases} cases, {nontrivial} with a bound below the number of tuples, largest count/bound = {worst:.4f}")
    averaging_check(rng)


if __name__ == "__main__":
    main()
