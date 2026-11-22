#!/usr/bin/env python3
"""Rates 1/4, 1/8, 1/16: the economical window of note 35 and explicit first integrals inside it
(Sections 5 and 6 of 43-low-rate-residuals.md).  Exact integers; imports Rloc, Ncoef, a1, lemmaC_ok of 35_counts.py.

  A  leading-order threshold e*(rho, a) = rho(1 - beta/2)/(a - rho beta/2) at the largest beta <= 1/2 with J(beta) >= 0,
     and the largest Y1-degree b of a smooth economical component, b < 2 e*/rho - 2.
  B  exact test of Lemma C (inequality (2) of note 35, multiplicities up to 600) on explicit b = 1 first integrals
     with simple contact along all (or all but one) of the n lines:
       C4   the flat cubic of rate 1/4, E = X Y^3 + (X gamma + e0) Y + e0 X^(n/2-1)        (any subspace domain)
       Q8   E_theta = X^3 Y^5 + theta X Y^3 + (theta X^(n/2-1) + X gamma + e0) Y + e0 X^(n/4-1)   (any subspace domain)
       R    E = Y^5 + c X Y + c^(5/4) X^(n/4+1)                                             (D = F_{2^N})
     "not cut" means that no (m, B) with m in the list makes (2) true: the component is economical there.
  C, D  see the docstrings of part_C and part_D (uniform exact evaluation at n = 2^25).
Run: python3 43_rates.py [A] [B] [C] [D]   (about 1 minute)
"""
import importlib
import sys
from math import sqrt, ceil, log2

sys.path.insert(0, sys.path[0] or ".")
c35 = importlib.import_module("35_counts")


def estar(rho, a):
    # J(beta) = (a^2/rho - 1)/2 + (1 - a) beta - (2 - rho)/2 beta^2
    A, B, C = -(2 - rho) / 2, (1 - a), (a * a / rho - 1) / 2
    disc = B * B - 4 * A * C
    if disc < 0:
        return None
    hi = (-B - sqrt(disc)) / (2 * A)
    beta = min(hi, 0.5)
    return rho * (1 - beta / 2) / (a - rho * beta / 2), beta


def part_A():
    print("A. e*(rho, a) and the largest b of a smooth economical component (leading order)")
    for R in (2, 3, 4):
        rho = 2.0 ** -R
        a1 = c35.a1(rho)
        for a in (a1 + 0.001, (a1 + sqrt(rho)) / 2, sqrt(rho) - 0.001):
            e, beta = estar(rho, a)
            bmax = ceil(2 * e / rho - 2) - 1
            print(f"   rate 1/{2**R}: a = {a:.4f}  beta = {beta:.3f}  e* = {e:.4f}  2e*/rho - 2 = {2*e/rho - 2:.3f}"
                  f"  b <= {bmax}   queries ceil(108/log2(1/a)) = {ceil(108 / log2(1 / a))}")


def part_B():
    print("B. exact Lemma C on explicit first integrals (n = 2^20, Delta = k - 1, m in 60..600)")
    n = 1 << 20
    ms = (60, 120, 240, 600)
    cases = []
    for R, name in ((3, "C4"), (4, "C4"), (3, "Q8"), (4, "Q8"), (3, "R"), (4, "R")):
        k = n >> R
        D = k - 1
        if name == "C4":
            W = max(3 * D + 1, n // 2 - 1 + D)
            prof = [(n - 1, 2), (1, 0)]
        elif name == "Q8":
            W = max(5 * D + 3, n // 2 - 1 + D)
            prof = [(n - 1, 2), (1, 0)]
        else:
            W = max(5 * D, n // 4, D + 1)
            prof = [(n, 2)]
        cases.append((R, name, D, W, prof))
    for (R, name, D, W, prof) in cases:
        rho = 2.0 ** -R
        a1 = c35.a1(rho)
        row = []
        for a in (a1 + 0.001, a1 + 0.005, a1 + 0.01, a1 + 0.015, a1 + 0.02, sqrt(rho) - 0.001):
            if a >= sqrt(rho):
                continue
            A = ceil(a * n)
            r = c35.lemmaC_ok(n, D, A, 1, W, prof, ms)
            row.append(f"a={a:.4f}: {'cut ' + str(r) if r else 'NOT CUT'}")
        tot = sum(c * o for c, o in prof)
        print(f"   rate 1/{2**R} {name:3s} W/n = {W/n:.4f}  e = W/sum(o) = {W/tot:.4f} : " + "; ".join(row))



def part_C():
    """n = 2^25, Delta = k + 5: uniform exact evaluation of Lemma C on every first integral with total contact
    <= 2n (Lemma U (a) of note 41: the right side of (2) is at most n*(R(m,B) - R(m-2,B-b))), the side condition
    of Lemma C imposed at the largest weighted degree m0*A - 1 of a factor of an explainer with certificate (m0, B0).
    For each b <= B0: is every such factor with W >= (b+2)*Delta cut?  If not, the smallest W0 from which it is."""
    print("C. n = 2^25, Delta = k + 5, a = a_1 + eps: factors with total contact <= 2n and W >= (b+2) Delta")
    n = 1 << 25
    for R in (2, 3, 4):
        rho = 2.0 ** -R
        k = n >> R
        D = k + 5
        for eps, (m0, B0) in zip((0.005, 0.01), {2: ((43, 19), (22, 9)), 3: ((39, 20), (19, 10)), 4: ((31, 19), (16, 9))}[R]):
            a = c35.a1(rho) + eps
            A = ceil(a * n)
            assert c35.Ncoef(B0, m0 * A, D) > n * c35.Rloc(m0, B0), "certificate"
            Wmax = m0 * A - 1
            mlist = list(range(m0 + 1, 3 * m0, 2)) + [4 * m0, 6 * m0]
            out = []
            mmax = 0
            for b in range(1, B0 + 1):
                Wlow = (b + 2) * D
                cutat = None
                for m in mlist:
                    Z = m * A
                    for B in range(b, m // 2 + 1):
                        if D * (m + B) > Z - Wmax:
                            break
                        cost = n * (c35.Rloc(m, B) - c35.Rloc(m - 2, B - b))
                        if c35.Ncoef(B, Z, D) - c35.Ncoef(B - b, Z - Wlow, D) > cost:
                            cutat = (m, B)
                            break
                    if cutat:
                        break
                if cutat:
                    m, B = cutat
                    # hypothesis (ii) of Lemma U of note 41 for this pair: j -> R(m - 2j, B - b) is convex
                    seq = [c35.Rloc(m - 2 * jj, B - b) for jj in range(0, m // 2 + 3)]
                    assert all(seq[t - 1] + seq[t + 1] >= 2 * seq[t] for t in range(1, len(seq) - 1)), "convexity"
                    out.append(f"b={b}: cut {cutat}")
                    mmax = max(mmax, m)
                    continue
                best = None
                for m in mlist:
                    Z = m * A
                    for B in range(b, m // 2 + 1):
                        if D * (m + B) > Z - Wmax:
                            break
                        cost = n * (c35.Rloc(m, B) - c35.Rloc(m - 2, B - b))
                        full = c35.Ncoef(B, Z, D)
                        if full - c35.Ncoef(B - b, Z - Wmax, D) <= cost:
                            continue
                        lo, hi = Wlow, Wmax
                        while lo < hi:
                            mid = (lo + hi) // 2
                            if full - c35.Ncoef(B - b, Z - mid, D) > cost:
                                hi = mid
                            else:
                                lo = mid + 1
                        if best is None or lo < best[0]:
                            best = (lo, m, B)
                if best is None:
                    out.append(f"b={b}: NOT CUT at any W")
                else:
                    seq = [c35.Rloc(best[1] - 2 * jj, best[2] - b) for jj in range(0, best[1] // 2 + 3)]
                    assert all(seq[t - 1] + seq[t + 1] >= 2 * seq[t] for t in range(1, len(seq) - 1)), "convexity"
                    mmax = max(mmax, best[1])
                    out.append(f"b={b}: OPEN for W in [{b + 2}, {best[0] / D:.3f}) Delta = [{(b + 2) * D / n:.3f}, {best[0] / n:.3f}) n, cut from there by {best[1:]}")
            # case I (leading coefficient in F[X]): W >= b*Delta + sum_alpha max(j, 2j - b) >= b*Delta + s*n, s = (total
            # contact)/(2n) <= 1; the two sides of (2) are concave and linear in s, so it is enough to test s = 0, 1
            caseI = []
            for b in range(1, B0 + 1):
                ok = None
                for m in mlist:
                    Z = m * A
                    for B in range(b, m // 2 + 1):
                        if D * (m + B) > Z - Wmax:
                            break
                        full = c35.Ncoef(B, Z, D)
                        psi0 = c35.Rloc(m, B) - c35.Rloc(m, B - b)
                        psi1 = c35.Rloc(m, B) - c35.Rloc(m - 2, B - b)
                        if full - c35.Ncoef(B - b, Z - b * D, D) > n * psi0 and \
                           full - c35.Ncoef(B - b, Z - b * D - n, D) > n * psi1:
                            seq = [c35.Rloc(m - 2 * jj, B - b) for jj in range(0, m // 2 + 3)]
                            assert all(seq[t - 1] + seq[t + 1] >= 2 * seq[t] for t in range(1, len(seq) - 1))
                            ok = (m, B)
                            break
                    if ok:
                        break
                caseI.append(ok)
                if ok:
                    mmax = max(mmax, ok[0])
            print(f"   rate 1/{2**R}, a = {a:.4f}, certificate ({m0},{B0}), B_jet = {(m0 * A - 1) // D}: " + "; ".join(out))
            bad = [b + 1 for b, ok in enumerate(caseI) if ok is None]
            bj = (m0 * A - 1) // D
            per = (mmax * A - 1) // D
            print(f"      leading coefficient in F[X], total contact <= 2n: cut for every b <= {B0}" if not bad
                  else f"      leading coefficient in F[X]: NOT cut for b in {bad}")
            print(f"      largest multiplicity used {mmax}: at most {per} members per unit of degree on a cut factor; "
                  f"constant term max((B_jet - t)^2 + max({per}, B_jet/4) t) = {max((bj - t) ** 2 + max(per, bj // 4 + 1) * t for t in range(bj + 1))}")


def part_D():
    """The window that Lemma C and the Sudan step (Lemma L part 4) leave open, for a factor with simple contact on
    x*n lines and none elsewhere: W in [max((b+2) Delta, b Delta + A - (1-x) n), W0(x)), in units of n."""
    print("D. n = 2^25, Delta = k + 5: open window [lower, W0) in units of n, simple contact on x*n lines")
    n = 1 << 25
    for R, bs in ((2, (1,)), (3, (1, 2)), (4, (1, 2, 3))):
        rho = 2.0 ** -R
        k = n >> R
        D = k + 5
        for eps, (m0, B0) in zip((0.005, 0.01), {2: ((43, 19), (22, 9)), 3: ((39, 20), (19, 10)), 4: ((31, 19), (16, 9))}[R]):
            a = c35.a1(rho) + eps
            A = ceil(a * n)
            Wmax = m0 * A - 1
            mlist = list(range(m0 + 1, 3 * m0, 2)) + [4 * m0, 6 * m0]
            for b in bs:
                cells = []
                for x in (0.6, 0.7, 0.8, 0.85, 0.9, 0.95, 1.0):
                    n1 = int(x * n)
                    low = max((b + 2) * D, b * D + A - (n - n1))
                    best = None
                    for m in mlist:
                        Z = m * A
                        for B in range(b, m // 2 + 1):
                            if D * (m + B) > Z - Wmax:
                                break
                            cost = n1 * (c35.Rloc(m, B) - c35.Rloc(m - 2, B - b)) + (n - n1) * (c35.Rloc(m, B) - c35.Rloc(m, B - b))
                            full = c35.Ncoef(B, Z, D)
                            if full - c35.Ncoef(B - b, Z - Wmax, D) <= cost:
                                continue
                            lo, hi = 0, Wmax
                            while lo < hi:
                                mid = (lo + hi) // 2
                                if full - c35.Ncoef(B - b, Z - mid, D) > cost:
                                    hi = mid
                                else:
                                    lo = mid + 1
                            if best is None or lo < best:
                                best = lo
                    if best is None or best > low:
                        cells.append(f"x={x}: [{low / n:.3f}, {('%.3f' % (best / n)) if best else 'inf'})")
                    else:
                        cells.append(f"x={x}: closed")
                print(f"   rate 1/{2**R}, a = {a:.4f}, b = {b}: " + "; ".join(cells))


if __name__ == "__main__":
    args = sys.argv[1:] or ["A", "B", "C", "D"]
    if "A" in args:
        part_A()
    if "B" in args:
        part_B()
    if "C" in args:
        part_C()
    if "D" in args:
        part_D()
