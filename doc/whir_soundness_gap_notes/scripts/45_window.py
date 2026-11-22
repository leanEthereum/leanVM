#!/usr/bin/env python3
"""45_window.py: the window of the b = 1 residual after the determinant bound (Theorem 4 of
45-rate-half-second-attempt.md), exact integers, and the explicit families against Lemma C.

1. contact 4 on all n lines, b = 1, n = 2^25 .. 2^28, D = n/2 + 5: lower ends
     N  (Corollary N of note 40):   3 A + D
     B  (Lemma B of note 40):       ceil((11 n + 25 D) / 9)
     T  (Theorem 4, det != 0):      ceil((4 n + 8 D + 1) / 3)
   upper end C (Lemma C of note 35, exact, multiplicities m in MS, all B <= m/2 with the side condition).
   Non-degenerate potentials: window [max(N, B, T), C).  Degenerate ones: [max(N, B), C).
2. the smallest agreement on a grid at which the non-degenerate window is empty (n = 2^25).
3. contact 4 on x4 n lines and contact 2 on x2 n lines (leading order, grid of note 40 Section 3.2), with the
   determinant bound  w >= (4 x4 + 4 rho) * 2 / 3 ... i.e. W >= (4 x4 n + 8 D) / 3  added: open cells, non-degenerate.
4. the family on D = F_n (Theorem 7): word X^(3n/4 - j), j even, W(j) = max(4j + 5D, 2n + 1 + D, 11n/4 - j);
   exact Lemma C verdict at the three certified agreements, n = 2^25, for the best j and for j on a grid.

5. Theorem 8' of note 41 at a = 0.703 (and 0.70 for comparison), n = 2^25 .. 2^28, with the functions of 41_counts.py:
   certificate (18, 5), the uniform cuts of case I and case II with the pairs of note 41, the constant, and the
   non-degenerate window of part 1 (empty at 0.703).

Run: python3 45_window.py [1] [2] [3] [4] [5]        (about 3 minutes in total)
"""
import sys
from math import ceil
from importlib import import_module

win = import_module("40_window")
w_C, leading_wC, bezout_low = win.w_C, win.leading_wC, win.bezout_low

MS = (60, 120, 240, 480)


def ends(n, a, ms=MS):
    D = n // 2 + 5
    A = ceil(a * n)
    lowN = 3 * A + D
    lowB = -(-(11 * n + 25 * D) // 9)
    lowT = -(-(4 * n + 8 * D + 1) // 3)
    r = w_C(n, D, A, 1, [(n, 4)], ms)
    return D, A, lowN, lowB, lowT, r


def part1():
    print("1. b = 1, contact 4 on all lines: lower ends N, B, T and upper end C, in units of n")
    for N in (25, 26, 27, 28):
        n = 1 << N
        for a in (0.6919, 0.6949, 0.70):
            D, A, lowN, lowB, lowT, r = ends(n, a)
            up = r[0]
            lo_nd, lo_d = max(lowN, lowB, lowT), max(lowN, lowB)
            print(f"   n = 2^{N}, a = {a}: N = {lowN / n:.5f}, B = {lowB / n:.5f}, T = {lowT / n:.5f}, "
                  f"C = {up / n:.5f} at (m, B) = ({r[1]}, {r[2]});  non-degenerate window "
                  f"{'[%.5f, %.5f) n, width %.5f n' % (lo_nd / n, up / n, (up - lo_nd) / n) if up > lo_nd else 'EMPTY'}; "
                  f"degenerate window [{lo_d / n:.5f}, {up / n:.5f}) n")
            sys.stdout.flush()


def part2():
    n = 1 << 25
    print("2. smallest agreement at which the non-degenerate window is empty, n = 2^25 (grid of step 0.0005)")
    prev = None
    for i in range(0, 15):
        a = 0.6995 + 0.0005 * i
        D, A, lowN, lowB, lowT, r = ends(n, a, (60, 120, 240, 480, 960))
        lo = max(lowN, lowB, lowT)
        st = "empty" if r[0] <= lo else f"width {(r[0] - lo) / n:.5f} n"
        print(f"   a = {a:.4f}: lower {lo / n:.5f} n (N {lowN / n:.4f}, T {lowT / n:.4f}), C = {r[0] / n:.5f} n at m = {r[1]}: {st}; "
              f"queries {ceil(108 / (-__import__('math').log2(A / n)))}")
        sys.stdout.flush()


def part3():
    rho = 0.5
    print("3. b = 1, contact 4 on x4 n lines, contact 2 on x2 n lines (leading order): open cells with the determinant bound")
    for a in (0.6919, 0.6949, 0.70):
        opened_old = opened_new = 0
        cells = []
        for i4 in range(0, 21):
            x4 = i4 / 20
            for i2 in range(0, 21 - i4):
                x2 = i2 / 20
                obar = 4 * x4 + 2 * x2
                if obar == 0:
                    continue
                wc = leading_wC(a, rho, 1, obar)[0]
                rest = a
                x0 = 1 - x4 - x2
                s = 0.0
                rest -= min(rest, x0)
                t = min(rest, x2)
                s += t
                rest -= t
                s += 3 * rest
                lowS = s + rho
                lowB = bezout_low(11 * x4 + x2, rho)
                lowT = (4 * x4 + 8 * rho) / 3
                lo_old = max(1.5, lowS, lowB)
                lo_new = max(lo_old, lowT)
                if wc > lo_old:
                    opened_old += 1
                if wc > lo_new:
                    opened_new += 1
                    cells.append((x4, x2, round(wc - lo_new, 3)))
        print(f"   a = {a}: open cells before {opened_old}, with the determinant bound (non-degenerate) {opened_new}: {cells}")


def part4():
    n = 1 << 25
    D = n // 2 + 5
    print("4. the family on D = F_n: word X^(3n/4 - j), W(j) = max(4j + 5D, 2n + 1 + D, 11n/4 - j), n = 2^25")
    jbest = min(range(2, n // 8, 2), key=lambda j: max(4 * j + 5 * D, 2 * n + 1 + D, 11 * n // 4 - j))
    Wbest = max(4 * jbest + 5 * D, 2 * n + 1 + D, 11 * n // 4 - jbest)
    print(f"   best j = {jbest} = {jbest / n:.5f} n, W = {Wbest} = {Wbest / n:.5f} n, efficiency {Wbest / (4 * n):.5f}, "
          f"exponent {(3 * n // 4 - jbest) / n:.5f} n; every codeword with agreement > W/4 = {Wbest / 4 / n:.5f} n is a section, "
          f"and there is no polynomial section of degree <= D (Theorem 7): the list is empty above {Wbest / 4 / n:.5f} n")
    for a in (0.6919, 0.6949, 0.70):
        A = ceil(a * n)
        r = w_C(n, D, A, 1, [(n, 4)], (120, 240, 480, 960))
        js = [j for j in range(2, n // 8, max(2, n // 4000) & ~1) if max(4 * j + 5 * D, 2 * n + 1 + D, 11 * n // 4 - j) < r[0]]
        if js:
            print(f"   a = {a}: C = {r[0] / n:.5f} n; not cut by Lemma C (m <= 960) for j/n in [{js[0] / n:.4f}, {js[-1] / n:.4f}]")
        else:
            print(f"   a = {a}: C = {r[0] / n:.5f} n; cut for every j (smallest W(j) = {Wbest / n:.5f} n)")
        sys.stdout.flush()


def part5():
    c41 = import_module("41_counts")
    pairs_II = {1: (71, 3), 2: (71, 3), 3: (71, 3), 4: (74, 4), 5: (76, 5)}
    pairs_I = {1: (71, 3), 2: (74, 4), 3: (74, 4), 4: (76, 5), 5: (79, 6)}
    print("5. Theorem 8' of note 41 re-evaluated (certificate (18, 5), pairs of note 41), and the non-degenerate window")
    for a in (0.70, 0.703):
        for lg in (25, 26, 27, 28):
            n = 1 << lg
            D = n // 2 + 5
            A = ceil(a * n)
            Wmax = 18 * A - 1
            cert = c41.N(5, 18 * A, D) > n * c41.R(18, 5)
            okII = all(c41.lemmaC_uniform(n, D, A, b, m, B, Wmax) for b, (m, B) in pairs_II.items())
            okI = all(c41.caseI_all_profiles(n, D, A, b, m, B, Wmax) for b, (m, B) in pairs_I.items())
            Bjet = (18 * A - 1) // D
            per = (79 * A - 1) // D
            const = max((Bjet - t) ** 2 + per * t for t in range(Bjet + 1))
            _, _, lowN, lowB, lowT, r = ends(n, a, (120, 240, 480, 960))
            lo = max(lowN, lowB, lowT)
            # a b = 1 factor with contact 4 on all lines and W >= r[0] is cut with (m, B) = (r[1], r[2]): the left side of (2)
            # is nondecreasing in W, and the side condition of Lemma C is checked here at the largest W of a factor
            side = D * (r[1] + r[2]) <= r[1] * A - Wmax
            per_big = (r[1] * A - 1) // D
            const_big = max((Bjet - t) ** 2 + per_big * t for t in range(Bjet + 1))
            print(f"      Lemma C for contact 4 on all lines, b = 1: (m, B) = ({r[1]}, {r[2]}), side condition at W_max: {side}, "
                  f"per unit of degree {per_big}, constant if such factors occur {const_big}")
            print(f"   a = {a}, n = 2^{lg}: certificate {cert}, B_jet = {Bjet}, case II cut {okII}, case I cut {okI}, "
                  f"per unit {per}, constant {const}; non-degenerate window "
                  f"{'EMPTY (C = %.5f n <= T = %.5f n)' % (r[0] / n, lowT / n) if r[0] <= lo else '[%.5f, %.5f) n' % (lo / n, r[0] / n)}; "
                  f"queries {ceil(108 / -__import__('math').log2(A / n))}")
            sys.stdout.flush()


if __name__ == "__main__":
    which = sys.argv[1:] or ["1", "2", "3", "4", "5"]
    for w in which:
        {"1": part1, "2": part2, "3": part3, "4": part4, "5": part5}[w]()
