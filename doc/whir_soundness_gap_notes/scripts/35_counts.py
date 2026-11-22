#!/usr/bin/env python3
"""Counting tables for 35-large-characteristic-transfer.md (exact integer arithmetic, no field needed).

  A  the first-order curve a_1(rho) of [DKT26, (31)] and the query counts it would give;
  B  finite interpolation certificates N_coef > n * R_loc at our sizes (valid in every characteristic);
  C  Lemma A / A+ thresholds: which components are harmless by degree and number of contained lines;
  D  Lemma C window: for a first integral with Y1-degree b containing x*n lines (simple contact),
     the largest weighted degree w_up*n for which the counting does NOT produce a cutting explainer,
     against the Sudan lower end w_lo = a - 1 + x + rho*b. A dangerous component needs w_lo <= w <= w_up.
  E  rate 1/2: exact check of Lemma C on components with a Y0-free leading coefficient, and the open cases.
Run: python3 35_counts.py [A] [B] [C] [D] [E]   (about 2 minutes in total)
"""
import sys
from math import sqrt, ceil, log2


def a1(rho):
    rc = 11 - 3 * sqrt(13)
    if rho >= rc:
        return (3 * rho + 2 * sqrt(rho * (5 - rho) * (2 - rho))) / (8 - rho)
    lo, hi = 0.0, 1.0
    for _ in range(200):
        u = (lo + hi) / 2
        if u * u * (u + 3) < sqrt(rho / 2):
            lo = u
        else:
            hi = u
    return sqrt(rho / 2) * (1 + lo)


def Rloc(m, B):
    """[DKT26, (24)]: exact local rank of the multiplicity-m first-order contact conditions on the
    full rectangle with Y1-degree <= B (checked over F2, F3 and a large prime in 35_checks.py A)."""
    if m <= 0 or B < 0:
        return 0
    return sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))


def Ncoef(B, Z, D):
    """number of monomials X^x Y0^a Y1^c with c <= B and x + D(a+c) < Z."""
    if Z <= 0 or B < 0:
        return 0
    tot, t = 0, 0
    while D * t < Z:
        tot += (min(t, B) + 1) * (Z - D * t)
        t += 1
    return tot


def part_A():
    print("A. first-order curve and query counts for 108 bits (t = ceil(108 / log2(1/a)))")
    print("   rate   Johnson  a_1      queries Johnson -> a_1")
    for R in range(1, 8):
        rho = 2.0 ** -R
        j, a = sqrt(rho), a1(rho)
        print(f"   1/{2**R:<4} {j:.4f}   {a:.4f}   {ceil(108 / log2(1 / j))} -> {ceil(108 / log2(1 / a))}")


def part_B():
    print("B. finite certificates: smallest multiplicity m <= 400 with N_coef(B, mA) > n R_loc(m, B)")
    print("   (degree bound D = k + 5, covering degree <= k - 1 + 6; n = 2^25)")
    n = 1 << 25
    for R in (1, 2, 3, 4):
        k = n >> R
        D = k + 5
        rho = 2.0 ** -R
        for eps in (0.002, 0.005, 0.01):
            a = a1(rho) + eps
            A = ceil(a * n)
            best = None
            for m in list(range(2, 60)) + list(range(60, 401, 10)):
                for B in range(1, m + 1):
                    if Ncoef(B, m * A, D) > n * Rloc(m, B):
                        best = (m, B)
                        break
                if best:
                    break
            if best:
                m, B = best
                bj = (m * A - 1) // D
                print(f"   rate 1/{2**R} a = a_1 + {eps} = {a:.4f} (Johnson {sqrt(rho):.4f}): m = {m}, B_d = {B}, "
                      f"B_jet = {bj}, margin {(Ncoef(B, m*A, D) - n*Rloc(m, B)) / (n * m**3):.2e} n m^3")
            else:
                print(f"   rate 1/{2**R} a = a_1 + {eps}: none with m <= 400")


def part_C():
    print("C. Lemma A (drop contained lines): harmless if (a - x)^2 > (rho/2)(1 - x), any degree;")
    print("   Lemma A+ (keep them): harmless if delta (a^2 - rho/2) > 2 a x.  x = fraction of lines contained")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        a = a1(rho) + 0.005
        # x_A: root of (a-x)^2 = (rho/2)(1-x)
        bq = -(2 * a - rho / 2)
        cq = a * a - rho / 2
        xA = (-bq - sqrt(bq * bq - 4 * cq)) / 2
        d_all = int(2 * a / (a * a - rho / 2)) + 1
        row = ", ".join(f"deg {d}: x < {min(1.0, max(xA, d * (a*a - rho/2) / (2*a))):.3f}" for d in range(2, d_all))
        print(f"   rate 1/{2**R}, a = {a:.4f}: x_A = {xA:.3f}; {row}; degree >= {d_all}: always harmless")


def w_up(n, k, a, b, x, ms=(40, 80, 160)):
    """smallest W (in units of n) for which Lemma C applies to some (m, B): simple contact (order 2) on
    x*n lines, order 0 elsewhere. Returns that W/n; a component with W above it is cut."""
    D = k - 1
    A = int(a * n)
    best = None
    for m in ms:
        Z = m * A
        for B in range(b, m // 2 + 1):
            cost = int(x * n) * (Rloc(m, B) - Rloc(m - 2, B - b)) + (n - int(x * n)) * (Rloc(m, B) - Rloc(m, B - b))
            # smallest W with Ncoef(B,Z) - Ncoef(B-b, Z-W) > cost : bisection (monotone in W)
            lo, hi = 0, Z
            if Ncoef(B, Z, D) - 0 <= cost:
                continue
            while lo < hi:
                mid = (lo + hi) // 2
                if Ncoef(B, Z, D) - Ncoef(B - b, Z - mid, D) > cost:
                    hi = mid
                else:
                    lo = mid + 1
            W = lo
            if D * (m - 3 + B - b) < Z - W:  # condition (R1)
                if best is None or W < best[0]:
                    best = (W, m, B)
    return None if best is None else (best[0] / n, best[1], best[2])


def part_D():
    print("D. Lemma C window for components with simple contact (n = 2^20; w in units of n)")
    n = 1 << 20
    for R in (1, 2):
        rho = 2.0 ** -R
        k = n >> R
        for a in (a1(rho) + 0.003, sqrt(rho) - 0.005):
            if R == 2 and a > 0.4999:
                a = 0.4999
            print(f"   rate 1/{2**R}, a = {a:.4f}")
            for b in (1, 2, 3):
                cells = []
                for x in (0.3, 0.5, 0.6, 0.8, 1.0):
                    r = w_up(n, k, a, b, x)
                    wlo = a - 1 + x + rho * b
                    if r is None:
                        cells.append(f"x={x}: none")
                    else:
                        tag = "OPEN" if r[0] > wlo else "closed"
                        cells.append(f"x={x}: [{wlo:.3f}, {r[0]:.3f}) {tag}")
                print(f"     b = {b}: " + "; ".join(cells))
    rho, k, a = 0.25, n >> 2, 0.4999
    print("   flat cubic (rate 1/4, x = 1, b = 1): w = 0.75, window", w_up(n, k, a, 1, 1.0)[0], ">= 0.75 >=", a - 1 + 1 + rho)


def lemmaC_ok(n, D, A, b, W, profile, ms):
    """profile: list of (number of lines, contact order). True if Lemma C applies for some (m, B)."""
    for m in ms:
        Z = m * A
        for B in range(max(b, 1), m // 2 + 1):
            if not D * (m + B) <= Z - W:   # (R1), with room for every contact order
                continue
            cost = sum(cnt * (Rloc(m, B) - Rloc(m - o, B - b)) for cnt, o in profile)
            if Ncoef(B, Z, D) - Ncoef(B - b, Z - W, D) > cost:
                return (m, B)
    return None


def part_E():
    print("E. rate 1/2: components whose leading Y1-coefficient is free of Y0 (n = 2^25, D = k + 5)")
    print("   uniform contact order 2j on x*n lines, W at its lower bound max(j, 2j-b)*x*n + b*D; OK = cut by Lemma C")
    n = 1 << 25
    k = n // 2
    D = k + 5
    for a in (0.695, 0.70):
        A = ceil(a * n)
        bad = []
        tot = 0
        for j in (1, 2, 3, 4, 6):
            for b in (1, 2, 3, 4, 6, 8):
                for x in (0.05, 0.25, 0.5, 0.75, 1.0):
                    npr = int(x * n)
                    W = max(j, 2 * j - b) * npr + b * D
                    r = lemmaC_ok(n, D, A, b, W, [(npr, 2 * j), (n - npr, 0)], (150, 300, 600))
                    tot += 1
                    if r is None:
                        bad.append((j, b, x))
        print(f"   a = {a}: {tot - len(bad)} of {tot} profiles cut; not cut: {bad}")
    print("   the same with a leading coefficient that involves Y0 (W at its lower bound (b+2)*D), a = 0.70:")
    A = ceil(0.70 * n)
    for j in (1, 2, 3):
        for b in (1, 2, 3):
            row = []
            for x in (0.25, 0.5, 0.75, 1.0):
                npr = int(x * n)
                W = (b + 2) * D
                r = lemmaC_ok(n, D, A, b, W, [(npr, 2 * j), (n - npr, 0)], (150, 300, 600))
                row.append(f"x={x}: {'cut' if r else 'OPEN'}")
            print(f"     contact {2*j}, b = {b}: " + ", ".join(row))


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C", "D", "E"]
    for w in which:
        {"A": part_A, "B": part_B, "C": part_C, "D": part_D, "E": part_E}[w]()
