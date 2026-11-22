#!/usr/bin/env python3
"""The residual window of 40-rate-half-residual.md (n = 2^25, rate 1/2, D = n/2 + 5).

For an absolutely irreducible first integral with Y1-degree b whose leading coefficient involves Y0, with
contact order o on x*n lines and none elsewhere, the tests are:
  floor      W >= (b + 2) D (Lemma L of note 35) and W >= (o / 2) D (Lemma M of note 40: j <= delta);
  lower (S)  W >= max(o/2, o - b) * (A - (n - x n)) + b D, otherwise every list member is a Y0-root of the
             leading coefficient (Lemma N of note 40; for o = 4 this is Section 4.3 of note 41);
  lower (B)  b = 1 only: x n (o^2 - o - 1) <= W (W - D) / D (Bezout, Lemma B of note 40);
  upper (C)  W_C = the smallest W for which Lemma C of note 35 applies with some (m, B) of the grid
             m in {10, 12, 16, 20, 24, 30, 40, 60, 80, 120, 240, 480}, B <= m/2 (exact integers), next to the leading-order value
             min over beta of [obar (1 - beta/2) - b J(beta)/beta] / (a/rho - beta/2).
Part 1: uniform profiles, exact integers.  Part 2: b = 1, profiles with contact 4 on x4 n lines and contact 2
on x2 n lines, at leading order.  Part 3: the explicit family W = 11n/4 - 2 of note 40, Section 5.
Run: python3 40_window.py [1] [2] [3]       (part 1 takes about 2 minutes)
"""
import sys
from math import ceil, sqrt
from importlib import import_module

lib = import_module("40_lib")
Rloc, Ncoef = lib.Rloc, lib.Ncoef

_R = {}


def R(m, B):
    key = (m, B)
    if key not in _R:
        _R[key] = Rloc(m, B)
    return _R[key]


def w_C(n, D, A, b, profile, ms):
    """smallest W (integer) such that (2) holds for some (m, B) with (R1); None if never."""
    best = None
    for m in ms:
        Z = m * A
        for B in range(b, m // 2 + 1):
            cost = sum(cnt * (R(m, B) - R(m - o, B - b)) for cnt, o in profile)
            NB = Ncoef(B, Z, D)
            if NB <= cost:
                continue
            lo, hi = 0, Z
            while lo < hi:
                mid = (lo + hi) // 2
                if NB - Ncoef(B - b, Z - mid, D) > cost:
                    hi = mid
                else:
                    lo = mid + 1
            W = lo
            if D * (m + B) <= Z - W and (best is None or W < best[0]):
                best = (W, m, B)
    return best


def leading_wC(a, rho, b, obar):
    best = None
    cap = min(0.5, a / rho - 1)
    for i in range(1, 4000):
        beta = i / 4000 * cap
        J = 0.5 * (a * a / rho - 1) + (1 - a) * beta - (2 - rho) / 2 * beta * beta
        w = (obar * (1 - beta / 2) - b * J / beta) / (a / rho - beta / 2)
        if best is None or w < best[0]:
            best = (w, beta)
    return best


def bezout_low(sum_term, D):
    """smallest W with W (W - D) / D >= sum_term."""
    return (D + sqrt(D * D + 4 * D * sum_term)) / 2


def part1():
    n = 1 << 25
    D = n // 2 + 5
    rho = 0.5
    ms = (10, 12, 16, 20, 24, 30, 40, 60, 80, 120, 240, 480)
    for a in (0.6919, 0.70):
        A = ceil(a * n)
        print(f"1. uniform profiles, exact integers, a = {a}: all W in units of n")
        print("   b  o   x     floor   lower(S)  lower(B)  upper(C) [m,B]     leading upper   status")
        for b in (1, 2, 3):
            for o in (2, 4, 6, 8):
                for x in (0.5, 0.75, 0.9, 0.95, 1.0):
                    npr = int(x * n)
                    prof = [(npr, o), (n - npr, 0)]
                    r = w_C(n, D, A, b, prof, ms)
                    floor = max((b + 2) * D, (o // 2) * D)
                    lowS = max(o // 2, o - b) * max(A - (n - npr), 0) + b * D
                    lowB = bezout_low(npr * (o * o - o - 1), D) if b == 1 else 0
                    lo = max(floor, lowS, lowB)
                    lead = leading_wC(a, rho, b, o * x)
                    if r is None:
                        print(f"   {b}  {o}  {x:<4}  none")
                        continue
                    status = f"OPEN  width {(r[0] - lo) / n:.4f}" if r[0] > lo else "closed"
                    print(f"   {b}  {o}  {x:<4}  {floor / n:.4f}  {lowS / n:.4f}    {lowB / n:.4f}    "
                          f"{r[0] / n:.4f} [{r[1]},{r[2]}]   {lead[0]:.4f}   {status}")
        sys.stdout.flush()


def part2():
    rho = 0.5
    print("2. b = 1, contact 4 on x4 n lines, contact 2 on x2 n lines, none elsewhere (leading order)")
    for a in (0.6919, 0.70):
        print(f"   a = {a}: rows x4, columns x2 = 0, 0.05, ..., 1 - x4; entry = width of the open window in units"
              f" of n ('.' = closed)")
        opened = 0
        for i4 in range(0, 21):
            x4 = i4 / 20
            row = []
            for i2 in range(0, 21 - i4):
                x2 = i2 / 20
                obar = 4 * x4 + 2 * x2
                if obar == 0:
                    row.append("  .  ")
                    continue
                wc = leading_wC(a, rho, 1, obar)[0]
                # refined Sudan: the A lines of smallest contact; values (o - 1)_+ = 0, 1, 3
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
                lo = max(1.5, lowS, lowB)
                if wc > lo:
                    opened += 1
                    row.append(f"{wc - lo:5.3f}")
                else:
                    row.append("  .  ")
            print(f"   x4 = {x4:4.2f}: " + " ".join(row))
        print(f"   open cells: {opened}")


def part3():
    n = 1 << 25
    D = n // 2 + 5
    Wf = 11 * n // 4 - 2
    print("3. the family of Section 5 (contact 4 on all lines, b = 1, W = 11n/4 - 2), n = 2^25")
    for a in (0.6905, 0.691, 0.6919, 0.6949, 0.70):
        A = ceil(a * n)
        r = w_C(n, D, A, 1, [(n, 4)], (240, 480, 960))
        lead = leading_wC(a, 0.5, 1, 4.0)[0]
        verdict = "cut by Lemma C" if Wf >= r[0] else "not cut for m in {240, 480, 960}"
        print(f"   a = {a}: W_C = {r[0] / n:.5f} n at (m, B) = ({r[1]}, {r[2]}), leading order {lead:.4f}; "
              f"W = {Wf / n:.5f} n: {verdict}; automatic section above agreement {Wf / 4 / n:.4f} n; "
              f"root of E_Y above {(Wf - D) / 3 / n:.4f} n")
    a = 0.6905
    A = ceil(a * n)
    row = []
    for m in (20, 30, 40, 60, 90, 120, 180, 240, 360, 480, 720, 960, 1440):
        r = w_C(n, D, A, 1, [(n, 4)], (m,))
        row.append(f"{m}: {'none' if r is None else format(r[0] / n, '.5f')}")
    print(f"   a = {a}, W_C / n by multiplicity m (the family has W / n = {Wf / n:.5f}): " + ", ".join(row))


if __name__ == "__main__":
    which = sys.argv[1:] or ["1", "2", "3"]
    for w in which:
        {"1": part1, "2": part2, "3": part3}[w]()
