#!/usr/bin/env python3
"""55_window.py: exact integers for the referee report on note 53, Theorem 6.2 (Johnson step, constants 42 and 19).
Own code, exact rational arithmetic.

The hard core is contact 4 on all lines and W below the first cut. Two cuts are used:
  (a) the note's hypothesis W < 2.6352 n (53_window.py takes W_cut = floor(2.6352 n));
  (b) the exact first cut of note 54 (54_results.txt, "first cut at W = ... by (960, 121)"), quoted, not recomputed:
      88424204, 176848364, 353696684, 707393312 at n = 2^25..2^28 (2.63525 n).
For each: s = (largest W) - Delta - 3A, A' = A - s, the smallest distance 2(A - Delta) - 2s, and the Johnson bound
M <= floor(w n / (w n - 2 A'(n - A'))) for several w.
Run: python3 55_window.py
"""
from fractions import Fraction as Fr

CUT54 = {25: 88424204, 26: 176848364, 27: 353696684, 28: 707393312}


def johnson(n, Ap, w):
    """largest M allowed by C(M,2) w <= M^2 Ap (n - Ap) / n, or None if void (w n <= 2 Ap (n - Ap))."""
    den = w * n - 2 * Ap * (n - Ap)
    if den <= 0:
        return None
    return int(Fr(w * n, den))


def johnson_frac(n, Ap, wnum, wden):
    den = Fr(wnum * n, wden) * n - 2 * Ap * (n - Ap)
    if den <= 0:
        return None
    return int(Fr(wnum * n, wden) * n / den)


def main():
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        Delta = n // 2 + 5
        A = -(-7065 * n // 10000)
        print(f"n = 2^{lg}: A = {A}, Delta = {Delta}, Delta + 3A = {Delta + 3 * A} ({(Delta + 3 * A) / n:.5f} n), "
              f"4A = {4 * A}")
        for (name, Wmax) in (("note 53: W < 2.6352 n", (26352 * n - 1) // 10000), ("note 54: W < first cut", CUT54[lg] - 1)):
            s = Wmax - Delta - 3 * A
            Ap = A - s
            dmin = 2 * (A - Delta) - 2 * s
            row = [f"7n/16: {johnson(n, Ap, 7 * n // 16)}", f"n/2: {johnson(n, Ap, n // 2)}",
                   f"55n/128: {johnson(n, Ap, 55 * n // 128)}", f"27n/64: {johnson(n, Ap, 27 * n // 64)}",
                   f"13n/32: {johnson(n, Ap, 13 * n // 32)}"]
            print(f"   {name}: W <= {Wmax} ({Wmax / n:.5f} n), W < 4A: {Wmax < 4 * A}; s <= {s} ({s / n:.5f} n); "
                  f"A' = A - s = {Ap} ({Ap / n:.5f} n) > n/2: {2 * Ap > n}; A' > Delta: {Ap > Delta}")
            print(f"      distances >= 2(A - Delta) - 2s = {dmin} ({dmin / n:.5f} n) > 3n/8: {8 * dmin > 3 * n}; "
                  f"2A'(n - A')/n = {2 * Ap * (n - Ap) / n / n:.5f} n; Johnson with w_1 = " + ", ".join(row))
        clean = [f"7n/16: {johnson(n, A, 7 * n // 16)}", f"n/2: {johnson(n, A, n // 2)}",
                 f"55n/128: {johnson(n, A, 55 * n // 128)}", f"27n/64: {johnson(n, A, 27 * n // 64)}",
                 f"13n/32: {johnson(n, A, 13 * n // 32)}"]
        print(f"   r_P constant (s = 0): distances >= 2(A - Delta) = {2 * (A - Delta) / n:.5f} n; 2A(n - A)/n = "
              f"{2 * A * (n - A) / n / n:.5f} n; Johnson with w_1 = " + ", ".join(clean))
        print(f"      width of the interval [2(A - Delta), 2A(n - A)/n): {(2 * A * (n - A) / n - 2 * (A - Delta)) / n:.5f} n")
    n = 1 << 25
    Delta = n // 2 + 5
    print("thresholds of Theorem S, clean bound with w_1 = 7n/16 (remark (ii) of note 53: 24, 21, 20, 19):")
    for a6 in (700840, 703000, 705000, 706500):
        A = -(-a6 * n // 10 ** 6)
        print(f"   a = {a6 / 1e6}: 2(A - Delta) > 3n/8: {8 * 2 * (A - Delta) > 3 * n}; M <= {johnson(n, A, 7 * n // 16)}")
    print("toy analogue at n = 32, Delta = 16 (sets of size p, distances >= 2(p - 16), next weight of RM(2, 5)):")
    wts = [8, 12, 16]          # the weights of RM(2, 5) up to n/2 (n/2 - n/2^(h+1) needs h <= 2 in five variables)
    for p in (20, 21, 22, 23, 24):
        d = 2 * (p - 16)
        w1 = min(w for w in wts if w >= d)
        print(f"   p = {p}: distances >= {d}, w_1 = {w1}, Johnson: {johnson(32, p, w1)}")
    print("rate 1/16 remark of note 53 (Section 7): sets of size exactly A, w_1 = 3n/8")
    A = -(-237478 * n // 10 ** 6)
    den = Fr(3 * n, 8) - Fr(2 * A * (n - A), n)
    print(f"   2A(n - A)/n = {2 * A * (n - A) / n / n:.5f} n < 3n/8: {den > 0}; bound {int(Fr(3 * n, 8) / den)}; "
          f"for sets of size a'n the step needs 2a'(1 - a') < 3/8, that is a' < 1/4: void from agreement n/4 on")


if __name__ == "__main__":
    main()
