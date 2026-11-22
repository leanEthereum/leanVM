#!/usr/bin/env python3
"""Note 42 (referee of note 36): exact probabilities of the star events against Lemma B1 and against the
general sequential count (Lemma M of note 42), from the output of 42_toy.c (t = 3 members, f_1 = 0).

A pattern has n1 coordinates with g2(a) = 0, n2 with g3(a) = 0, n3 with g2(a) = g3(a), n4 with both zero.

Lemma B1 (note 36), with the exact factor corr = m^n / (m)_n of its proof in place of e^(n^2/(m-n)):
    Pr[E_T] <= E[number of (g2, g3) satisfying T] <= corr * q^(2k - W_D) * (h/m)^g,  W_D = n1 + n2 + 2 n4,  g = n3,
    and both are 0 when a member has at least k zeros (n1 + n4 >= k or n2 + n4 >= k).
The middle quantity, the expected number of bad configurations, is what the proof bounds; it is the one
compared here (Pr[E_T] is often exactly 0 where the bound is below 1, so it has no power).
Lemma M (note 42): every coordinate may be read as free (it gives a unit to each member that uses it) or as
a root (one factor h/m, and a unit to the members that come after the pair); the bound is
    corr * q^((k - c_2)_+ + (k - c_3)_+) * (h/m)^roots,
minimized here over all readings and both orders of the two members.

Usage: python3 42_toy_check.py file [file ...]
"""
import sys
from fractions import Fraction as Fr
from math import factorial


def lemma_m(p, k, n1, n2, n3, n4):
    """best exponent pair over the readings: returns the smallest bound (without corr) as a Fraction."""
    best = None
    h = Fr(k - 1, p)
    for a1, a2 in ((n1, n2), (n2, n1)):  # the two orders of the members
        for x1 in range(a1 + 1):          # free coordinates among those where member 2 vanishes
            for x2 in range(a2 + 1):      # free among those where member 3 vanishes
                for x3 in range(n3 + 1):  # coordinates g2 = g3 read as a unit of member 3
                    for y in range(n4 + 1):  # double zeros read as free (else: root of member 2, unit of 3)
                        c2 = x1 + y
                        c3 = x2 + x3 + n4
                        roots = (a1 - x1) + (a2 - x2) + (n3 - x3) + (n4 - y)
                        b = Fr(p) ** (max(k - c2, 0) + max(k - c3, 0)) * h ** roots
                        if best is None or b < best:
                            best = b
    return best


def main():
    for path in sys.argv[1:]:
        rows = []
        lists = []
        for line in open(path):
            if line.startswith("#"):
                hdr = dict(kv.split("=") for kv in line[1:].split() if "=" in kv and kv.split("=")[0] in ("p", "n", "k"))
                p, n, k = int(hdr["p"]), int(hdr["n"]), int(hdr["k"])
                print(line.strip()[2:])
            elif line.startswith("L"):
                lists.append(tuple(map(int, line.split()[1:])))
            else:
                rows.append(tuple(map(int, line.split())))
        corr = Fr(p ** n)
        for i in range(n):
            corr /= (p - i)
        viol_b1 = viol_m = 0
        npat = 0
        window = []
        by_w = {}
        for n1, n2, n3, n4, cnt, tot, pairs in rows:
            n0 = n - n1 - n2 - n3 - n4
            mult = factorial(n) // (factorial(n0) * factorial(n1) * factorial(n2) * factorial(n3) * factorial(n4))
            exists = Fr(cnt, tot)      # Pr[E_T]
            expect = Fr(pairs, tot)    # E[number of (g2, g3) satisfying the pattern]
            W, g = n1 + n2 + 2 * n4, n3
            b1 = corr * Fr(p) ** (2 * k - W) * Fr(k - 1, p) ** g
            if n1 + n4 >= k or n2 + n4 >= k:
                b1 = Fr(0)
            bm = corr * lemma_m(p, k, n1, n2, n3, n4)
            assert exists <= expect or expect == 0
            if expect > b1:
                viol_b1 += 1
            if expect > bm:
                viol_m += 1
            npat += mult
            if Fr(1, 100) <= b1 <= 100:
                window.append((float(expect / b1), (n1, n2, n3, n4), mult, float(expect), float(b1), float(bm), float(exists)))
            w = W + g
            e = by_w.setdefault(w, [Fr(0), Fr(0), Fr(0), Fr(0), 0])
            e[0] += mult * expect
            e[1] += mult * b1
            e[2] += mult * bm
            e[3] += mult * exists
            e[4] += mult
        print(f"  {len(rows)} count vectors, {npat} patterns; the expected number of configurations exceeds Lemma B1 in {viol_b1} and Lemma M in {viol_m}")
        nz = [r for r in window if r[0] > 0]
        print(f"  count vectors with a Lemma B1 prediction in [0.01, 100]: {len(window)}, of which {len(nz)} have a nonzero expectation")
        if nz:
            rs = sorted(r[0] for r in nz)
            print(f"  observed / predicted on those: min {rs[0]:.3f}, median {rs[len(rs)//2]:.3f}, max {rs[-1]:.3f}")
            nz.sort(reverse=True)
            for r, c, mult, expect, b1, bm, ex in (nz[:6] + nz[-3:] if len(nz) > 9 else nz):
                print(f"    (n1,n2,n3,n4)={c} x{mult}: expected configurations {expect:.4f}, Lemma B1 {b1:.4f}, Lemma M {bm:.4f}, Pr[E_T] {ex:.4f}")
        print("  by weight W_D + g, summed over patterns: expected configurations | Lemma B1 | Lemma M | sum of Pr[E_T] | patterns")
        for w in sorted(by_w):
            e = by_w[w]
            print(f"    weight {w}: {float(e[0]):.4f} | {float(e[1]):.4f} | {float(e[2]):.4f} | {float(e[3]):.4f} | {e[4]}")
        # the tilted sum identity of Theorem B at t = 3, checked on two tilts
        for x, y in ((Fr(1, 3), Fr(1, 5)), (Fr(1, 7), Fr(2, 3))):
            lhs = Fr(0)
            for n1, n2, n3, n4, cnt, tot, pairs in rows:
                n0 = n - n1 - n2 - n3 - n4
                mult = factorial(n) // (factorial(n0) * factorial(n1) * factorial(n2) * factorial(n3) * factorial(n4))
                lhs += mult * x ** (n1 + n2 + 2 * n4) * y ** n3
            assert lhs == ((1 + x) ** 2 + y) ** n
        print("  tilted sum over all labelings equals ((1+x)^2 + y)^n: checked exactly for two tilts")
        if lists:
            print("  largest list over all words, by agreement A (exhaustive over words): A, largest list, number of point tuples")
            for A, L, c in lists:
                print(f"    A={A} largest list {L}: {c}")


if __name__ == "__main__":
    main()
