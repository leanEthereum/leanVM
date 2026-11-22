#!/usr/bin/env python3
"""50_window.py: exact integers for 50-residual-b-at-least-2.md (rate 1/2, Delta = n/2 + 5, n = 2^25 unless said otherwise).

The counting functions R(m, B), N(B, Z) and inequality (2) of Lemma C are those of notes 35 and 41 (imported from 41_counts.py,
whose closed forms are checked against the defining sums there).  New here: the lower bounds of note 50,
  (L1_d)  W >= (b + d) Delta + sum_alpha eps_d(j_alpha),          eps_d(j) = max(j - d/2, 2j - b - d, 0),   d = deg_Y0 of the leading
          coefficient (even, >= 2 in case II),                                                                         [Theorem 3.1]
  (L2_d)  W >= b Delta + sum_alpha eps_d(j_alpha) + sum_{alpha in S} (max(j_alpha, 2 j_alpha - b) - eps_d(j_alpha)),   [Theorem 3.3]
  (J)     W >= Delta + sum_{alpha in S} (2 j_alpha - 1)_+ ,                                                            [Theorem 3.4]
where S is the agreement set of a list member (the worst case is the A lines of smallest contact), (L2) holding for all members
but at most d and (J) for all but at most delta (delta - 1).

Parts:
  1  certificates (m, B) with B <= 6 at a = 0.70, 0.703, 0.705: which Y1-degrees can a fixed component have.
  2  two-level profiles (contact 2j on x n lines, contact 2j' on the others, j' = 0 or 1): per b and j the cut W_C of Lemma C
     (exact, smallest W_0 such that every W in [W_0, W_max] is cut by some (m, B) of the grid, side condition included),
     the lower bounds, and the status, for every admissible d; a = 0.70 and a = 0.703.
  3  Theorem 4.1 (all profiles with contact orders <= 4, b = 2..5): the three vertices of Lemma U (b) of note 41 with phi(j) = (j-1)_+.
  4  the same test with phi(j) = (j-1)_+ and contact orders <= 2 jmax: the largest jmax for which (L1) alone closes every profile.
  5  the tie (b, contact) = (2, 6): leading-order discriminant and the exact thresholds as a function of a and of m.
  6  the smallest agreement with a certificate of Y1-degree B = 1..6; b = 2 with contact orders <= 6 and at most x6 n lines of contact 6.
Run: python3 50_window.py [1] [2] [3] [4] [5] [6] [0.70] [0.703] [0.705]      (about 1 minute; the agreements select tables of part 2)
"""
import sys
from math import ceil, log2
from fractions import Fraction
from importlib import import_module

c41 = import_module("41_counts")
R, N = c41.R, c41.N

MS = (12, 16, 20, 24, 30, 36, 44, 52, 60, 71, 80, 100, 120, 160, 240, 320, 480, 640, 960)
_Rc = {}


def Rm(m, B):
    key = (m, B)
    v = _Rc.get(key)
    if v is None:
        v = _Rc[key] = R(m, B)
    return v


def cut_intervals(n, D, A, b, profile, Wmax, ms=MS):
    """profile: list of (count, j).  For each (m, B) of the grid the interval of W on which Lemma C applies:
    [smallest W with (2), min(mA - D(m + B), Wmax)].  Returns the list of (lo, hi, m, B)."""
    out = []
    for m in ms:
        Z = m * A
        for B in range(b, m // 2 + 1):
            hi = min(Z - D * (m + B), Wmax)
            if hi <= 0:
                break
            cost = sum(cnt * (Rm(m, B) - Rm(m - 2 * j, B - b)) for cnt, j in profile)
            NB = N(B, Z, D)
            if NB - N(B - b, Z - hi, D) <= cost:
                continue
            lo, h2 = 0, hi
            while lo < h2:
                mid = (lo + h2) // 2
                if NB - N(B - b, Z - mid, D) > cost:
                    h2 = mid
                else:
                    lo = mid + 1
            out.append((lo, hi, m, B))
    return out


def w_cut(n, D, A, b, profile, Wmax, ms=MS):
    """smallest W_0 such that every integer W in [W_0, Wmax] lies in one of the intervals; None if Wmax itself is not cut."""
    iv = cut_intervals(n, D, A, b, profile, Wmax, ms)
    cur = Wmax + 1
    best = None
    changed = True
    while changed:
        changed = False
        for (lo, hi, m, B) in iv:
            if hi >= cur - 1 and lo < cur:
                cur = lo
                best = (m, B)
                changed = True
    return (cur, best) if cur <= Wmax else (None, None)


def eps(d, b, j):
    return max(j - d // 2, 2 * j - b - d, 0)


def lower_bounds(n, D, A, b, d, profile):
    """profile: list of (count, j).  Returns (L1, L2, J) for the worst agreement set (the A lines of smallest contact)."""
    L1 = (b + d) * D + sum(cnt * eps(d, b, j) for cnt, j in profile)
    rest = A
    L2 = b * D + sum(cnt * eps(d, b, j) for cnt, j in profile)
    J = D
    for cnt, j in sorted(profile, key=lambda t: t[1]):
        take = min(cnt, rest)
        rest -= take
        L2 += take * (max(j, 2 * j - b) - eps(d, b, j))
        J += take * max(2 * j - 1, 0)
    return L1, L2, J


# ---------------------------------------------------------------- 1
def part1():
    print("1. certificates (m, B): N(B, mA) > n R(m, B); a fixed component of the explainer spaces has Y1-degree <= the smallest B")
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        D = n // 2 + 5
        for a in ("0.70", "0.703", "0.705"):
            A = ceil(Fraction(a) * n)
            row = []
            for B in range(1, 7):
                ms = [m for m in range(1, 400) if N(B, m * A, D) > n * R(m, B)]
                if ms:
                    m0 = ms[0]
                    row.append(f"B={B}: m={ms[0]}..{ms[-1]} (B_jet({m0})={(m0 * A - 1) // D}, W<{m0}A={m0 * A / n:.2f}n)")
                else:
                    row.append(f"B={B}: none")
            print(f"   n = 2^{lg}, a = {a}: " + "; ".join(row))
    print("   queries ceil(108 / log2(n/A)): " + ", ".join(f"a = {a}: {ceil(108 / log2(1 / a))}" for a in (0.70, 0.703, 0.705, 0.7071)))


# ---------------------------------------------------------------- 2
def bezout_b2(n, D, d2, profile):
    """(B2) of Theorem 3.6 (b = 2, primitive parts of G_1 and G_2 coprime): the smallest W allowed, minimised over d1 = deg_Y0 G_1:
       (d1 + d2) W >= D (2 d1 + d2 + d1 d2) + sum_alpha [min(mu1, d1) min(mu2, d2) + d1 (mu2 - d2)_+ + d2 (mu1 - d1)_+],
       W >= (1 + d1) D + sum_alpha (mu1 - d1)_+,     mu1 = (2j - 1)_+,  mu2 = max(j, 2j - 2)."""
    best = None
    for d1 in range(0, 60):
        lhs = 0
        c1 = 0
        for cnt, j in profile:
            if j == 0:
                continue
            mu1, mu2 = 2 * j - 1, max(j, 2 * j - 2)
            lhs += cnt * (min(mu1, d1) * min(mu2, d2) + d1 * max(mu2 - d2, 0) + d2 * max(mu1 - d1, 0))
            c1 += cnt * max(mu1 - d1, 0)
        W = max(-(-(D * (2 * d1 + d2 + d1 * d2) + lhs) // (d1 + d2)), (1 + d1) * D + c1)
        if best is None or W < best:
            best = W
    return best


CONF = {"0.70": (18, 5, "(18, 5), W < 18A; b = 5 is excluded by the certificate (21, 4)"),
        "0.703": (14, 3, "(14, 3), W < 14A"),
        "0.705": (12, 2, "(12, 3) for W < 12A and (14, 2) for b <= 2")}


def part2(args):
    n = 1 << 25
    D = n // 2 + 5
    alist = [a for a in CONF if a in args] or list(CONF)
    for a in alist:
        A = ceil(Fraction(a) * n)
        m0, bmax, cert = CONF[a]
        Wmax = m0 * A - 1
        print(f"2. two-level profiles, a = {a}, A = {A}, certificates {cert}, W_max = {Wmax / n:.3f} n; all W in units of n")
        print("   columns: b, contact 2j on x n lines, contact 2j' on the others; W_C = cut of Lemma C (every W in [W_C, W_max] is cut);")
        print("   L = min over d of max(L1_d, L2_d, J) with the d that realise it; LB = the same with (B2) added (b = 2, non-degenerate)")
        summary = {}
        for b in range(2, bmax + 1):
            for j in range(2, 14):
                if (b + 2) * D > Wmax:
                    break
                for jr in sorted({0, 1, j - 1}):
                    for x in (("0.5", "0.75", "0.85", "0.9", "0.95", "0.98", "1") if jr <= 1 else ("0.1", "0.3", "0.5", "0.7", "0.9")):
                        if x == "1" and jr >= 1:
                            continue
                        n1 = int(Fraction(x) * n)
                        prof = [(n1, j), (n - n1, jr)]
                        rows = []
                        d = 2
                        while (b + d) * D <= Wmax:
                            L1, L2, J = lower_bounds(n, D, A, b, d, prof)
                            lo = max(L1, L2, J)
                            lob = max(lo, bezout_b2(n, D, d, prof)) if b == 2 else lo
                            rows.append((d, lo, lob))
                            d += 2
                        if not rows or min(r[1] for r in rows) > Wmax:
                            continue          # no such component inside the budget
                        wc, arg = w_cut(n, D, A, b, prof, Wmax)
                        L = min(r[1] for r in rows)
                        LB = min(r[2] for r in rows)
                        if wc is None:
                            status = "NOT CUT at W_max"
                            wcs = "none"
                            key = "open"
                        else:
                            wcs = f"{wc / n:.4f} [{arg[0]},{arg[1]}]"
                            if L >= wc:
                                status, key = "closed", "closed"
                            elif LB >= wc:
                                status, key = "closed if non-degenerate (B2); else OPEN " + f"[{L / n:.4f}, {wc / n:.4f}) for d in {[r[0] for r in rows if r[1] < wc]}", "nd"
                            else:
                                status = f"OPEN [{LB / n:.4f}, {wc / n:.4f}) width {(wc - LB) / n:.4f}, d in {[r[0] for r in rows if r[2] < wc]}"
                                if b == 2:
                                    status += f"; degenerate from {L / n:.4f}"
                                key = "open"
                        summary.setdefault((b, 2 * j), []).append(key)
                        print(f"   {b}  {2*j:<2}  {x:<4}  {2*jr:<2}  W_C {wcs:<19} L {L / n:.4f}  LB {LB / n:.4f}  {status}")
                    sys.stdout.flush()
        print(f"   summary a = {a} (rows closed / closed if non-degenerate / open) per (b, top contact):")
        for (b, o), ks in sorted(summary.items()):
            print(f"     b = {b}, contact {o}: {ks.count('closed')} / {ks.count('nd')} / {ks.count('open')}")


# ---------------------------------------------------------------- 3, 4
def lemmaU_L1(n, D, A, b, m, B, Wmax, jmax):
    """True if (2) and the side condition hold with this (m, B) for every first integral with Y1-degree b, leading
    coefficient involving Y0, weighted degree in [(b+2)D + sum (j_alpha - 1)_+, Wmax] and all j_alpha <= jmax.
    Lemma U (b) of note 41 with phi(j) = (j - 1)_+: the mean of (phi, psi) over the lines lies in the convex hull of the points
    (phi(j), psi(j)), j = 0..jmax, whose upper vertices are j = 1, ..., jmax (psi is concave and nondecreasing in j, phi is
    linear for j >= 1 and phi(0) = phi(1), psi(0) <= psi(1)); the set {(s, t): n t < Phi~((b+2)D + n s)} is convex."""
    Z = m * A
    if B < b or not D * (m + B) <= Z - Wmax:
        return False
    full = N(B, Z, D)
    for j in range(1, jmax + 1):
        W = (b + 2) * D + n * (j - 1)
        if W > Wmax:
            # chord between the last inside vertex and this one, at s_max
            smax = Fraction(Wmax - (b + 2) * D, n)
            t0 = R(m, B) - R(m - 2 * (j - 1), B - b)
            t1 = R(m, B) - R(m - 2 * j, B - b)
            lam = smax - (j - 2)
            t = t0 + lam * (t1 - t0)
            return full - N(B - b, Z - Wmax, D) > n * t
        if not full - N(B - b, Z - W, D) > n * (R(m, B) - R(m - 2 * j, B - b)):
            return False
    return True


def part3():
    print("3. Theorem 4.1: every first-integral component with b >= 2, leading coefficient involving Y0 and all contact orders <= 4")
    print("   is cut by Lemma C: one (m, B) per b such that (2) holds at the vertices j = 1 (W = (b+2) Delta) and j = 2 (W = (b+2) Delta + n)")
    for a, m0, bmax in (("0.70", 18, 5), ("0.703", 18, 5), ("0.703", 14, 3)):
        for lg in (25, 26, 27, 28):
            n = 1 << lg
            D = n // 2 + 5
            A = ceil(Fraction(a) * n)
            Wmax = m0 * A - 1
            res = []
            for b in range(1, bmax + 1):
                found = None
                for m in range(20, 400):
                    for B in range(b, m // 2 + 1):
                        if not D * (m + B) <= m * A - Wmax:
                            break
                        if lemmaU_L1(n, D, A, b, m, B, Wmax, 2):
                            found = (m, B)
                            break
                    if found:
                        break
                res.append(f"b={b}: {found if found else 'NO (m <= 399)'}" + (f" bound/deg {(found[0] * A - 1) // D}" if found else ""))
            print(f"   a = {a}, n = 2^{lg}, W_max = {m0}A - 1: " + "; ".join(res))


def part4():
    print("4. with (L1) alone, the largest jmax such that every profile with all contact orders <= 2 jmax is cut (one (m, B), m <= 399)")
    n = 1 << 25
    D = n // 2 + 5
    for a, m0, bmax in (("0.70", 18, 5), ("0.703", 14, 3), ("0.705", 14, 2)):
        A = ceil(Fraction(a) * n)
        Wmax = m0 * A - 1
        for b in range(2, bmax + 1):
            best = None
            for jmax in range(2, 14):
                found = None
                for m in range(20, 400):
                    for B in range(b, m // 2 + 1):
                        if not D * (m + B) <= m * A - Wmax:
                            break
                        if lemmaU_L1(n, D, A, b, m, B, Wmax, jmax):
                            found = (m, B)
                            break
                    if found:
                        break
                if not found:
                    break
                best = (jmax, found)
            print(f"   a = {a}, W_max = {m0}A - 1, b = {b}: " + (f"closed for all contact orders <= {2 * best[0]} with (m, B) = {best[1]}" if best else "not even jmax = 2"))


# ---------------------------------------------------------------- 5
def part5():
    print("5. the tie (b, contact) = (2, 6) on all lines: lower bound (J) = Delta + 5A against the cut of Lemma C")
    print("   leading order: (J) meets the cut iff 100 a^4 - 89 a^2 - 2a + 21 = (10a - 7)(10a^3 + 7a^2 - 4a - 3) = 0, i.e. a = 7/10 exactly")
    n = 1 << 25
    D = n // 2 + 5
    for a in ("0.70", "0.7005", "0.701", "0.702", "0.703"):
        A = ceil(Fraction(a) * n)
        Wmax = 18 * A - 1
        prof = [(n, 3)]
        row = []
        for m in (60, 120, 240, 480, 960, 1920):
            iv = cut_intervals(n, D, A, 2, prof, Wmax, (m,))
            lo = min((t[0] for t in iv if t[1] >= 5 * n), default=None)
            row.append(f"m={m}: {lo / n:.5f}" if lo else f"m={m}: none")
        LJ = D + 5 * A
        L1 = 8 * D
        print(f"   a = {a}: (J) = {LJ / n:.5f} n, (L1, d = 6) = {L1 / n:.5f} n; cut from: " + ", ".join(row))


# ---------------------------------------------------------------- 6
def part6():
    print("6. smallest agreement with a certificate of Y1-degree B (n = 2^25, any m <= 400), and b = 2 with contact orders <= 6")
    n = 1 << 25
    D = n // 2 + 5
    for B in range(1, 7):
        lo, hi = n // 2, 23726566          # hi = floor(n / sqrt 2)
        if not any(N(B, m * hi, D) > n * R(m, B) for m in range(1, 401)):
            print(f"   B = {B}: no certificate with m <= 400 up to A = {hi} = {hi / n:.5f} n (just below the Johnson radius)")
            continue
        while lo < hi:
            mid = (lo + hi) // 2
            if any(N(B, m * mid, D) > n * R(m, B) for m in range(1, 401)):
                hi = mid
            else:
                lo = mid + 1
        ms = [m for m in range(1, 401) if N(B, m * lo, D) > n * R(m, B)]
        print(f"   B = {B}: certificates exist from A = {lo} = {lo / n:.5f} n on (there with m = {ms[0]}); queries {ceil(108 / log2(n / lo))}")
    print("   b = 2, all contact orders <= 6, at most x6 n lines of contact 6 (a = 0.70, W_max = 18A - 1): Lemma U with phi = (j-1)_+,")
    print("   vertices: uniform j = 1, 2 and x6 [j = 3] + (1 - x6) [j' = 0, 1, 2]")
    A = ceil(Fraction("0.70") * n)
    Wmax = 18 * A - 1
    b = 2
    for x6 in ("0.9", "0.95", "0.98", "0.99", "0.995", "0.999", "1"):
        x = Fraction(x6)
        found = None
        for m in (74, 100, 160, 240, 480, 960, 1920, 3840, 7680):
            Z = m * A
            for B in range(b, m // 2 + 1):
                if not D * (m + B) <= Z - Wmax:
                    break
                full = N(B, Z, D)
                psi = [R(m, B) - R(m - 2 * j, B - b) for j in range(4)]
                ok = True
                tests = [(Fraction(0), Fraction(psi[1])), (Fraction(1), Fraction(psi[2]))]
                for jp in (0, 1, 2):
                    tests.append((2 * x + (1 - x) * max(jp - 1, 0), x * psi[3] + (1 - x) * psi[jp]))
                for (sv, tv) in tests:
                    W = (b + 2) * D + int(sv * n)
                    if not full - N(B - b, Z - W, D) > tv * n:
                        ok = False
                        break
                if ok:
                    found = (m, B)
                    break
            if found:
                break
        print(f"     x6 = {x6}: " + (f"closed with (m, B) = {found}, bound per unit of degree {(found[0] * A - 1) // D}" if found else "no (m, B) with m <= 7680"))


if __name__ == "__main__":
    which = [w for w in sys.argv[1:] if w in "123456"] or ["1", "3", "4", "5", "6", "2"]
    rest = [w for w in sys.argv[1:] if w not in "123456"]
    for w in which:
        if w == "2":
            part2(rest)
        else:
            {"1": part1, "3": part3, "4": part4, "5": part5, "6": part6}[w]()
