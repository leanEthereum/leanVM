#!/usr/bin/env python3
"""Referee 41: independent re-derivation of the numbers of 35-large-characteristic-transfer.md.
Exact integer arithmetic except part A (floating point, with the exact cases flagged).

  A  a_1(rho): closed form against a direct maximisation of the asymptotic margin; query counts.
  B  the certificate (m, B) = (18, 5) at n = 2^25, rate 1/2; B_jet; smallest agreement it covers.
  C  convexity of j -> R(m - 2j, B') (needed to reduce every contact profile to the uniform one).
  D  UNIFORM form of the rate 1/2 conditional statement: every first-integral factor with total contact
     <= 2n of an (18, 5) explainer is cut by Lemma C with one explicit (m, B) per b = 1..5.
  E  falsification test: Lemmas C, A+ and L4 against the flat cubic (which has n - 1 list members).
  F  toy certificates (n = 16, 32, 64) for the field experiments of 41_theory.c.
  G  e*, the windows of Section 4.1, the flat cubic window.
  H  Proposition 6 with exact integers for EVERY contact profile (rate 1/2, n = 2^25).
  I  the uniform checks at the certificates (37, 11) and (100, 28).
  J  the region left open (case II, singular contact), with exact integers.
  K  the uniform checks at n = 2^26, 2^27, 2^28.
Run: python3 41_counts.py [A] [B] [C] [D] [E] [F] [G] [H] [I] [J] [K]   (about 2 minutes in total)
"""
import sys
from fractions import Fraction
from math import sqrt, log2, ceil, isqrt


def R_sum(m, B):
    if m <= 0 or B < 0:
        return 0
    return sum((s + 1) * (B + 1) - max(2 * s - m + 1, 0) * max(s + B - m + 1, 0) for s in range(m))


def R(m, B):
    """closed form of R_sum (checked against it in part C): with t = m - 1 - s the product is (m - 1 - 2t)(B - t)."""
    if m <= 0 or B < 0:
        return 0
    T = min((m - 2) // 2, B - 1)
    tot = (B + 1) * m * (m + 1) // 2
    if T >= 0:
        tot -= (T + 1) * (m - 1) * B - (m - 1 + 2 * B) * T * (T + 1) // 2 + T * (T + 1) * (2 * T + 1) // 3
    return tot


def N_loop(B, Z, D):
    if Z <= 0 or B < 0:
        return 0
    tot, t = 0, 0
    while D * t < Z:
        tot += (min(t, B) + 1) * (Z - D * t)
        t += 1
    return tot


def N(B, Z, D):
    """closed form of N_loop (checked against it in part C)."""
    if Z <= 0 or B < 0:
        return 0
    tmax = (Z - 1) // D
    T1 = min(B, tmax)
    # sum_{t=0}^{T1} (t+1)(Z - D t)
    s0 = (T1 + 1) * (T1 + 2) // 2                     # sum (t+1)
    s1 = T1 * (T1 + 1) * (2 * T1 + 1) // 6 + T1 * (T1 + 1) // 2   # sum t(t+1)
    tot = Z * s0 - D * s1
    if tmax > B:
        cnt = tmax - B
        st = (B + 1 + tmax) * cnt // 2                # sum_{t=B+1}^{tmax} t
        tot += (B + 1) * (Z * cnt - D * st)
    return tot


def Ndelta(delta, Z, kappa):
    if Z <= 0:
        return 0
    tot, t = 0, 0
    while kappa * t < Z:
        tot += min(t + 1, delta) * (Z - kappa * t)
        t += 1
    return tot


# ---------------------------------------------------------------- A
def margin_asym(a, rho, beta):
    """lim (N - n R) / (n m^3), exact piecewise formula for every beta in (0, 1] (my derivation)."""
    th = a / rho
    if beta <= th:
        Nn = beta * a * a / (2 * rho) - a * beta * beta / 2 + rho * beta ** 3 / 6
    else:
        Nn = a ** 3 / (6 * rho * rho)
    if beta <= 0.5:
        Rr = beta / 2 - beta * beta / 2 + beta ** 3 / 3
    else:
        Rr = beta / 4 + 1 / 24
    return Nn - Rr


def a1_numeric(rho):
    lo, hi = rho, sqrt(rho)
    for _ in range(60):
        a = (lo + hi) / 2
        best = max(margin_asym(a, rho, i / 4000) for i in range(1, 4001))
        if best > 0:
            hi = a
        else:
            lo = a
    return hi


def a1_closed(rho):
    rc = 11 - 3 * sqrt(13)
    if rho >= rc:
        return (3 * rho + 2 * sqrt(rho * (5 - rho) * (2 - rho))) / (8 - rho)
    s = sqrt(rho / 2)
    lo, hi = 0.0, 1.0
    for _ in range(100):
        u = (lo + hi) / 2
        if u * u * (u + 3) < s:
            lo = u
        else:
            hi = u
    return s * (1 + lo)


def queries_strict(num, den_is_exact_power=None):
    return None


def part_A():
    print("A. a_1(rho): closed form vs direct maximisation of the margin over beta in (0, 1]")
    for r in (1, 2, 3, 4):
        rho = 2.0 ** -r
        c, d = a1_closed(rho), a1_numeric(rho)
        print(f"   rate 1/{2**r}: closed {c:.6f}  numeric {d:.6f}  Johnson {sqrt(rho):.6f}  diff {abs(c-d):.1e}")
    print("   queries t = ceil(108 / log2(n/A)):")
    for a in (0.70, 0.6999, 0.692, 0.6899):
        print(f"     a = {a}: {108 / log2(1 / a):.3f} -> {ceil(108 / log2(1 / a))}")
    print("   at the Johnson radius itself 108/log2(1/sqrt(rho)) is the integer 216, 108, 72, 54;")
    print("   strictly above it the counts are 217, 109, 73, 55 (note 35's table has 217, 108, 73, 54:")
    print("   a floating point artefact, sqrt(1/2) and sqrt(1/8) round up, sqrt(1/4), sqrt(1/16) do not).")
    for r in (1, 2, 3, 4):
        rho = 2.0 ** -r
        print(f"     rate 1/{2**r}: at a_1: {ceil(108 / log2(1 / a1_closed(rho)))}")


# ---------------------------------------------------------------- B
def part_B():
    print("B. the certificate at n = 2^25, rate 1/2, Delta = k + 5")
    n = 1 << 25
    D = n // 2 + 5
    print(f"   R(18, 5) = {R(18, 5)}")
    for A in (ceil(0.70 * n), ceil(0.6999 * n), 7 * n // 10):
        Nc = N(5, 18 * A, D)
        print(f"   A = {A} ({A/n:.6f} n): N = {Nc}, n R = {n * R(18, 5)}, margin {Nc - n * R(18, 5)} "
              f"({'certificate' if Nc > n * R(18, 5) else 'NO certificate'}), B_jet = {(18 * A - 1) // D}")
    lo, hi = n // 2, n
    while lo < hi:
        mid = (lo + hi) // 2
        if N(5, 18 * mid, D) > n * R(18, 5):
            hi = mid
        else:
            lo = mid + 1
    print(f"   smallest A covered by (18, 5): {lo} = {lo / n:.6f} n")
    # is (18,5) the smallest multiplicity at 0.70?
    A = ceil(0.70 * n)
    small = [(m, B) for m in range(1, 19) for B in range(0, m + 1) if N(B, m * A, D) > n * R(m, B)]
    print(f"   certificates with m <= 18 at A = ceil(0.70 n): {small}")
    A = ceil(0.6949 * n)
    small = [(m, B) for m in range(1, 38) for B in range(0, m + 1) if N(B, m * A, D) > n * R(m, B)]
    print(f"   certificates with m <= 37 at A = ceil(0.6949 n): {small}, B_jet = {(37 * A - 1) // D}")


# ---------------------------------------------------------------- C
def part_C():
    import random
    rnd = random.Random(41)
    for _ in range(20000):
        B, Z, D = rnd.randrange(0, 40), rnd.randrange(-5, 3000), rnd.randrange(1, 90)
        assert N(B, Z, D) == N_loop(B, Z, D), (B, Z, D)
    for mm in range(0, 121):
        for BB in range(0, 131):
            assert R(mm, BB) == R_sum(mm, BB), (mm, BB)
    print("C. closed forms of N and R agree with the defining sums (20000 random (B, Z, Delta); all m <= 120, B <= 130)")
    print("   convexity of f(j) = R(m - 2j, B') in j >= 0 (second differences), all m <= 520, B' <= m")
    bad = 0
    worst = None
    for m in range(1, 521):
        for B in range(0, m + 1):
            f = [R(m - 2 * j, B) for j in range(0, m // 2 + 3)]
            for j in range(len(f) - 2):
                dd = f[j] - 2 * f[j + 1] + f[j + 2]
                if dd < 0:
                    bad += 1
                    if worst is None:
                        worst = (m, B, j, dd)
    print(f"   violations: {bad}" + (f", first at (m, B', j, second difference) = {worst}" if worst else ""))
    bad = 0
    for m in range(1, 301):
        for B in range(0, m + 1):
            if R(m, B) < R(m - 1, B) or (B and R(m, B) < R(m, B - 1)):
                bad += 1
    print(f"   monotonicity of R in m and in B: {bad} violations")
    # the pairs used in part D
    for (m, B) in PAIRS_D.values():
        for b in range(1, 6):
            f = [R(m - 2 * j, B - b) for j in range(0, m // 2 + 3)]
            assert all(f[j] - 2 * f[j + 1] + f[j + 2] >= 0 for j in range(len(f) - 2)), (m, B, b)
    print("   convex for every (m, B - b) used in part D")


# ---------------------------------------------------------------- D
PAIRS_D = {}


def lemmaC_uniform(n, D, A, b, m, B, Wmax):
    """True if, for EVERY first integral with Y1-degree b, weighted degree <= Wmax and total contact
    sum o_alpha <= 2n, inequality (2) of Lemma C and its side condition hold with this (m, B).
    Reduction (referee report, section 4): by convexity of j -> R(m - 2j, B - b) the right side of (2) is
    largest for contact 2 on x n lines (x <= 1) and 0 elsewhere; W is at least
      case II (leading coefficient involves Y0):  (b + 2) D            (Lemma L3), any x,
      case I  (leading coefficient in F[X]):      x n + b D            (Lemma L3),
    the left side is increasing and concave in W and the right side is linear in x, so it is enough to
    test x = 1 in case II and x = 0, 1 in case I."""
    Z = m * A
    if B < b or not D * (m + B) <= Z - Wmax:
        return False
    full = N(B, Z, D)
    r0 = R(m, B) - R(m, B - b)          # per line with contact 0
    r2 = R(m, B) - R(m - 2, B - b)      # per line with contact 2
    # case II, x = 1
    if not full - N(B - b, Z - (b + 2) * D, D) > n * r2:
        return False
    # case I, x = 0 and x = 1
    if not full - N(B - b, Z - b * D, D) > n * r0:
        return False
    if not full - N(B - b, Z - (n + b * D), D) > n * r2:
        return False
    return True


def part_D():
    print("D. uniform Lemma C at n = 2^25, rate 1/2, Delta = k + 5, explainer (18, 5)")
    n = 1 << 25
    D = n // 2 + 5
    for a in (0.70, 0.6999):
        A = ceil(a * n)
        Wmax = 18 * A - 1
        Bjet = (18 * A - 1) // D
        print(f"   a = {a}: A = {A}, B_jet = {Bjet}, factors have b <= 5, W <= {Wmax}")
        worst_m = 0
        for b in range(1, 6):
            found = None
            for m in range(20, 601):
                for B in range(b, m // 2 + 1):
                    if lemmaC_uniform(n, D, A, b, m, B, Wmax):
                        found = (m, B)
                        break
                if found:
                    break
            if found is None:
                print(f"     b = {b}: NO (m, B) with m <= 600")
                worst_m = None
                break
            PAIRS_D[(a, b)] = found
            worst_m = max(worst_m, found[0])
            print(f"     b = {b}: smallest multiplicity m = {found[0]} (B = {found[1]}), "
                  f"bound per unit of degree floor((mA-1)/Delta) = {(found[0] * A - 1) // D}")
        if worst_m:
            per = (worst_m * A - 1) // D
            total = Bjet * Bjet + Bjet * per
            print(f"     list bound B_jet^2 + B_jet * {per} = {total} = 2^{log2(total):.2f}")
            print(f"     (note 35's looser accounting B_jet^2 + B_jet * 2*600*A/Delta = "
                  f"{Bjet*Bjet + Bjet * ((2 * 600 * A) // D)} = 2^{log2(Bjet*Bjet + Bjet * ((2 * 600 * A) // D)):.2f})")
    # the case that stays open: contact 4 everywhere, case II
    A = ceil(0.70 * n)
    print("   for comparison, contact 4 on all lines, case II, W = (b+2) Delta, m <= 600:")
    for b in (1, 2, 3):
        ok = None
        W = (b + 2) * D
        for m in (150, 300, 600):
            for B in range(b, m // 2 + 1):
                if D * (m + B) <= m * A - W and N(B, m * A, D) - N(B - b, m * A - W, D) > n * (R(m, B) - R(m - 4, B - b)):
                    ok = (m, B)
                    break
            if ok:
                break
        print(f"     b = {b}: {'cut with ' + str(ok) if ok else 'not cut (open, as note 35 says)'}")


# ---------------------------------------------------------------- E
def part_E():
    print("E. flat cubic (rate 1/4, delta = 3, b = 1, W = 3k - 2, contact 2 on n - 1 lines, n - 1 members)")
    print("   a lemma whose hypothesis holds must give a bound >= n - 1; a violation would refute the lemma")
    for Nn in range(4, 11):
        n = 1 << Nn
        k = n // 4
        D = k - 1
        W = 3 * k - 2
        viol = 0
        tested = 0
        applicable = 0
        firstapp = None
        As = sorted(set([3 * n // 8 + 1, 13 * n // 32, 7 * n // 16, 15 * n // 32, n // 2 - 2, n // 2 - 1]) & set(range(3 * n // 8 + 1, n // 2))) if n > 64 else list(range(3 * n // 8 + 1, n // 2))
        for A in As:
            # Lemma C
            mmax = min(160, 4 * n)
            for m in range(1, mmax + 1):
                Z = m * A
                bound = 3 * ((Z - 1) // D)
                for B in range(1, m + 1):
                    if not D * (m + B) <= Z - W:
                        continue
                    tested += 1
                    lhs = N(B, Z, D) - N(B - 1, Z - W, D)
                    rhs = (n - 1) * (R(m, B) - R(m - 2, B - 1)) + (R(m, B) - R(m, B - 1))
                    if lhs > rhs:
                        applicable += 1
                        if firstapp is None or m < firstapp[1]:
                            firstapp = (A, m, B, bound)
                        if bound < n - 1:
                            viol += 1
        print(f"   n = {n:5d}: Lemma C tested {tested} (A, m, B); hypothesis holds {applicable} times"
              f"{' (smallest m: A=%d m=%d B=%d bound=%d)' % firstapp if firstapp else ''}; violations {viol}")
        # Lemma A+ : n1 = n - 1 contained lines of order exactly 1
        viol = app = 0
        kappa = D // 2
        if kappa >= 1:
            for A in As:
                for mu in range(1, min(400, 4 * n) + 1):
                    Z = mu * A
                    r = (Z - 1) // kappa
                    if r < 3 + mu:
                        continue
                    if Ndelta(3, Z, kappa) > n * 3 * mu * (mu + 1) // 2 + (n - 1) * mu * (r + 1 - 3):
                        app += 1
                        if 3 * r < n - 1:
                            viol += 1
        # Lemma L4 (Sudan step): A - (n - n') > W - b D
        l4 = sum(1 for A in range(3 * n // 8 + 1, n // 2) if A - 1 > W - D)
        print(f"              Lemma A+ hypothesis holds {app} times, violations {viol}; Sudan step applies for {l4} values of A")


# ---------------------------------------------------------------- F
def part_F():
    print("F. toy certificates: smallest support with N(B, mA) > n R(m, B)")
    cases = [(16, 3, 7), (16, 3, 8), (16, 7, 10), (16, 7, 11), (16, 8, 10), (16, 8, 11), (16, 1, 5), (16, 2, 7),
             (32, 7, 15), (32, 7, 16), (32, 15, 22), (32, 15, 20), (32, 1, 5), (32, 1, 6), (32, 3, 9), (32, 3, 10),
             (64, 3, 12), (64, 3, 13), (64, 1, 7), (64, 1, 8), (64, 15, 31)]
    for (n, D, A) in cases:
        best = None
        for m in range(1, 41):
            for B in range(0, m + 1):
                Nc = N(B, m * A, D)
                if Nc > n * R(m, B):
                    if best is None or Nc < best[0]:
                        best = (Nc, m, B)
        j = "below Johnson" if A * A <= n * D else "above Johnson"
        if best:
            print(f"   n = {n}, Delta = {D}, A = {A} ({j}): (m, B) = ({best[1]}, {best[2]}), "
                  f"{best[0]} unknowns, n R = {n * R(best[1], best[2])}, B_jet = {(best[1] * A - 1) // D}")
        else:
            print(f"   n = {n}, Delta = {D}, A = {A} ({j}): none with m <= 40")


# ---------------------------------------------------------------- G
def estar(rho, a):
    """largest beta <= 1/2 with J(beta) >= 0, and e*(beta) = rho (1 - beta/2) / (a - rho beta/2)."""
    disc = (1 - a) ** 2 + (2 - rho) * (a * a / rho - 1)
    if disc < 0:
        return None
    beta = min(0.5, ((1 - a) + sqrt(disc)) / (2 - rho))
    return beta, rho * (1 - beta / 2) / (a - rho * beta / 2)


def part_G():
    print("G. e* (largest beta <= 1/2 with J >= 0)")
    for rho, a in ((0.5, 0.692), (0.5, 0.70), (0.25, 0.48), (0.5, a1_closed(0.5) + 1e-9), (0.25, a1_closed(0.25) + 1e-9),
                   (0.125, a1_closed(0.125) + 1e-9), (0.0625, a1_closed(0.0625) + 1e-9)):
        b, e = estar(rho, a)
        print(f"   rho = {rho}, a = {a:.4f}: beta = {b:.4f}, e* = {e:.4f}, (1 + rho)/2 = {(1 + rho) / 2:.4f}, "
              f"smooth economical components need b < 2 e*/rho - 2 = {2 * e / rho - 2:.2f}; (b+2) Delta / e* at b = 1: {3 * rho / e:.3f} n")
    print("   flat cubic window at n = 2^20, rate 1/4, a = 0.4999 (b = 1, contact 2 on n - 1 lines):")
    n = 1 << 20
    k = n // 4
    D = k - 1
    A = int(0.4999 * n)
    best = None
    for m in (40, 80, 160, 320):
        Z = m * A
        for B in range(1, m // 2 + 1):
            cost = (n - 1) * (R(m, B) - R(m - 2, B - 1)) + (R(m, B) - R(m, B - 1))
            if N(B, Z, D) <= cost:
                continue
            lo, hi = 0, Z
            while lo < hi:
                mid = (lo + hi) // 2
                if N(B, Z, D) - N(B - 1, Z - mid, D) > cost:
                    hi = mid
                else:
                    lo = mid + 1
            if D * (m + B) <= Z - lo and (best is None or lo < best[0]):
                best = (lo, m, B)
    print(f"     Lemma C applies only for W >= {best[0] / n:.4f} n (m = {best[1]}, B = {best[2]}); the cubic has W = {(3 * k - 2) / n:.4f} n: not cut")


# ---------------------------------------------------------------- H
def gen_rank(mu, mp, Bp):
    """rank of the rectangle {Taylor degree < mp, Y1-degree <= Bp} in F[..]/c_mu, mp <= mu (same proof as R)."""
    if mu <= 0 or mp <= 0 or Bp < 0:
        return 0
    return sum((s + 1) * (Bp + 1) - max(2 * s - mu + 1, 0) * max(s + Bp - mu + 1, 0) for s in range(min(mp, mu)))


def part_H():
    print("H. Proposition 6 uniformly at n = 2^25, rate 1/2 (case I: leading Y1-coefficient in F[X]), every contact profile")
    print("   reduction: (2) holds for every profile iff it holds at the vertices of the convex hull of the points")
    print("   (max(j, 2j - b), R(m,B) - R(m - 2j, B - b)), j = 0, 1, ..., cut at the largest possible weighted degree")
    n = 1 << 25
    D = n // 2 + 5
    A = ceil(0.70 * n)
    Wmax = 18 * A - 1
    for b in range(1, 6):
        found = None
        for m in range(60, 601):
            Z = m * A
            for B in range(b, m // 2 + 1):
                if not D * (m + B) <= Z - Wmax:
                    break
                full = N(B, Z, D)
                smax = Fraction(Wmax - b * D, n)       # mean of phi over the lines is at most smax
                pts = []
                j = 0
                while True:   # beyond 2j >= m the second coordinate is constant, so later points add nothing
                    phi = max(j, 2 * j - b)
                    pts.append((Fraction(phi), R(m, B) - R(m - 2 * j, B - b)))
                    if phi > smax and 2 * j > m + 2:
                        break
                    j += 1
                # vertices to test: all points with phi <= smax, and on the line s = smax the chord between
                # the last admissible point and each later point (upper envelope at s = smax)
                ok = True
                tests = [(s, t) for (s, t) in pts if s <= smax]
                inside = [(s, t) for (s, t) in pts if s <= smax]
                outside = [(s, t) for (s, t) in pts if s > smax]
                for (s1, t1) in inside:
                    for (s2, t2) in outside:
                        lam = (smax - s1) / (s2 - s1)
                        tests.append((smax, t1 + lam * (t2 - t1)))
                for (s, t) in tests:
                    W = b * D + int(s * n)
                    if not full - N(B - b, Z - W, D) > t * n:
                        ok = False
                        break
                if ok:
                    found = (m, B, len(tests))
                    break
            if found:
                break
        if found:
            print(f"   b = {b}: every profile is cut with (m, B) = ({found[0]}, {found[1]}) ({found[2]} vertices tested), "
                  f"bound per unit of degree {(found[0] * A - 1) // D}")
        else:
            print(f"   b = {b}: no (m, B) with m <= 600 cuts every profile")


# ---------------------------------------------------------------- I
def part_I():
    print("I. the same uniform checks at the other rate 1/2 certificates of note 35 (n = 2^25, Delta = k + 5)")
    print("   per b: smallest m <= 1200 cutting (i) every case II factor with total contact <= 2n, (ii) every case I factor")
    n = 1 << 25
    D = n // 2 + 5
    for a, m0, B0 in ((0.6949, 37, 11), (0.6919, 100, 28)):
        A = ceil(a * n)
        assert N(B0, m0 * A, D) > n * R(m0, B0)
        Wmax = m0 * A - 1
        Bjet = (m0 * A - 1) // D
        worst = 0
        fail = False
        for b in range(1, B0 + 1):
            found = None
            mlo = (Wmax + D * b) // (A - D)      # the side condition needs m (A - Delta) >= Wmax + Delta B
            for m in range(mlo, 1201):
                Z = m * A
                for B in range(b, m // 2 + 1):
                    if not D * (m + B) <= Z - Wmax:
                        break
                    if not lemmaC_uniform(n, D, A, b, m, B, Wmax):
                        continue
                    # case I, all profiles (hull vertices, as in part H)
                    full = N(B, Z, D)
                    smax = Fraction(Wmax - b * D, n)
                    pts, j = [], 0
                    while True:
                        phi = max(j, 2 * j - b)
                        pts.append((Fraction(phi), R(m, B) - R(m - 2 * j, B - b)))
                        if phi > smax and 2 * j > m + 2:
                            break
                        j += 1
                    inside = [(s, t) for (s, t) in pts if s <= smax]
                    outside = [(s, t) for (s, t) in pts if s > smax]
                    tests = list(inside)
                    for (s1, t1) in inside:
                        for (s2, t2) in outside[:3]:
                            lam = (smax - s1) / (s2 - s1)
                            tests.append((smax, t1 + lam * (t2 - t1)))
                    if all(full - N(B - b, Z - (b * D + int(s * n)), D) > t * n for (s, t) in tests):
                        found = (m, B)
                        break
                if found:
                    break
            if not found:
                print(f"   a = {a}, certificate ({m0}, {B0}): b = {b}: nothing with m <= 1200")
                fail = True
                break
            worst = max(worst, found[0])
        if not fail:
            per = (worst * A - 1) // D
            tot = max(Bjet * Bjet, Bjet * per)
            print(f"   a = {a}, certificate ({m0}, {B0}), B_jet = {Bjet}: every b <= {B0} is cut with m <= {worst}; "
                  f"list bound max(B_jet^2, B_jet * {per}) = {tot} = 2^{log2(tot):.2f}; queries {ceil(108 / log2(n / A))}")


# ---------------------------------------------------------------- J
def part_J():
    print("J. the open region at n = 2^25, rate 1/2, a = 0.70, certificate (18, 5): case II factors (W >= (b+2) Delta)")
    print("   profile: contact 4 on x n lines and contact 2 on the others (for a given total contact this is the")
    print("   profile hardest to cut, by concavity). Smallest x for which NO (m, B), m <= 600, satisfies (2):")
    n = 1 << 25
    D = n // 2 + 5
    A = ceil(0.70 * n)
    Wmax = 18 * A - 1
    grid = [m for m in range(64, 200, 3)] + [m for m in range(200, 601, 20)]
    for b in range(1, 6):
        W = (b + 2) * D
        best_x = Fraction(0)      # largest x that is still cut by some (m, B)
        arg = None
        for m in grid:
            Z = m * A
            for B in range(b, m // 2 + 1):
                if not D * (m + B) <= Z - Wmax:
                    break
                lhs = N(B, Z, D) - N(B - b, Z - W, D)
                p2 = R(m, B) - R(m - 2, B - b)
                p4 = R(m, B) - R(m - 4, B - b)
                # cut iff lhs > n (p2 + x (p4 - p2))
                if lhs <= n * p2:
                    continue
                x = Fraction(lhs - n * p2, n * (p4 - p2))
                if x > best_x:
                    best_x, arg = x, (m, B)
        xs = float(min(best_x, 1))
        print(f"     b = {b}: cut for x < {xs:.4f} (best (m, B) = {arg}); an uncut factor needs total contact >= {2 + 2 * xs:.3f} n"
              f" and weighted degree >= {(b + 2) * 0.5:.1f} n, so efficiency W / contact can be as large as {(b + 2) * 0.5 / (2 + 2 * xs):.3f} only if W is at its minimum")
    print("   the same with W as a free parameter: for contact 4 on all lines, the smallest W/n at which (2) holds (factor is cut):")
    for b in range(1, 6):
        best = None
        for m in grid:
            Z = m * A
            for B in range(b, m // 2 + 1):
                if not D * (m + B) <= Z - Wmax:
                    break
                cost = n * (R(m, B) - R(m - 4, B - b))
                if N(B, Z, D) <= cost:
                    continue
                lo, hi = 0, Wmax
                if not N(B, Z, D) - N(B - b, Z - hi, D) > cost:
                    continue
                while lo < hi:
                    mid = (lo + hi) // 2
                    if N(B, Z, D) - N(B - b, Z - mid, D) > cost:
                        hi = mid
                    else:
                        lo = mid + 1
                if best is None or lo < best[0]:
                    best = (lo, m, B)
        lower = (3 * A + D) / n if b == 1 else (b + 2) * D / n   # b = 1: refined Sudan step (report, 4.3); else Lemma L3
        up = best[0] / n
        tag = f"open window W in [{lower:.3f}, {up:.3f}) n" if lower < up else f"no window (lower bound {lower:.3f} n): always cut"
        print(f"     b = {b}: cut as soon as W >= {up:.4f} n, i.e. efficiency >= {best[0] / (4 * n):.4f} (leading order e* = 0.6717); {tag}")


# ---------------------------------------------------------------- K
def caseI_all_profiles(n, D, A, b, m, B, Wmax):
    """Lemma U (b): True if (2) and the side condition hold for every case I factor, whatever its profile."""
    Z = m * A
    if B < b or not D * (m + B) <= Z - Wmax:
        return False
    full = N(B, Z, D)
    smax = Fraction(Wmax - b * D, n)
    pts, j = [], 0
    while True:
        phi = max(j, 2 * j - b)
        pts.append((Fraction(phi), R(m, B) - R(m - 2 * j, B - b)))
        if phi > smax and 2 * j > m + 2:
            break
        j += 1
    inside = [(s, t) for (s, t) in pts if s <= smax]
    outside = [(s, t) for (s, t) in pts if s > smax]
    tests = list(inside)
    for (s1, t1) in inside:
        for (s2, t2) in outside:
            lam = (smax - s1) / (s2 - s1)
            tests.append((smax, t1 + lam * (t2 - t1)))
    return all(full - N(B - b, Z - (b * D + int(s * n)), D) > t * n for (s, t) in tests)


def part_K():
    print("K. the other sizes of the brief: rate 1/2, a = 0.70, Delta = k + 5, certificate (18, 5), with the pairs of parts D and H")
    pairs_II = {1: (71, 3), 2: (71, 3), 3: (71, 3), 4: (74, 4), 5: (76, 5)}
    pairs_I = {1: (71, 3), 2: (74, 4), 3: (74, 4), 4: (76, 5), 5: (79, 6)}
    for lg in (25, 26, 27, 28):
        n = 1 << lg
        D = n // 2 + 5
        A = ceil(0.70 * n)
        Wmax = 18 * A - 1
        cert = N(5, 18 * A, D) > n * R(18, 5)
        okII = all(lemmaC_uniform(n, D, A, b, m, B, Wmax) for b, (m, B) in pairs_II.items())
        okI = all(caseI_all_profiles(n, D, A, b, m, B, Wmax) for b, (m, B) in pairs_I.items())
        Bjet = (18 * A - 1) // D
        per = (79 * A - 1) // D
        print(f"   n = 2^{lg}: certificate {cert}, B_jet = {Bjet}, case II (contact <= 2n) cut: {okII}, case I (all profiles) cut: {okI}, "
              f"bound {max(Bjet * Bjet, Bjet * per)}")


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "D", "C", "E", "F", "G", "H", "I", "J", "K"]
    if "C" in which and "D" not in which:
        which = ["D"] + which
    for w in which:
        {"A": part_A, "B": part_B, "C": part_C, "D": part_D, "E": part_E, "F": part_F, "G": part_G, "H": part_H, "I": part_I, "J": part_J, "K": part_K}[w]()
