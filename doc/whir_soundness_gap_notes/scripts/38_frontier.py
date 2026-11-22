"""Note 38: list lower bounds, attack requirements and the attack frontier of Protocol D.
Exact integer arithmetic for the counts, lgamma for the binomials of the pigeonhole lists.
Level 0 of the mu = 30 ladder: kappa = 24, ell = 6, n = 2^(24+R) at rate 2^-R, |K| = 2^64, q = |E| = 2^128."""
import math
from fractions import Fraction as Fr

LQ, LK, KAPPA, ELL = 128, 64, 24, 6
lg = lambda x: math.log2(x)


def gb(n, k):
    """Gaussian binomial [n choose k]_2"""
    if k < 0 or k > n:
        return 0
    num = den = 1
    for i in range(k):
        num *= 2 ** (n - i) - 1
        den *= 2 ** (i + 1) - 1
    return num // den


def Q2(m):
    return (2**m - 1) * (2**m - 2) * (2 ** (m + 1) - 8) // 6 + 2 ** (m + 1) - 2


def qc(c, m):
    """lower bound on |Q_c(X)|, dim X = m (Theorem 3.1 of the note)"""
    if c == 1:
        return 2 ** (m + 1) - 2
    return Q2(m - c + 2) ** (2 ** (c - 2))


def lchoose(n, t):
    return (math.lgamma(n + 1) - math.lgamma(t + 1) - math.lgamma(n - t + 1)) / math.log(2)


def pigeon(n, k, ell, T):
    """log2 of the average number of polynomials of degree <= k-1+ell over K within agreement exactly T"""
    return lchoose(n, T) - LK * (T - (k - 1 + ell) - 1)


def lists(R, N, kappa=KAPPA, quoted=False):
    """(tau, log2 L, label) for the explicit families at rate 2^-R on a subspace domain of dimension N"""
    n, k, rho = 2**N, 2 ** (N - R), Fr(1, 2**R)
    out = []
    if R >= 2:
        out.append((2 * rho, lg(2 ** (R - 1) * gb(N, R - 1)), "flats"))
        for u in range(1, R - 1):
            c = R - u - 1
            v = lg(2**c * gb(N, c)) - LK * u
            if v > 0:
                out.append((2 ** (u + 1) * rho, v, f"subspace pigeonhole u={u}"))
        v = lg(2 ** (R - 1) * gb(N, R - 1)) - LK
        if v > 0:
            out.append((rho * (Fr(5, 2) - rho), v, "padded subspace pigeonhole"))
    if R == 1:
        out.append((Fr(3, 4), lg(3), "3 hyperplanes"))
        for mp in range(4, N // 2 + 1):
            out.append((Fr(5, 8) + Fr(1, 2 ** (mp + 2)), lg((4**mp - 2**mp) // 4), f"biased padding m'={mp}"))
        out.append((Fr(5, 8), lg(56 * (2**N - 7)), "5n/8 class"))
        for c in range(3, 9):
            v = 3
            for i in range(1, c):
                v *= qc(i, N - c + i)
            out.append((Fr(1, 2) + Fr(1, 2 ** (c + 1)), lg(v), f"nested c={c}"))
        if quoted:
            w = n // 16
            out.append((Fr(9, 16), lg(71680 * (6 * w - 5) * (w - 1) * (w - 2) * (w - 4)), "DKTZ h=3 (quoted)"))
            if N == 25:
                out.append((Fr(17, 32), 262.5, "DKTZ h=4 (quoted)"))
    else:
        if R == 2:
            out.append((Fr(3, 8), lg(56 * (2**N - 7)), "complement of the 5n/8 class"))
        for c in range(1, 8):
            # X = a + V of codimension r, disjoint from the subspace P of codimension R + c (Theorem 3.1)
            r = R if c == 1 else R - 1
            m = N - R + 1
            if c >= 2 and m - c + 2 < 3:
                break
            nX = (2 ** (R + c) - 1) * (gb(N - 1, r - 1) - (2 ** (R + c - 1) - 1) * gb(N - 2, r - 2)) * 2 ** (r - 1)
            v = nX if c == 1 else nX * (qc(c, m) - 2 ** (m + 1) + 2)
            if v <= 0 or R + c > N - 2:
                break
            out.append((rho * (1 + Fr(1, 2**c)), lg(v), f"nested c={c}"))
    return sorted(out, key=lambda e: -e[0])


def best_tau(R, N, need, kappa=KAPPA, ell=ELL, quoted=False):
    """largest tau at which some list has log2(L * tau) >= need; returns (tau, label, log2 L)"""
    n, k = 2**N, 2 ** (N - R)
    best = (0.0, "none", 0.0)
    for tau, v, lab in lists(R, N, kappa, quoted):
        if v + lg(tau) >= need and float(tau) > best[0]:
            best = (float(tau), lab, v)
    lo, hi = k + ell, n                                   # pigeonhole: largest T with enough members
    if pigeon(n, k, ell, lo) + lg(lo / n) >= need:
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if pigeon(n, k, ell, mid) + lg(mid / n) >= need:
                lo = mid
            else:
                hi = mid
        if lo / n > best[0]:
            best = (lo / n, "pigeonhole", pigeon(n, k, ell, lo))
    return best


need_gen = lambda s: 11 + LQ * (s - 1)                    # L*tau >= 2^11 q^(s-1): members through one column
need_wc = lambda s: lg(3) if s == 1 else 11 + LQ * (s - 2)
floor_q = lambda tau: math.ceil(108 / lg(1 / tau) - 1e-9)

if __name__ == "__main__":
    print("== 1. list lower bounds at level 0 (log2 of the number of polynomials of degree <= k within the agreement)")
    for R in (1, 2, 3, 4):
        N = KAPPA + R
        n, k = 2**N, 2 ** (N - R)
        print(f"rate 2^-{R}, N = {N}, Johnson {2**(-R/2):.4f}:")
        for tau, v, lab in lists(R, N, quoted=True):
            print(f"   tau = {str(tau):>9} = {float(tau):.5f}   log2 L >= {v:8.1f}   {lab}")
        for B in (0, 128, 1024, 5000):
            t, lab, v = best_tau(R, N, B)
            lo, hi = k + ELL, n
            while hi - lo > 1:
                mid = (lo + hi) // 2
                lo, hi = (mid, hi) if pigeon(n, k, ELL, mid) >= B else (lo, mid)
            print(f"   pigeonhole: log2 L >= {B:5d} up to tau = {lo/n:.6f}")

    print("\n== 2. attack requirements on the list (log2 of members through one column), and what the proof tolerates")
    le0 = LQ - lg(2**KAPPA + ELL - 1 + 2**ELL - 1)
    print(f"   log2(1/eps_0) = {le0:.3f}")
    print("    s   proof 5.2 (L <=)   pinning union bound (L <=)   attack generic weights (L*tau >=)   attack worst-case weights (L*tau >=)")
    for s in (1, 2, 3, 4, 6, 8, 11, 12, 14, 20, 30, 40):
        proof = (s * le0 - 1062) / 3
        pin = (s * le0 - 110 + 1) / 2
        print(f"   {s:2d}   {max(proof, float('-inf')):12.1f}   {pin:20.1f}   {need_gen(s):26.1f}   {need_wc(s):30.1f}")

    print("\n== 3. attack frontier at level 0: largest agreement fraction with an attack below 2^125, and query floor")
    for R in (1, 2, 3, 4):
        N = KAPPA + R
        J = 2 ** (-R / 2)
        print(f"rate 2^-{R} (N = {N}): Johnson {J:.4f}, {floor_q(J)} queries; capacity {2.0**-R}, {math.ceil(108/R)} queries")
        prev = None
        for s in range(2, 41):
            g = best_tau(R, N, need_gen(s))
            w = best_tau(R, N, need_wc(s))
            gq = best_tau(R, N, need_gen(s), quoted=True)
            wq = best_tau(R, N, need_wc(s), quoted=True)
            row = (round(g[0], 5), g[1], round(w[0], 5), w[1], round(gq[0], 5), round(wq[0], 5))
            if row != prev:
                fg, fw = floor_q(min(g[0], J)), floor_q(min(w[0], J))
                print(f"   s >= {s:2d}: generic weights tau = {g[0]:.5f} ({g[1]}), floor {fg} queries, gap to Johnson {floor_q(J)-fg} = {100*(floor_q(J)-fg)/floor_q(J):.0f}% | "
                      f"worst-case weights tau = {w[0]:.5f} ({w[1]}), floor {fw}, gap {floor_q(J)-fw} = {100*(floor_q(J)-fw)/floor_q(J):.0f}%"
                      + (f" | with quoted counts: {gq[0]:.5f} / {wq[0]:.5f}" if (gq[0], wq[0]) != (g[0], w[0]) else ""))
                prev = row

    print("\n== 4. if the lists were no larger than the lower bounds: points Theorem 5.2 needs just above each step (level 0, one batch)")
    for R in (1, 2, 3, 4):
        N = KAPPA + R
        print(f"rate 2^-{R}:", end="")
        for tau, v, lab in lists(R, N):
            if float(tau) < 2 ** (-R / 2) and v > 20:
                print(f"  above {tau}: b={v:.0f} -> s={math.ceil((3*v+1062)/le0)}", end=";")
        print()

    print("\n== 5. the counting bound C(n,d+1)/C(A,d+1): bits per query log2(n/A) it supports with s points (level-0 rate 1/2)")
    print("   level kappa ell  N   Johnson bits  capacity bits | theorem 5.2: s=20, s=40 | fold lemma at the pinning requirement: s=20, s=40")
    for i, (kap, ell) in enumerate(((24, 6), (20, 4), (16, 4), (12, 4), (8, 4), (4, 4))):
        Ri = 1 + 3 * i
        Ni = kap + Ri
        n, d = 2**Ni, 2**kap - 1 + ell
        le = LQ - lg(d + 2**ell - 1)
        base = 1062 if ell == 6 else 824

        def bits(budget):
            # largest log2(n/A) with log2 C(n,d+1) - log2 C(A,d+1) <= budget
            if budget <= 0:
                return 0.0
            lo, hi = d + 2, n
            f = lambda A: lchoose(n, d + 1) - lchoose(A, d + 1)
            if f(lo) <= budget:
                return lg(n / lo)
            while hi - lo > 1:
                mid = (lo + hi) // 2
                lo, hi = (lo, mid) if f(mid) <= budget else (mid, hi)
            return lg(n / hi)
        th = [bits((s * le - base) / 3) for s in (20, 40)]
        pn = [bits((s * le - 109) / 2) for s in (20, 40)]
        sth = next((s for s in range(1, 2000) if bits((s * le - base) / 3) > Ri / 2), None)
        spn = next((s for s in range(1, 2000) if bits((s * le - 109) / 2) > Ri / 2), None)
        print(f"   {i}     {kap:2d}    {ell}  {Ni}   {Ri/2:6.2f}        {Ri:5.2f}        | {th[0]:8.4f} {th[1]:8.4f}     | {pn[0]:8.4f} {pn[1]:8.4f}   | points to beat Johnson: {sth} / {spn}")

    print("\n== 6. later levels (level-0 rate 1/2): frontier in bits per query log2(1/tau)")
    print("   level  rate    N   Johnson  capacity | worst-case s=2 | generic s=2 | generic s=3 | generic s=8")
    for i, (kap, ell) in enumerate(((24, 6), (20, 4), (16, 4), (12, 4), (8, 4), (4, 4))):
        Ri = 1 + 3 * i
        Ni = kap + Ri
        cells = []
        for need in (need_wc(2), need_gen(2), need_gen(3), need_gen(8)):
            t = best_tau(Ri, Ni, need, kappa=kap, ell=ell)
            cells.append(f"{lg(1/t[0]):5.2f} ({t[1]})" if t[0] > 0 else "none")
        print(f"   {i}      2^-{Ri:<2d}  {Ni}   {Ri/2:5.2f}    {Ri:5.2f}   | " + " | ".join(cells))

    print("\n== 7. pair collisions at s uniform points, log2 of the probability (model of section 2; flats exact)")
    fam = (("flats, rate 1/4, 2n-2 affine hyperplanes", 26, 27.0, 0.5, 24, True),
           ("5n/8 class, rate 1/2", 25, lg(56 * (2**25 - 7)), 0.625, 24, False),
           ("nested c=3 at 9n/16, rate 1/2", 25, lists(1, 25)[[e[2] for e in lists(1, 25)].index("nested c=3")][1], 0.5625, 24, False),
           ("nested c=4 at 17n/32, rate 1/2", 25, lists(1, 25)[[e[2] for e in lists(1, 25)].index("nested c=4")][1], 0.53125, 24, False),
           ("biased padding m'=12, rate 1/2", 25, 22.0, 0.625, 24, False))
    for name, N, L, tau, kap, exact in fam:
        le = LQ - lg(2**kap + ELL - 1 + 63)
        cells = []
        for s in (1, 2, 3):
            best = -1e9
            for j in range(s + 1):
                pairs = 2 * (L + j * lg(tau)) - 1 - LQ * (s - j)
                if exact and j < s:
                    continue
                best = max(best, lg(math.comb(s, j)) + j * (N - LQ) + min(0.0, pairs))
            cells.append(f"s={s}: {best:7.1f} (union bound {min(0.0, 2*L-1-s*le):7.1f})")
        print(f"   {name:42s} " + "  ".join(cells))
