#!/usr/bin/env python3
"""Referee 46: the arithmetic of notes 37 and 39, recomputed from the formulas with exact integers.

1. The conditional bounds of note 39 Theorem 1.3 and Corollary 1.5 and of note 37 Theorem 3.5.
2. The constant of note 39 Corollary 2.6.
3. The table of note 37 Theorem 5.1 (own optimization over beta and theta_1).
4. The counting step of note 37 Theorem 4.3, exhaustively for N <= 10.
5. Which small ordinary problems sit inside the levels of the descent (the hypothesis must hold for them).
python3 46_numbers.py
"""
from fractions import Fraction
from math import comb, log2, ceil, floor, isqrt


def lg(x):
    """log2 of a positive int or Fraction of any size."""
    if isinstance(x, Fraction):
        return lg(x.numerator) - lg(x.denominator)
    x = int(x)
    b = x.bit_length()
    if b <= 1000:
        return log2(x)
    return (b - 1000) + log2(x >> (b - 1000))


def gauss(N, r):
    num = den = 1
    for i in range(r):
        num *= (1 << (N - i)) - 1
        den *= (1 << (i + 1)) - 1
    return num // den


def base_log2(N, k, Delta, j):
    """log2 of the Lemma 3.2 bound for a level-j problem: max over degrees kappa' <= floor((k-1)/2^j) of
    prod_{i=0}^{kappa'} (n - m i)/(m kappa' + Delta - m i), m = 2^j. Consecutive degrees differ by the
    factor (n' - kappa' - 1)/(Delta/m + kappa' + 1), n' = n/m."""
    n = 1 << N
    m = 1 << j
    nq = n >> j
    kap = (k - 1) >> j
    cur = log2(n / Delta)
    best = cur
    for t in range(kap):
        cur += log2((nq - t - 1) / (Delta / m + t + 1))
        best = max(best, cur)
    return best


print("== 1. conditional bounds ==")
for N in (25,):
    n = 1 << N
    k = n // 2
    T = -((-64 * n) // 100)  # ceil(0.64 n)
    Delta = T - k + 1
    J = (k - 1).bit_length()  # ceil(log2 k) for k >= 2
    assert (1 << J) >= k > (1 << (J - 1))
    expo = N * J - J * (J - 1) // 2
    print(f"N={N} k=2^{N-1} T=ceil(0.64 n)={T} Delta={Delta} sigma={Delta/n:.6f} J={J} NJ-J(J-1)/2={expo} n/Delta+1={n/Delta+1:.4f}")
    for f in (2, 7, 16, 133, 134, 1000, 15736):
        G = comb(f + 1, 3)
        bound = Fraction(G ** J * (1 << expo) * (n + Delta), Delta)
        print(f"   note 39 Thm 1.3, f={f:6d}: C(f+1,3)={G}, log2 bound = {lg(bound):.2f}")
    for B in (0, 13568, 2 ** 20):
        bound = (1 << expo) * (J * (B + 2) + Fraction(n, Delta))
        print(f"   note 37 Thm 3.5, B={B}: log2 bound = {lg(bound):.2f}")
    # Corollary 1.5 with f ordinary = 133
    sigma = Fraction(Delta, n)
    for f in (7, 133, 134, 1000):
        f2 = floor(2 * f / sigma)
        need = Fraction(4) / sigma
        c = 0
        while (1 << c) < need:
            c += 1  # ceil(log2(4/sigma))
        j0 = N + 1 - c
        kap = (k - 1) >> j0
        nq = n >> j0
        base = Fraction(n, Delta) ** (kap + 1)
        G = comb(f2 + 1, 3)
        e0 = N * j0 - j0 * (j0 - 1) // 2
        bound = G ** j0 * (1 << e0) * (base + 1)
        # sharper base case from note 37 Lemma 3.2 with A = m kappa + Delta
        m = 1 << j0
        A = m * kap + Delta
        prod = Fraction(1)
        for i in range(kap + 1):
            prod *= Fraction(n - m * i, A - m * i)
        print(f"   note 39 Cor 1.5, f={f}: f'={f2}, j0={j0} (quotient of {nq} points), kappa={kap}, base (n/Delta)^(kappa+1)=2^{lg(base):.2f} (Lemma 3.2: 2^{base_log2(N, k, Delta, j0):.2f}), log2 bound = {lg(bound):.2f}")

print("   the same theorem stopped at level j0 < J with the base case of note 37 Lemma 3.2 (hypothesis needed only on quotients with more than 2^(N-j0) points):")
N = 25
n = 1 << N
k = n // 2
T = -((-64 * n) // 100)
Delta = T - k + 1
for f in (7, 14, 16, 134, 1000):
    G = comb(f + 1, 3)
    rows = []
    for j0 in range(14, 25):
        e0 = N * j0 - j0 * (j0 - 1) // 2
        b = base_log2(N, k, Delta, j0)
        tot = j0 * log2(G) + e0 + log2(2 ** b + 1) if b < 900 else j0 * log2(G) + e0 + b
        rows.append((tot, j0, b))
    best = min(rows)
    print(f"      f={f:5d}: " + ", ".join(f"j0={j0}: 2^{tot:.1f}" for tot, j0, b in rows if j0 >= 17) + f"   best j0={best[1]} (quotient {n >> best[1]} points, base 2^{best[2]:.1f}): 2^{best[0]:.1f}")

print("   ordinary words (note 39 Lemma 1.4 and Corollary 1.5): f' = floor(2 f0 / sigma), hypothesis at slack sigma/2 on quotients with more than 2^(N-j0) points:")
for f0 in (20, 134, 1000):
    f2 = floor(2 * f0 * n / Delta)
    G = comb(f2 + 1, 3)
    rows = []
    for j0 in range(14, 22):
        e0 = N * j0 - j0 * (j0 - 1) // 2
        b = base_log2(N, k, Delta, j0)
        rows.append((j0 * log2(G) + e0 + b, j0, b))
    best = min(rows)
    print(f"      f0={f0:5d}, f'={f2}: " + ", ".join(f"j0={j0}: 2^{tot:.1f}" for tot, j0, b in rows if j0 >= 16) + f"   best j0={best[1]}: 2^{best[0]:.1f}")
# the recursion a_j <= f + G 2^(N-j) a_(j+1) unrolled exactly, against the closed form
for f in (2, 7, 134):
    G = comb(f + 1, 3)
    J = 24
    a = Fraction(n, Delta)
    for j in range(J - 1, -1, -1):
        a = f + G * (1 << (N - j)) * a
    closed = G ** J * (1 << (N * J - J * (J - 1) // 2)) * (Fraction(n, Delta) + 1)
    print(f"   recursion a_j = f + G 2^(N-j) a_(j+1) from a_J = n/Delta, f={f}: a_0 = 2^{lg(a):.3f} <= closed form 2^{lg(closed):.3f}: {a <= closed}")

print()
print("== 2. note 39 Corollary 2.6 at tau = 0.64, rate 1/2 ==")
eps = Fraction(64, 100) - Fraction(5, 8)
b1 = 1 / (16 * eps * eps)
b2 = 1 + (2 * Fraction(64, 100) - Fraction(1, 2)) / eps
print(f"   1/(16 eps^2) = {float(b1):.3f}, 1 + (2 tau - 1/2)/eps = {float(b2):.3f}: at most {floor(max(b1, b2))} codewords; (T-k+1)/3 = {0.14/3:.4f} n")

print()
print("== 3. note 37 Theorem 5.1 ==")


def thm51(N, rho_inv, below, verbose=False):
    n = 1 << N
    k = n // rho_inv
    TJ = isqrt(n * (k - 1)) + 1  # least T with T^2 > n(k-1)
    T = TJ - below
    tau = T / n
    theta = (k - 1) / n - tau * tau
    best = None
    kk = (k - 1) / n
    for bi in range(1, 2000):
        beta = kk * bi / 2000
        # g as a function of theta_1 is decreasing; choose theta_1 to minimise max(1 + 2/theta_1, 2 + C/g)
        pistar = 1
        while pistar < 6 * beta * n / 7:
            pistar *= 2
        dstar = (k - 1) // pistar
        lo = 6 * beta * n / 7
        hi = min(k - 1, T - k + 1 + 2 * beta * beta * n / 21)
        p = 1
        haspow = False
        while p <= hi:
            if p >= lo:
                haspow = True
            p *= 2
        C = lg(gauss(N, N - (pistar.bit_length() - 1)))
        for i in range(1, dstar + 2):
            C += log2((n - k + i) / (T - k + i))

        def g_of(t1):
            return 1 - 63 * (theta + t1) / beta ** 2 - (tau ** 3 + (1 + 2 * tau) * (theta + t1)) / (kk - beta)

        if g_of(0) <= 0:
            continue
        # theta_1 from 0 up to where g vanishes
        slope = 63 / beta ** 2 + (1 + 2 * tau) / (kk - beta)
        t1max = g_of(0) / slope
        for ti in range(1, 200):
            t1 = t1max * ti / 200
            g = g_of(t1)
            first = log2(1 + 2 / t1)
            second = first if not haspow else max(first, log2(2 + 2 ** min(C - log2(g), 1000)) if C - log2(g) < 1000 else C - log2(g))
            val = second
            if best is None or val < best[0]:
                best = (val, beta, g, t1, haspow, pistar, dstar)
    return TJ, T, tau, theta, best


for rho_inv, rows in ((2, ((25, 175), (28, 1399))), (4, ((25, 376), (28, 3015))), (8, ((25, 237), (28, 1904))), (16, ((25, 225), (28, 1808)))):
    for N, below in rows:
        TJ, T, tau, theta, best = thm51(N, rho_inv, below)
        if best is None:
            print(f"   rate 1/{rho_inv} N={N} below={below}: no admissible (beta, theta_1)")
            continue
        val, beta, g, t1, haspow, pistar, dstar = best
        print(f"   rate 1/{rho_inv} N={N}: Johnson threshold T_J={TJ}, T=T_J-{below}, T/n={tau:.7f}, theta={theta:.3e}: best bound 2^{val:.1f} at beta={beta:.4f}, g={g:.3f}, theta_1={t1:.2e}, pi*=n/{(1<<N)//pistar}, delta*={dstar}, power of two available: {haspow}")
# with the parameters printed in note 37
print("   with note 37's own (beta, g):")
for rho_inv, N, below, beta in ((2, 25, 175, 0.0875), (2, 28, 1399, 0.0875), (4, 25, 376, 0.0794), (4, 28, 3015, 0.0794), (8, 25, 237, 0.0731), (16, 25, 225, 0.0366)):
    n = 1 << N
    k = n // rho_inv
    TJ = isqrt(n * (k - 1)) + 1
    T = TJ - below
    tau = T / n
    kk = (k - 1) / n
    theta = kk - tau * tau
    pistar = 1
    while pistar < 6 * beta * n / 7:
        pistar *= 2
    dstar = (k - 1) // pistar
    C = lg(gauss(N, N - (pistar.bit_length() - 1)))
    for i in range(1, dstar + 2):
        C += log2((n - k + i) / (T - k + i))
    g0 = 1 - 63 * theta / beta ** 2 - (tau ** 3 + (1 + 2 * tau) * theta) / (kk - beta)
    slope = 63 / beta ** 2 + (1 + 2 * tau) / (kk - beta)
    best = None
    for ti in range(1, 2000):
        t1 = g0 / slope * ti / 2000
        g = g0 - slope * t1
        v = max(log2(1 + 2 / t1), C - log2(g))
        if best is None or v < best[0]:
            best = (v, g, t1)
    lo = 6 * beta * n / 7
    hi = min(k - 1, T - k + 1 + 2 * beta * beta * n / 21)
    print(f"      rate 1/{rho_inv} N={N} below={below} beta={beta}: g(theta_1=0)={g0:.3f}, pi*=n/{n//pistar}, delta*={dstar}, Gaussian binomial x product = 2^{C:.2f}, balanced bound 2^{best[0]:.1f} (g={best[1]:.3f}); interval for a power of two [{lo/n:.4f} n, {hi/n:.4f} n]; constant alternative 1+2/theta_1 = 2^{log2(1+2*slope/g0):.1f} at g->0")

# end of the windows: largest theta with g > 0 for some beta (theta_1 -> 0)
for rho_inv in (2, 4, 8, 16):
    N = 25
    n = 1 << N
    k = n // rho_inv
    kk = (k - 1) / n
    TJ = isqrt(n * (k - 1)) + 1
    lo, hi = 0, n // 100
    while lo < hi:
        mid = (lo + hi + 1) // 2
        T = TJ - mid
        tau = T / n
        theta = kk - tau * tau
        ok = False
        for bi in range(1, 4000):
            beta = kk * bi / 4000
            if 1 - 63 * theta / beta ** 2 - (tau ** 3 + (1 + 2 * tau) * theta) / (kk - beta) > 0:
                ok = True
                break
        if ok:
            lo = mid
        else:
            hi = mid - 1
    T = TJ - lo
    print(f"   rate 1/{rho_inv} N=25: g > 0 is possible up to {lo} points below the Johnson threshold, theta = {kk - (T/n)**2:.2e}")

print()
print("== 4. counting step of note 37 Theorem 4.3, exact bounds of Steps 1 and 3 ==")
tot = bad = 0
for N in range(3, 11):
    n = 1 << N
    for delta in range(2, n + 1):
        smax = (delta * delta - 1) // (4 * n)  # s < delta^2/(4n)
        for s in range(0, smax + 1):
            if 3 * delta - s > n:
                continue
            for s2 in range(0, s // 3 + 1):
                for s1 in range(s2, (s - s2) // 2 + 1):
                    s0 = s - s1 - s2
                    r0, r1, r2 = delta - s0, delta - s1, delta - s2
                    tot += 1
                    if not (r1 > s0 and r0 > s1 and r2 - s0 - s2 > 0):
                        bad += 1
                        continue
                    Z0 = Fraction(r1 * r2 - s0 * (n - 1), r1 - s0)
                    Z1 = Fraction(r0 * r2 - s1 * (n - 1), r0 - s1)
                    P2 = Fraction(r2 * (r2 - 1), r2 - s0 - s2)
                    lower = ceil(Z0) + ceil(Z1) - 1 - floor(P2)
                    if not (2 * lower > delta and 3 * delta - 3 * s >= 2 * delta):
                        bad += 1
print(f"   parameter sets (n <= 1024, delta, s0 >= s1 >= s2) with s < delta^2/4n and nu <= n: {tot}; failing |Z0|+|Z1|-1-|P2| > delta/2 or delta >= 3s: {bad}")
# the statement without a bound on delta is false: for delta > (6 + sqrt 32) n the hypothesis holds for every function
n = 32
delta = 13 * n
print(f"   remark: for delta = 13 n and nu = 0, s = 3 delta = {3*delta} < delta^2/4n = {delta*delta/(4*n)}: the hypothesis of Theorem 4.3 holds vacuously, so the theorem needs delta < 2n (true for triple functions, delta <= k - 1)")

print()
print("== 5. ordinary problems inside the levels (rate 1/2, k = n/2, T = ceil(0.64 n), N = 25) ==")
N = 25
n = 1 << N
k = n // 2
T = -((-64 * n) // 100)
Delta = T - k + 1
for j in range(N - 7, N - 1):
    m = 1 << j
    nq = n >> j
    kap = (k - 1) >> j
    Tq = kap + ceil(Fraction(Delta, m))
    b = base_log2(N, k, Delta, j)
    print(f"   level {j}: quotient of {nq} points, degree <= {kap}, an ordinary word needs agreement >= {Tq} = {Tq/nq:.4f} n'; every list of the level has at most 2^{b:.2f} = {floor(2 ** b + 1e-9)} members (Lemma 3.2, maximum over the degrees <= {kap})")
