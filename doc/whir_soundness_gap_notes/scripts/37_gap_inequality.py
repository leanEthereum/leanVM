"""Researcher 37: exhaustive check of the counting step of the gap theorem (note 37, Theorem 4.3), and the numbers of
Theorem 5.1 (the list bound just below the Johnson radius on a generic subspace).

Part 1. For n = 2^N, N <= 10, every degree delta and every (s_0 >= s_1 >= s_2) with 1 <= s = s_0 + s_1 + s_2 <
delta^2 / (4n) and 3 delta - s <= n, the exact bounds of the proof

    |Z_0| >= (r_1 r_2 - s_0 (n - 1)) / (r_1 - s_0),   |Z_1| >= (r_0 r_2 - s_1 (n - 1)) / (r_0 - s_1),
    |P_2| <= r_2 (r_2 - 1) / (r_2 - s_0 - s_2),       |Pi| >= |Z_0| + |Z_1| - 1 - |P_2|,       r_i = delta - s_i,

must give |Pi| > delta / 2, and delta >= 3 s must hold. The script checks both with exact rational arithmetic, and
does the same for random parameters with N up to 28.

Part 2. For rho in {1/2, 1/4, 1/8, 1/16} and N = 25, 28: the largest theta_target for which Theorem 5.1 applies with
T = ceil(n sqrt(rho - theta_target)) and theta_1 = theta_target / 2 (some beta on a grid gives g > 0), and the list
bound of the theorem at 0.6 times that value: part (a) the polynomial bound, part (b) the constant bound 1 + 2/theta_1,
which needs in addition that no power of two lies in [6 beta n / 7, min(k - 1, T - k + 1 + 2 beta^2 n / 21)].

Run: python3 37_gap_inequality.py      (about 20 seconds)
"""
import math
import random
from fractions import Fraction as Fr


def check(n, delta, s0, s1, s2):
    s = s0 + s1 + s2
    r0, r1, r2 = delta - s0, delta - s1, delta - s2
    if not (delta >= 3 * s and r1 > s0 and r0 > s1 and r2 > s0 + s2):
        return False
    z0 = Fr(r1 * r2 - s0 * (n - 1), r1 - s0)
    z1 = Fr(r0 * r2 - s1 * (n - 1), r0 - s1)
    p2 = Fr(r2 * (r2 - 1), r2 - s0 - s2)
    return z0 + z1 - 1 - p2 > Fr(delta, 2)


def part1():
    total = 0
    for N in range(2, 11):
        n = 1 << N
        for delta in range(1, n):
            smax = (delta * delta - 1) // (4 * n)  # s < delta^2 / (4n)
            for s in range(1, smax + 1):
                if 3 * delta - s > n:
                    continue
                for s2 in range(0, s // 3 + 1):
                    for s1 in range(s2, (s - s2) // 2 + 1):
                        s0 = s - s1 - s2
                        total += 1
                        assert check(n, delta, s0, s1, s2), (n, delta, s0, s1, s2)
    rng = random.Random(1)
    rnd = 0
    while rnd < 200000:
        N = rng.randint(11, 28)
        n = 1 << N
        delta = rng.randint(1, n // 2)
        smax = (delta * delta - 1) // (4 * n)
        if smax < 1:
            continue
        s = smax if rng.random() < 0.5 else rng.randint(1, smax)
        if 3 * delta - s > n:
            delta = (n + s) // 3
            if s >= Fr(delta * delta, 4 * n):
                continue
        s2 = rng.randint(0, s // 3)
        s1 = rng.randint(s2, (s - s2) // 2)
        assert check(n, delta, s - s1 - s2, s1, s2), (n, delta, s, s1, s2)
        rnd += 1
    print("part 1: %d parameter sets with N <= 10 (all) and %d random ones with 11 <= N <= 28: the counting step holds" % (total, rnd))


def log2_gauss_binom(N, c):
    v = 0.0
    for i in range(c):
        v += math.log2((2.0 ** (N - i) - 1) / (2.0 ** (i + 1) - 1))
    return v


def theorem51(N, k, T, beta, theta1):
    """Theorem 5.1 of note 37 with exact n, k, T. Returns (theta, g, log2 bound (a), constant-case flag (b))."""
    n = 1 << N
    tau = T / n
    theta = (k - 1) / n - tau * tau
    th = theta + theta1
    g = 1 - 63 * th / beta ** 2 - (tau ** 3 + (1 + 2 * tau) * th) / ((k - 1) / n - beta)
    if g <= 0:
        return theta, g, None, False
    dmin = 6.0 / 7.0 * beta * n
    dmax = min(k - 1, T - k + 1 + 2 * beta * beta * n / 21)
    logpi = math.ceil(math.log2(dmin))
    no_power_of_two = 2.0 ** logpi > dmax
    c = N - logpi
    dstar = (k - 1) >> logpi
    per_class = sum(math.log2((n - k + i) / (T - k + i)) for i in range(1, dstar + 2))
    bound = max(math.log2(1 + 2 / theta1), math.log2(2 + 2.0 ** (log2_gauss_binom(N, c) + per_class - math.log2(g))))
    return theta, g, bound, no_power_of_two


def part2():
    print("part 2: Theorem 5.1 with theta_1 = theta_target / 2 and T = ceil(n sqrt(rho - theta_target)), beta on a grid of 400 values")
    for R in (1, 2, 3, 4):
        rho = 2.0 ** -R
        for N in (25, 28):
            n, k = 1 << N, 1 << (N - R)
            johnson = math.isqrt(n * (k - 1)) + 1  # smallest T with T^2 > n (k - 1)

            def best(tt, constant):
                T = math.ceil(n * math.sqrt(rho - tt))
                out = None
                for i in range(1, 400):
                    beta = rho * i / 400
                    th, g, b, flag = theorem51(N, k, T, beta, tt / 2)
                    if b is None or (constant and not flag):
                        continue
                    if constant:
                        b = math.log2(1 + 4 / tt)
                    if out is None or b < out[3]:
                        out = (T, beta, g, b, th)
                return out

            for constant in (False, True):
                lo, hi = 0.0, rho / 2
                for _ in range(60):
                    mid = (lo + hi) / 2
                    if best(mid, constant) is not None:
                        lo = mid
                    else:
                        hi = mid
                if lo < 1e-12:
                    print("  rho = 1/%d, N = %d, part (%s): no admissible window" % (1 << R, N, "b" if constant else "a"))
                    continue
                tt = lo * 0.6
                T, beta, g, b, th = best(tt, constant)
                print("  rho = 1/%d, N = %d, part (%s): theta_target up to %.3e; at %.3e: T = %d (T/n = %.7f, %d points below the Johnson threshold %d), beta = %.4f, g = %.3f, log2(list bound) = %.1f"
                      % (1 << R, N, "b" if constant else "a", lo, tt, T, T / n, johnson - T, johnson, beta, g, b))


if __name__ == "__main__":
    part1()
    part2()
