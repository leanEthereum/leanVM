#!/usr/bin/env python3
"""Note 84, Theorem 5.1: the slack eps_Delta of the robust one-functional rank property.

eps(r, v, J, L, nd, p_log2, a, lam) evaluates the formula of Section 5 for one lambda;
best(...) minimizes over lambda on a grid. Standard library only.
  r: rate 2^-r, v: k = 2^v, J: fixed top levels, L: number of differences (t - 1),
  nd: |Delta| (binom(t,2) for the graphic directions), p_log2: log2 of the failure
  probability, a: excess allowed to the top code (Top_Delta(a)).
"""
import math
import sys

BITS = 64.0


def log2_binom(n, m):
    if m < 0 or m > n:
        return float("-inf")
    return (math.lgamma(n + 1) - math.lgamma(m + 1) - math.lgamma(n - m + 1)) / math.log(2)


def multipliers(lam, eta, nd, levels):
    """Backward recursion of Section 4. Returns (C_J, C'_J)."""
    C = 0.0
    Cp = 0.0
    for _ in range(levels):
        B = 0.5 * (C - Cp)
        x = 2.0 ** (-(lam + B))
        z = 2.0 ** (-(eta - B))
        c = math.log2(1.0 + 2.0 * nd * x + nd * (nd - 1.0) * x * x)
        cp = math.log1p(2.0 * z * (1.0 + (nd - 1.0) * x)) / math.log(2)
        C += c
        Cp += cp
    return C, Cp


def c_kappa(eps_hat, r, v, J):
    tot = 0.0
    Lv = v - J
    for j in range(J, v):
        m = j - J
        wgt = 2.0 ** (-(m + 1)) if j <= v - 2 else 2.0 ** (-(Lv - 1))
        g = math.floor(eps_hat * 2.0 ** (j + 1 + r))
        tot += wgt * log2_binom(g + m, m)
    return tot


def eps(r, v, J, L, nd, p_log2, a, lam, bits=BITS, parts=False):
    rho = 2.0 ** (-r)
    Lv = v - J
    eta = (bits - lam) / 2.0
    C, Cp = multipliers(lam, eta, nd, Lv)
    M = lam * L * rho + 0.5 * C
    if J > 0:
        M += 0.5 * math.log2(1.0 + nd * 2.0 ** (-2.0 * lam - C + Cp))
    nJ1 = 2.0 ** (J + 1 + r)
    nJ = 2.0 ** (J + r)

    def Psi(eh):
        return M + (math.log2(Lv) - p_log2 + 2.0 ** -31 + c_kappa(eh, r, v, J)) / nJ1

    eh = float(Lv)
    for _ in range(200):
        new = 2.0 / (bits - lam) * (Psi(eh) + (bits + lam) * a / (2.0 * nJ))
        if new >= eh:
            break
        eh = new
    val = Psi(eh) / (bits - lam) + bits / (bits - lam) * a / nJ
    if parts:
        return val, M / (bits - lam), (Psi(eh) - M) / (bits - lam), C, Cp, eh
    return val


def best(r, v, J, L, nd, p_log2=-130.0, a=0.0, bits=BITS, lo=0.25, hi=None, step=0.05):
    hi = bits - 1.0 if hi is None else hi
    bl, bv = None, float("inf")
    lam = lo
    while lam < hi:
        val = eps(r, v, J, L, nd, p_log2, a, lam, bits)
        if val < bv:
            bl, bv = lam, val
        lam += step
    return bv, bl


def graphic(t):
    return t - 1, t * (t - 1) // 2


if __name__ == "__main__":
    print("== check against note 73 (L = 1, |Delta| = 1): 64*eps, rate 1/2 and 1/4, J = 4 ==")
    for r, logn, want in ((1, 19, 5.34), (1, 25, 5.68), (2, 19, 3.06), (2, 25, 3.24)):
        val, lam = best(r, logn - r, 4, 1, 1)
        print(f"  r={r} log2 n={logn}: 64*eps = {64*val:.3f} (note 73: {want}), lambda = {lam:.2f}")
    print()
    print("== eps_t for the graphic directions, p = 2^-130 ==")
    print("   columns: t, (t-1)rho, eps_t, eps_t/((t-1)rho), main part, first-level part, lambda, C_J, C'_J")
    for r in (3, 4, 7, 10):
        for logn in (20, 24):
            v = logn - r
            for J in (0, 1, 2, 3):
                print(f" rate 2^-{r}, n = 2^{logn}, J = {J} (n_(J+1) = {2**(J+1+r)})")
                ts = [2, 3, 4, 5, 7, 8, 12, 13, 16, 32, 48, 64, 94, 128, 256, 376]
                for t in ts:
                    L, nd = graphic(t)
                    if L * 2.0 ** (-r) >= 1.0:
                        continue
                    val, lam = best(r, v, J, L, nd)
                    _, main, first, C, Cp, eh = eps(r, v, J, L, nd, -130.0, 0.0, lam, parts=True)
                    base = L * 2.0 ** (-r)
                    print(f"   t={t:4d} {base:.5f} {val:.5f} {val/base:6.3f} {main:.5f} {first:.5f} lam={lam:5.2f} C={C:.3f} C'={Cp:.1e}")
    sys.stdout.flush()
