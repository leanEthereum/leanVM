#!/usr/bin/env python3
"""Note 73, Theorem 5.1: the explicit slack eps_0(lambda) of the random tree code.

eps_0 = sup of eps with (64 - lam) eps < lam rho + C_J/2 + (1/2) log2(1 + 2^(-2 lam - C_J))
                                  + (log2(L chi / p) + c_kappa(eps)) / n_{J+1},
C_v = 0, C_i = C_{i+1} + log2(1 + 2^(1 - lam - C_{i+1}/2)),
c_kappa(eps) = sum_j (omega_j / u_{J+1}) log2 binom(floor(eps n_{j+1}) + j - J, j - J).
Standard library only. Prints eps_0 * 64 minimized over lambda on a grid.
"""
import math, sys

LOG2Q = 64

def log2binom(a, b):
    if b <= 0 or b >= a: return 0.0
    return (math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)) / math.log(2)

def CJ(lam, L):
    C = 0.0
    for _ in range(L):
        C += math.log2(1 + 2 ** (1 - lam - C / 2))
    return C

def ckappa(eps, v, r, J):
    n = 2 ** (v + r); tot = 0.0
    uJ1 = 2 ** (v - J - 1)
    for j in range(J, v):
        u1 = 2 ** (v - j - 1)                      # u_{j+1}
        u2 = 2 ** (v - j - 2) if j <= v - 2 else 0  # u_{j+2}
        om = u1 - u2
        nj1 = 2 ** (j + 1 + r)
        G = math.floor(eps * nj1)
        tot += om / uJ1 * log2binom(G + j - J, j - J)
    return tot

def eps0(lam, v, r, J, log2p=-130.0, main_only=False):
    rho = 2.0 ** (-r); L = v - J; nJ1 = 2 ** (J + 1 + r)
    C = CJ(lam, L)
    main = lam * rho + C / 2 + 0.5 * math.log2(1 + 2 ** (-2 * lam - C))
    if main_only: return main / (LOG2Q - lam)
    eps = 1.0
    for _ in range(60):
        top = (math.log2(L) - log2p + 2 ** -32 + ckappa(eps, v, r, J)) / nJ1
        new = (main + top) / (LOG2Q - lam)
        if abs(new - eps) < 1e-15: break
        eps = new
    return eps

def best(v, r, J, log2p=-130.0, main_only=False):
    b = (9, None)
    for t in range(40, 1400):
        lam = t / 100.0
        e = eps0(lam, v, r, J, log2p, main_only)
        if e < b[0]: b = (e, lam)
    return b

if __name__ == "__main__":
    print("eps_0 * 64 at p = 2^-130 (best lambda in brackets); 'main' = the part that does not depend on p or J+1's size")
    for r in (1, 2):
        print(f"rate 2^-{r}")
        print("  log2 n | " + " | ".join(f"J={J:2d}        " for J in (4, 5, 6, 7, 8, 10)) + " | main (J=5)")
        for ln in (19, 20, 21, 22, 23, 24, 25):
            v = ln - r; row = []
            for J in (4, 5, 6, 7, 8, 10):
                e, lam = best(v, r, J)
                row.append(f"{64*e:5.2f} [{lam:4.2f}]")
            em, _ = best(v, r, 5, main_only=True)
            print(f"  {ln:6d} | " + " | ".join(row) + f" | {64*em:5.2f}")
    print("dependence on p (rate 1/2, n = 2^22, J = 5):")
    for lp in (-64, -100, -130, -160, -256):
        e, lam = best(21, 1, 5, lp)
        print(f"  p = 2^{lp}: eps_0 * 64 = {64*e:.2f}")
    print("few random levels (rate 1/2, n = 2^22): J = v - L")
    for L in (1, 2, 3, 4, 6, 8):
        e, lam = best(21, 1, 21 - L)
        print(f"  L = {L}: eps_0 * 64 = {64*e:.3f} [lambda {lam}]")
