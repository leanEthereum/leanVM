#!/usr/bin/python3
# Referee 87: independent evaluation of eps_Delta of note 84, Theorem 5.1, written from the
# formulas of Sections 4 and 5 of the note only (not from 84_eps.py).
import math, sys

def lg_binom(a, b):
    # log2 of binomial(a, b)
    if b < 0 or b > a:
        return float("-inf")
    return (math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)) / math.log(2)

def eps(lam, r, v, J, log2_inv_p, L, nD, Q=64.0, a=0, log2chi=2.0 ** -31):
    """eps_Delta(lam; r, v, J, p, a); Q is the number of bits of the field (64 in the note)."""
    rho = 2.0 ** -r
    n = 2 ** (v + r)
    eta = (Q - lam) / 2
    C = 0.0
    Cp = 0.0
    for i in range(v - 1, J - 1, -1):
        B = (C - Cp) / 2
        lam_i = lam + B
        eta_i = eta - B
        x = 2.0 ** -lam_i
        c = math.log2(1 + 2 * nD * x + nD * (nD - 1) * x * x)
        cp = math.log2(1 + 2.0 ** (1 - eta_i) * (1 + (nD - 1) * x))
        C += c
        Cp += cp
    M = lam * L * rho + C / 2
    if J > 0:
        M += 0.5 * math.log2(1 + nD * 2.0 ** (-2 * lam - C + Cp))
    Lev = v - J
    nJ1 = 2 ** (J + 1 + r)
    nJ = 2 ** (J + r)
    u = lambda j: 2 ** (v - j) if j <= v else 0
    def ckappa(eh):
        s = 0.0
        for j in range(J, v):
            om = u(j + 1) - u(j + 2)
            nj1 = 2 ** (j + 1 + r)
            G = math.floor(eh * nj1)
            s += om / u(J + 1) * lg_binom(G + j - J, j - J)
        return s
    def Psi(eh):
        return M + (math.log2(Lev) + log2_inv_p + log2chi + ckappa(eh)) / nJ1
    eh = float(Lev)
    for _ in range(200):
        new = 2 / (Q - lam) * (Psi(eh) + (Q + lam) * a / (2 * nJ))
        if abs(new - eh) < 1e-15:
            eh = new
            break
        eh = new
    return Psi(eh) / (Q - lam) + Q / (Q - lam) * a / nJ, M / (Q - lam), Cp

def best(r, v, J, log2_inv_p, t, Q=64.0, step=0.05, lo=0.05, hi=None, log2chi=2.0 ** -31):
    L = t - 1
    nD = t * (t - 1) // 2
    hi = Q - step if hi is None else hi
    bestv = None
    lam = lo
    while lam < hi:
        e, m, cp = eps(lam, r, v, J, log2_inv_p, L, nD, Q=Q, log2chi=log2chi)
        if bestv is None or e < bestv[0]:
            bestv = (e, lam, m, cp)
        lam += step
    return bestv

if __name__ == "__main__":
    # entries of the table of Section 7 (p = 2^-130), claimed value n=2^20 / n=2^24
    cases = [
        (3, 0, 2, "0.168/0.170"), (3, 0, 8, "0.276/0.281"), (3, 2, 3, "0.076/0.078"),
        (4, 1, 4, "0.073/0.075"), (4, 0, 16, "0.240/0.245"),
        (7, 0, 8, "0.0255/0.0261"), (7, 0, 64, "0.176/0.182"), (7, 2, 3, "0.0062/0.0064"),
        (10, 0, 64, "0.0278/0.0288"), (10, 1, 16, "0.0061/0.0063"), (10, 0, 128, "0.058/0.060"),
        (10, 0, 376, "0.184/0.190"),
    ]
    print("rate J t | eps(n=2^20) eps(n=2^24) | lam | main/((t-1)rho) | first-level*n_{J+1} | C'_J | claimed")
    for r, J, t, claim in cases:
        out = []
        for lgn in (20, 24):
            e, lam, m, cp = best(r, lgn - r, J, 130, t)
            out.append((e, lam, m, cp))
        rho = 2.0 ** -r
        e0, lam0, m0, cp0 = out[0]
        print("2^-%d J=%d t=%d | %.4f %.4f | lam %.2f %.2f | %.3f %.3f | %.2f %.2f | %.1e | %s" % (
            r, J, t, out[0][0], out[1][0], out[0][1], out[1][1], out[0][2] / ((t - 1) * rho), out[1][2] / ((t - 1) * rho),
            (out[0][0] - out[0][2]) * 2 ** (J + 1 + r), (out[1][0] - out[1][2]) * 2 ** (J + 1 + r), max(out[0][3], out[1][3]), claim))
    # L = 1 check against note 73's numbers quoted in note 84 Section 7 (64 eps = 5.36, 5.69, 3.07, 3.25)
    for r, lgn in ((1, 19), (1, 25), (2, 19), (2, 25)):
        e, lam, m, cp = best(r, lgn - r, 4, 130, 2)
        print("L=1 check rate 2^-%d n=2^%d J=4: 64 eps = %.3f (lam %.2f)" % (r, lgn, 64 * e, lam))
    # toy version of Section 9.1: 8-bit field, k=4, n=16, J=0, t=3, chi exact
    Q = 8.0
    n = 16
    chi = -2 * math.log2(1 - 2 * n / 256.0)
    for pr, claim in ((0.5, 6.56), (0.1, 7.17), (0.01, 8.05)):
        e, lam, m, cp = best(2, 2, 0, -math.log2(pr), 3, Q=Q, step=0.01, lo=0.01, hi=7.99, log2chi=chi)
        print("toy q=2^8 k=4 n=16 t=3 failure prob %.2f: eps*n = %.3f (lam %.2f) claimed %.2f" % (pr, e * n, lam, claim))
