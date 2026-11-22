# Referee 75: independent evaluation of eps_0 of note 73, Theorem 5.1, from the formulas of its Sections 4 and 5 (written from the
# note's text, not from 73_eps0.py), for a field of 2^b elements (b = 64 for the table; b = 8 for the toy check of 75_toy.c).
import math, sys

def lbinom(a, b):
    return (math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)) / math.log(2)

def eps0(r, v, J, log2_inv_p, lam, b=64):
    L = v - J; n = 2 ** (v + r); rho = 2.0 ** -r; nJ1 = 2 ** (J + 1 + r)
    C = 0.0                                   # C_v = 0, then C_i = C_{i+1} + log2(1 + 2^(1 - lam - C_{i+1}/2)), i = v-1 .. J
    for i in range(v - 1, J - 1, -1):
        C += math.log2(1 + 2 ** (1 - lam - C / 2))
    M = lam * rho + C / 2 + 0.5 * math.log2(1 + 2 ** (-2 * lam - C))
    log2chi = -L * math.log2(1 - n / 2.0 ** b)
    def ckappa(eps):
        s = 0.0
        for j in range(J, v):
            w = 2.0 ** -(j - J + 1) if j <= v - 2 else 2.0 ** -(L - 1)
            G = math.floor(eps * 2 ** (j + 1 + r))
            s += w * lbinom(G + j - J, j - J)
        return s
    def Psi(eps):
        return (M + (math.log2(L) + log2_inv_p + log2chi + ckappa(eps)) / nJ1) / (b - lam)
    e = 1.0
    for _ in range(200):
        e2 = Psi(e)
        if e2 == e: break
        e = e2
    return e, M / (b - lam)

def best(r, v, J, log2_inv_p, b=64, step=0.01):
    out = (9.0, 0.0, 0.0)
    lam = step
    while lam < min(b, 12):
        e, main = eps0(r, v, J, log2_inv_p, lam, b)
        if e < out[0]: out = (e, lam, main)
        lam += step
    return out

if __name__ == "__main__":
    print("64 eps_0 at p = 2^-130, best lambda on a grid of step 0.01 (note 73's table value in brackets)")
    ref = {(1, 19, 4): 5.34, (1, 25, 4): 5.68, (2, 19, 4): 3.06, (2, 25, 4): 3.24, (1, 22, 5): 4.33, (1, 22, 8): 3.14, (2, 22, 8): 1.92, (1, 19, 10): 2.62, (2, 25, 10): 1.90}
    for (r, lg, J), val in ref.items():
        e, lam, main = best(r, lg - r, J, 130)
        print(f"  rate 2^-{r}, n = 2^{lg}, J = {J}: 64 eps_0 = {64 * e:.3f} at lambda = {lam:.2f} [{val}]   main term 64 M/(64 - lambda) = {64 * main:.3f}")
    print("toy sizes, field of 2^8 elements: eps_0 n as a function of p (the theorem: Pr[E >= eps_0 n] <= p)")
    for (r, v, J) in ((1, 3, 1), (1, 3, 2), (2, 2, 1), (1, 4, 2), (1, 3, 0)):
        n = 2 ** (v + r)
        line = []
        for lp in (1, 2, 3, 5, 7, 10, 13, 17):
            e, lam, _ = best(r, v, J, lp, b=8)
            line.append(f"p=2^-{lp}: {e * n:.2f}")
        print(f"  r={r} v={v} J={J} (n={n}, k={2 ** v}): " + "; ".join(line))

def pstar(r, v, J, s, b=8):
    """largest p (as log2(1/p), smallest value) with eps_0(p) n <= s for some lambda: the theorem then says Pr[E >= s] <= p"""
    n = 2 ** (v + r); lo, hi = 0.0, 200.0
    if best(r, v, J, lo, b, 0.02)[0] * n > s: return None
    while hi - lo > 0.01:
        mid = (lo + hi) / 2
        if best(r, v, J, mid, b, 0.02)[0] * n <= s: lo = mid
        else: hi = mid
    return lo

if __name__ == "__main__":
    print("toy sizes: for each integer s, the theorem's bound on Pr[E >= s] (log2), from the largest p with eps_0(p) n <= s")
    for (r, v, J) in ((1, 3, 1), (1, 3, 2), (2, 2, 1)):
        out = []
        for s in range(1, 9):
            lp = pstar(r, v, J, s)
            out.append(f"s={s}: " + ("no bound" if lp is None else f"2^-{lp:.2f}"))
        print(f"  r={r} v={v} J={J}: " + "; ".join(out))
