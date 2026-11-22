#!/usr/bin/env python3
"""Note 73: arithmetic checks of the proof of Theorem 5.1 (no field arithmetic).
(1) Kraft equality for prefix labels, by enumeration on a tiny tree.
(2) The identity sum_j omega_j w(pi_j) = lam*sum_i u_{i+1} d_i + lam*u_J*z_J + C_J*n/2 + (n/2)*log2(1+2^(-2lam-C_J))
    on random chain profiles, and Abel summation E_v = sum_j omega_j Gamma_j.
"""
import itertools, math, random

def multipliers(lam, J, v):
    C = {v: 0.0}; c = {}; lm = {}
    for i in range(v - 1, J - 1, -1):
        c[i] = math.log2(1 + 2 ** (1 - lam - C[i + 1] / 2)); C[i] = C[i + 1] + c[i]; lm[i] = lam + C[i + 1] / 2
    return C, c, lm

def kraft(lam, r, J, v):
    C, c, lm = multipliers(lam, J, v); lJ = 2 * lam + C[J]; nJ = 2 ** (J + r)
    def rec(i, Z, nodes):
        # Z: frozenset of positions at level i (of 'nodes' positions); returns sum over extensions down to level v-1 of 2^-w
        if i == v: return 1.0
        free = [p for p in range(nodes) if p not in Z]; tot = 0.0
        for assign in itertools.product((None, 0, 1), repeat=len(free)):
            D = [(p, a) for p, a in zip(free, assign) if a is not None]
            Zn = frozenset([2 * p for p in Z] + [2 * p + 1 for p in Z] + [2 * p + a for p, a in D])
            tot += 2 ** -(lm[i] * len(D) + len(free) * c[i]) * rec(i + 1, Zn, 2 * nodes)
        return tot
    tot = 0.0
    for m in range(nJ + 1):
        for Z in itertools.combinations(range(nJ), m):
            tot += 2 ** -(lJ * m + nJ * math.log2(1 + 2 ** -lJ)) * rec(J, frozenset(Z), nJ)
    return tot

def identity(trials=2000):
    worst = 0.0
    for _ in range(trials):
        r = random.choice((1, 2)); J = random.randint(0, 4); v = J + random.randint(1, 8); lam = random.uniform(0.2, 8)
        n = 2 ** (v + r); k = 2 ** v
        C, c, lm = multipliers(lam, J, v); lJ = 2 * lam + C[J]
        u = lambda j: 2 ** (v - j) if j <= v else 0
        nJ = 2 ** (J + r); zJ = random.randint(0, nJ)
        size = zJ; d = {}; G = {}
        for i in range(J, v):
            ni = 2 ** (i + r); d[i] = random.randint(0, ni - size); G[i] = random.randint(0, 5); size = 2 * size + d[i]
        # code lengths
        lhs = 0.0; Ev = 0.0; EvAbel = 0.0; Gam = 0; wj = lJ * zJ + nJ * math.log2(1 + 2 ** -lJ); size = zJ
        for j in range(J, v):
            nj = 2 ** (j + r); wj += lm[j] * d[j] + (nj - size) * c[j]; size = 2 * size + d[j]
            om = u(j + 1) - (u(j + 2) if j + 2 <= v else 0)
            lhs += om * wj; Gam += G[j]; EvAbel += om * Gam; Ev += u(j + 1) * G[j]
        rhs = lam * sum(u(i + 1) * d[i] for i in range(J, v)) + lam * u(J) * zJ + C[J] * n / 2 + (n / 2) * math.log2(1 + 2 ** (-2 * lam - C[J]))
        worst = max(worst, abs(lhs - rhs) / max(1.0, abs(rhs)), abs(Ev - EvAbel))
    return worst

if __name__ == "__main__":
    random.seed(73)
    for (lam, r, J, v) in ((1.0, 1, 0, 2), (2.5, 1, 0, 2), (0.7, 0, 1, 3), (3.0, 0, 0, 3)):
        print(f"Kraft sum, lambda = {lam}, r = {r}, J = {J}, v = {v}: {kraft(lam, r, J, v):.12f}")
    print(f"identity of Steps 1 to 4 and Abel summation, largest relative error over 2000 random profiles: {identity():.2e}")
