#!/usr/bin/env python3
"""Note 84: arithmetic of the proof of Theorem 5.1 (standard library).
 (1) Kraft equality of the prefix code (Lemma 4.1) by brute-force enumeration of all prefix labels
     on tiny trees;
 (2) the identity of Steps 1, 2 and 4 with the Abel summation, on random profiles:
     sum_j omega_j w(pi_j) = u_{J+1} n_J log2(1 + |D| 2^-lam'_J) + lam (y_J + sum u_{i+1} d_i) + eta H + n C_J / 2
     (the term lam y_J is the one that the nullity budget of Step 3 cancels)."""
import itertools, math, random

def mult(lam, eta, nd, J, v):
    """lists indexed by level i = J..v-1: lam_i, eta_i, c_i, c'_i; and C_J, C'_J"""
    C = Cp = 0.0
    out = {}
    for i in range(v - 1, J - 1, -1):
        B = 0.5 * (C - Cp)
        li, ei = lam + B, eta - B
        x, z = 2.0 ** -li, 2.0 ** -ei
        c = math.log2(1 + 2 * nd * x + nd * (nd - 1) * x * x)
        cp = math.log2(1 + 2 * z * (1 + (nd - 1) * x))
        out[i] = (li, ei, c, cp)
        C += c; Cp += cp
    return out, C, Cp

def kraft(r, J, v, nd, lam, eta):
    m, C, Cp = mult(lam, eta, nd, J, v)
    lamJ = 2 * lam + C - Cp
    nJ = 2 ** (J + r)
    total = 0.0
    count = 0
    def level(i, Y, w):
        # Y: dict node -> direction at level i
        nonlocal total, count
        if i == v:
            total += 2.0 ** -w; count += 1; return
        li, ei, c, cp = m[i]
        opts = []
        for p in range(2 ** (i + r)):
            if p in Y:
                d = Y[p]
                o = [({2 * p: d, 2 * p + 1: d}, 0, 0), ({2 * p: d}, 0, 1), ({2 * p + 1: d}, 0, 1)]
                for mu in range(nd):
                    if mu != d:
                        o.append(({2 * p: d, 2 * p + 1: mu}, 1, 1)); o.append(({2 * p: mu, 2 * p + 1: d}, 1, 1))
            else:
                o = [({}, 0, 0)]
                for mu in range(nd):
                    o.append(({2 * p: mu}, 1, 0)); o.append(({2 * p + 1: mu}, 1, 0))
                    for nu in range(nd):
                        if nu != mu: o.append(({2 * p: mu, 2 * p + 1: nu}, 2, 0))
            opts.append(o)
        base = (2 ** (i + r) - len(Y)) * c + len(Y) * cp
        for combo in itertools.product(*opts):
            Yn = {}; d = h = 0
            for ch, dd, hh in combo:
                Yn.update(ch); d += dd; h += hh
            level(i + 1, Yn, w + base + li * d + ei * h)
    if J == 0:
        level(0, {}, 0.0)
    else:
        for dirs in itertools.product(range(nd + 1), repeat=nJ):
            Y = {p: d - 1 for p, d in enumerate(dirs) if d > 0}
            level(J, Y, lamJ * len(Y) + nJ * math.log2(1 + nd * 2.0 ** -lamJ))
    return total, count

def identity(rng, trials=2000):
    worst = 0.0
    for _ in range(trials):
        r = rng.randint(1, 3); J = rng.randint(0, 2); v = J + rng.randint(1, 5); nd = rng.choice([1, 3, 6, 10])
        lam = rng.uniform(0.5, 12); eta = rng.uniform(1, 30)
        m, C, Cp = mult(lam, eta, nd, J, v)
        lamJ = 2 * lam + C - Cp
        n = 2 ** (v + r); u = lambda j: 2.0 ** (v - j) if j <= v else 0.0
        nJ = 2 ** (J + r)
        Ysz = rng.randint(0, nJ) if J > 0 else 0
        prof = []; sizes = [Ysz]
        for i in range(J, v):
            y = sizes[-1]
            h = rng.randint(0, y)
            dmax = (2 ** (i + r) - y) * 2 + h
            d = rng.randint(0, dmax)
            prof.append((d, h)); sizes.append(2 * y - h + d)
        topw = (lamJ * Ysz + nJ * math.log2(1 + nd * 2.0 ** -lamJ)) if J > 0 else 0.0
        lhs = 0.0; w = topw
        for j in range(J, v):
            li, ei, c, cp = m[j]
            d, h = prof[j - J]; y = sizes[j - J]
            w += li * d + ei * h + (2 ** (j + r) - y) * c + y * cp
            lhs += (u(j + 1) - u(j + 2)) * w
        rhs = (u(J + 1) * nJ * math.log2(1 + nd * 2.0 ** -lamJ) if J > 0 else 0.0) + 0.5 * n * C
        rhs += sum(u(i + 1) * (lam * prof[i - J][0] + eta * prof[i - J][1]) for i in range(J, v))
        rhs += lam * u(J) * Ysz  # u_{J+1} lam'_J |Y_J| - y_J B_J = lam y_J; Step 3's budget then removes it (Step 4)
        worst = max(worst, abs(lhs - rhs) / max(1.0, abs(rhs)))
    return worst

if __name__ == "__main__":
    for (r, J, v, nd, lam, eta) in ((1, 0, 2, 3, 1.3, 2.0), (1, 0, 2, 2, 0.7, 5.0), (1, 1, 2, 3, 2.1, 3.0), (1, 1, 2, 1, 1.0, 4.0), (1, 0, 2, 1, 0.5, 1.0)):
        tot, cnt = kraft(r, J, v, nd, lam, eta)
        print(f"Kraft: r={r} J={J} v={v} |Delta|={nd} lambda={lam} eta={eta}: {cnt} prefix labels, sum 2^-w = {tot:.12f}")
    print("identity of Steps 1, 2, 4: largest relative error on 2000 random profiles:", identity(random.Random(84)))
