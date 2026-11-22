#!/usr/bin/env python3
"""Note 65: the expansion constant gamma of axiom (W2) for the window graphs priced in the note. Standard library.

E1  Random d-out graph on n points (note 66): for a fixed Z of density phi a point of Z is interior with probability
    at most phi^d, independently, so  P[some Z of z = phi n points has >= gamma z interior points]
    <= C(n, z) C(z, gamma z) phi^(d gamma z).  gamma(d, phi, n) is the least gamma (step 0.001) making this at most
    2^-128 / n (a union over the sizes z as well); n = inf drops the 128 + log2 n bits.
E2  The smallest d a rung can use: the rank asks d >= t - 1; the free configurations ask gamma <= 1/2 (the crude
    bound of note 66) or Phi(gamma rho C(t, 2)) <= g_t(alpha_t) (note 60, Proposition 3.7 read as a threshold: Phi is
    piecewise linear with Phi(C(s, 2)) = s - 1, g_t(a) = t a - 1 + (1 - a)^t; its limit for large t is sqrt(rho gamma)).
E3  Deterministic graphs: Tanner's bound. In a regular undirected graph with normalised second eigenvalue lam, a set
    Z of density phi has at least (1 - phi)(1 - lam^2) / ((1 - phi) + phi lam^2) |Z| points with a neighbour outside.
E4  Pool designs: partners x ^ c, c among p public offsets, d of them a position. A hyperplane holding a share s of
    the pool keeps s^d of its points interior; for p random offsets the largest share is about 1/2 + sqrt(N ln 2 / 2p).
"""
import math


def h2(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log2(x) - (1 - x) * math.log2(1 - x)


def gamma(d, phi, n=None):
    extra = 0.0 if n is None else (128 + math.log2(n)) / (phi * n)
    g = 0.001
    while g < 1 and h2(phi) / phi + h2(g) + extra > d * g * math.log2(1 / phi):
        g += 0.001
    return g


ALPHA = {(1, 4): 0.6354, (1, 5): 0.6133, (1, 8): 0.5777, (2, 4): 0.4257, (2, 5): 0.3996, (2, 8): 0.3546}  # note 61, L1

print("## E1. gamma(d, phi, n) for the random d-out graph\n")
print("| d | phi = 1/2, n = inf | n = 2^20 | n = 2^12 | n = 2^10 | phi = 1/4, n = inf | n = 2^10 |")
print("| --- | --- | --- | --- | --- | --- | --- |")
for d in (3, 4, 5, 6, 7, 8, 10, 12, 16):
    row = [gamma(d, 0.5), gamma(d, 0.5, 2**20), gamma(d, 0.5, 2**12), gamma(d, 0.5, 2**10), gamma(d, 0.25), gamma(d, 0.25, 2**10)]
    print(f"| {d} | " + " | ".join(f"{x:.3f}" for x in row) + " |")

def phi_pl(y):
    s = 1
    while s * (s + 1) // 2 <= y:
        s += 1
    lo, hi = s * (s - 1) // 2, s * (s + 1) // 2
    return s - 1 + (y - lo) / (hi - lo)


def d_min(r, t, a, sharp):
    rho = 2.0**-r
    rhs = t * a - 1 + (1 - a) ** t
    for d in range(2, 40):
        g = gamma(d, rho, 2**20)
        if (phi_pl(g * rho * t * (t - 1) / 2) <= rhs) if sharp else (g <= (0.5 if r == 1 else rho)):
            return d, g


print("\n## E2. The smallest d of a rung (rank d >= t - 1; expansion at density rho)\n")
print("| rate | t | alpha_t | d for the crude bound (gamma <= 1/2 or rho) | d for note 60's bound, its gamma | with the rank: crude, note 60 |")
print("| --- | --- | --- | --- | --- | --- |")
for (r, t), a in ALPHA.items():
    dc, ds = d_min(r, t, a, False), d_min(r, t, a, True)
    print(f"| 1/{1 << r} | {t} | {a} | {dc[0]} | {ds[0]}, {ds[1]:.3f} | {max(dc[0], t - 1)}, {max(ds[0], t - 1)} |")

print("\n## E3. Tanner: interior fraction at most 1 - beta, beta = (1 - phi)(1 - lam^2) / ((1 - phi) + phi lam^2)\n")
print("| graph | degree | lam | gamma at phi = 1/2 | at phi = 1/4 |")
print("| --- | --- | --- | --- | --- |")
tanner = lambda lam, phi: 1 - (1 - phi) * (1 - lam * lam) / ((1 - phi) + phi * lam * lam)
rows = [("Margulis, Gabber-Galil, lam <= 5 sqrt 2 / 8", 8, 5 * math.sqrt(2) / 8)]
rows += [(f"Ramanujan, lam = 2 sqrt(d - 1) / d", d, 2 * math.sqrt(d - 1) / d) for d in (6, 8, 12, 16)]
rows += [(f"Cayley graph of F_2^N on p offsets, weights of the pool code in [p (1 - lam) / 2, p (1 + lam) / 2]", "p", lam) for lam in (0.3, 0.5)]
for name, d, lam in rows:
    print(f"| {name} | {d} | {lam:.3f} | {tanner(lam, 0.5):.3f} | {tanner(lam, 0.25):.3f} |")

print("\n## E4. Pools: the largest hyperplane share of p random offsets in F_2^25, and what it leaves interior\n")
print("| p | share s (estimate) | s^8 | s^12 | bias 2 s - 1 | points of Z holding > 0.65 of their pool neighbours (Chebyshev) |")
print("| --- | --- | --- | --- | --- | --- |")
for p in (32, 64, 128, 256, 512, 4096, 65536):
    s = min(1.0, 0.5 + math.sqrt(25 * math.log(2) / (2 * p)))
    lam = 2 * s - 1
    print(f"| {p} | {s:.3f} | {s**8:.3f} | {s**12:.3f} | {lam:.3f} | {min(1.0, lam * lam * 0.5 / 0.15**2):.3f} |")
