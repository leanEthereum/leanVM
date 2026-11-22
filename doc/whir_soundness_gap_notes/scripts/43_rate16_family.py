#!/usr/bin/env python3
"""The quintic first integral R at rate 1/16 and its sections (Section 6 of 43-low-rate-residuals.md).

D = F_n, n = 4^Np with Np even, word w(x) = x^(n/4) (= x^(1/4) on D), rate 1/16 (k = n/16), c = 1.
E = Y^5 + X Y + X^(n/4+1);   dE = Y0 + X^(n/4) + Y1 (Y0^4 + X);   all n lines of w lie on dE = 0.
For mu = mu0 + mu1 X^j, j = sqrt(n)/4, mu0 in F_n, mu1^4 in F_sqrt(n) \\ 0, put
    z = Tr_{n/4}(mu0^4 X) + Tr_{sqrt(n)/4}(mu1^4 X^(sqrt(n)+1))      (so z^4 + z = (X^n + X) mu^4).
Claim: for exactly one eps in F_4, mu^4 divides z + eps, and then P = X^(n/4) + (z + eps)/mu is a polynomial of
degree n/16 - 3 sqrt(n)/16 < n/16 that agrees with w on exactly n/4 - 3 sqrt(n)/4 points, with
P^4 + X = (z + eps)/mu^4 dividing X^n + X, P' = mu^3 and d/dX E(X, P) = 0.  (mu, z) and (om mu, om z), om in F_4*,
give the same P, so the word has (sqrt(n) - 1) n / 3 such codewords.

The script checks the claim for all (mu0, mu1) at n = 256 (1280 codewords at agreement 52, degree 13 < 16) and for a
sample at n = 4096 (agreement 976 = 0.2383 n, degree 244 < 256; a_1(1/16) n = 893.3), and counts distinct P.
Run: python3 43_rate16_family.py [samples at n = 4096, default 12]    (about 1 minute)
"""
import random
import sys
import importlib

sys.path.insert(0, sys.path[0] or ".")
gfm = importlib.import_module("43_gf")


def run(m, pairs=None, seed=5):
    F = gfm.GF(m)
    n = F.q
    rt = 1 << (m // 2)          # sqrt(n)
    assert (m // 2) % 2 == 0
    j = rt // 4
    F4 = [x for x in range(n) if F.pow(x, 4) == x]
    assert len(F4) == 4
    sub = [x for x in range(1, n) if F.pow(x, rt) == x]          # F_sqrt(n)^*
    mu1s = [F.pow(a, n // 4) for a in sub]                        # 4th roots
    rnd = random.Random(seed)
    if pairs is None:
        todo = [(mu0, mu1) for mu1 in mu1s for mu0 in range(n)]
    else:
        todo = [(rnd.randrange(n), rnd.choice(mu1s)) for _ in range(pairs)]
    Ps = set()
    ag_expect = n // 4 - 3 * rt // 4
    for (mu0, mu1) in todo:
        z = [0] * (n // 4 + j + 1)
        c0, e = F.pow(mu0, 4), 1
        for _ in range(m // 2):                # Tr_{n/4}(mu0^4 X)
            z[e] ^= c0
            c0, e = F.pow(c0, 4), e * 4
        c1, e = F.pow(mu1, 4), rt + 1
        for _ in range(m // 4):                # Tr_{sqrt(n)/4}(mu1^4 X^(sqrt(n)+1))
            z[e] ^= c1
            c1, e = F.pow(c1, 4), (e * 4)
        mu = [mu0] + [0] * (j - 1) + [mu1]
        mu4 = F.ppow(mu, 4)
        good = []
        for eps in F4:
            ze = list(z)
            ze[0] ^= eps
            M, r = F.pdivmod(ze, mu4)
            if not r:
                good.append((eps, ze, M))
        assert len(good) == 1, "exactly one eps"
        eps, ze, M = good[0]
        q, r = F.pdivmod(ze, mu)
        assert not r
        P = F.padd(q, [0] * (n // 4) + [1])
        assert F.deg(M) == ag_expect and F.deg(P) == ag_expect // 4 and F.deg(P) < n // 16
        assert F.padd(F.ppow(P, 4), [0, 1]) == M, "P^4 + X = (z + eps)/mu^4"
        assert F.pderiv(P) == F.ppow(mu, 3), "P' = mu^3"
        Ps.add(tuple(P))
        if pairs is not None or len(Ps) <= 40:
            # agreement with w on D, section property, M | X^n + X
            ag = sum(1 for x in range(n) if F.peval(P, x) == F.pow(x, n // 4))
            assert ag == ag_expect, (ag, ag_expect)
            EP = F.padd(F.padd(F.ppow(P, 5), [0] + P), [0] * (n // 4 + 1) + [1])
            assert F.is_even(EP), "E(X,P) in F[X^2]"
            assert not F.pdivmod([0, 1] + [0] * (n - 2) + [1], M)[1]
    return n, len(todo), len(Ps), ag_expect


if __name__ == "__main__":
    n, t, d, ag = run(8)
    print(f"n = {n}: all {t} pairs (mu0, mu1) give a polynomial section; {d} distinct P "
          f"(= (sqrt(n)-1) n/3 = {(16 - 1) * n // 3}), degree {ag // 4} < {n // 16}, agreement {ag} = {ag / n:.4f} n")
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    n, t, d, ag = run(12, pairs=s)
    print(f"n = {n}: {t} random pairs, {d} distinct P, degree {ag // 4} < {n // 16}, agreement {ag} = {ag / n:.4f} n "
          f"> a_1(1/16) n = {0.21810 * n:.1f}; predicted number of codewords (sqrt(n)-1) n/3 = {(64 - 1) * n // 3}")
