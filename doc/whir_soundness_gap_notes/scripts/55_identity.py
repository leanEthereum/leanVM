#!/usr/bin/env python3
"""55_identity.py: referee tests of note 53, Sections 1, 2.2, 2.4 (Proposition 2.5) and 3.3. Own code (55_lib.py).

A. Proposition 2.2 on random potentials E_Y = sum_i e_{2i+1} Y^{2i} (K = 1, 2, 3) and random P, Q, polynomial and
   rational: (eps_P eps_Q)' = sum_{i<j} mu_ij^2 (P^2i Q^2j + P^2j Q^2i), and for K = 2 the closed form
   ((P + Q)(mu01 + mu02 (P + Q) + mu12 P Q))^2, with mu_ij = sqrt((e_{2i+1} e_{2j+1})').
B. Lemma 1.1: the section equation (S) on random E (odd part of E(X, P) equals P ^ eps_P + E_0^1(tau, P^2)); case (I):
   for a random polynomial centre psi, E - (Y + psi) E_Y has coefficients in F[X^2] and psi is a section; case (II):
   E_Y = rho(X) q(X^2, Y^2) gives eps_P = rho times a square for random P.
C. Proposition 2.5: quintics with E_Y in m^3 at every received point; mu02 = mu12 y, mu01 = mu12 y^2 on D.
D. Section 3.3: S_1 = V + R, S_2 = (c + V) + R, V a plane: the difference is in Gamma_inf(6) and
   deg(Lambda_S1 + Lambda_S2) = p - 4.
E. The 11/16 family of note 45 (closed form quoted): the statements of note 53 about its centre, minors and word.
Run: python3 55_identity.py
"""
import importlib
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("55_lib")


def split(F, p):
    """p = p0(X^2) + X p1(X^2) as polynomials in X (even exponents only)."""
    p0 = F.trim([c if i % 2 == 0 else 0 for i, c in enumerate(p)])
    p1 = F.trim([p[i + 1] if i % 2 == 0 and i + 1 < len(p) else 0 for i in range(len(p))])
    return p0, p1


def wedge(F, f, g):
    return F.pderiv(F.pmul(f, g))


def eps(F, es, P):
    """sum_i es[i] P^(2i)."""
    r = []
    P2 = F.pmul(P, P)
    pw = [1]
    for e in es:
        r = F.padd(r, F.pmul(e, pw))
        pw = F.pmul(pw, P2)
    return r


def minors(F, es):
    mu = {}
    for i in range(len(es)):
        for j in range(i + 1, len(es)):
            d = F.pderiv(F.pmul(es[i], es[j]))
            assert F.is_square_poly(d)
            mu[(i, j)] = F.psqrt(d)
    return mu


def test_A(F, rnd, trials=60):
    ok_gen = ok_quintic = ok_rat = 0
    nq = 0
    for t in range(trials):
        K = 1 + t % 3
        es = [F.rand_poly(rnd, rnd.randrange(0, 9), exact=False) for _ in range(K + 1)]
        mu = minors(F, es)
        P = F.rand_poly(rnd, rnd.randrange(0, 6), exact=False)
        Q = F.rand_poly(rnd, rnd.randrange(0, 6), exact=False)
        lhs = F.pderiv(F.pmul(eps(F, es, P), eps(F, es, Q)))
        rhs = []
        for (i, j), m in mu.items():
            a = F.pmul(F.ppow(P, 2 * i), F.ppow(Q, 2 * j))
            b = F.pmul(F.ppow(P, 2 * j), F.ppow(Q, 2 * i))
            rhs = F.padd(rhs, F.pmul(F.pmul(m, m), F.padd(a, b)))
        ok_gen += lhs == rhs
        if K == 2:
            nq += 1
            B = F.padd(F.padd(mu[(0, 1)], F.pmul(mu[(0, 2)], F.padd(P, Q))), F.pmul(mu[(1, 2)], F.pmul(P, Q)))
            sq = F.pmul(F.padd(P, Q), B)
            ok_quintic += lhs == F.pmul(sq, sq)
            # rational P = Pn / d, Q = Qn / d (common denominator d): eps_P = eps_num / d^4, and
            # (eps_P eps_Q)' = (num_P num_Q)' / d^8; B(P, Q) = Bnum / d^2, (P + Q) = (Pn + Qn) / d
            d = F.rand_poly(rnd, 2)
            Pn, Qn = F.rand_poly(rnd, 4, exact=False), F.rand_poly(rnd, 3, exact=False)
            d2 = F.pmul(d, d)
            d4 = F.pmul(d2, d2)

            def num(Pn):
                return F.padd(F.padd(F.pmul(es[0], d4), F.pmul(es[1], F.pmul(F.pmul(Pn, Pn), d2))),
                              F.pmul(es[2], F.ppow(Pn, 4)))
            lhs_r = F.pderiv(F.pmul(num(Pn), num(Qn)))                 # times d^-8
            Bn = F.padd(F.padd(F.pmul(mu[(0, 1)], d2), F.pmul(mu[(0, 2)], F.pmul(F.padd(Pn, Qn), d))),
                        F.pmul(mu[(1, 2)], F.pmul(Pn, Qn)))            # times d^-2
            sqr = F.pmul(F.padd(Pn, Qn), Bn)                           # times d^-3
            # ((P+Q) B)^2 = sqr^2 d^-6, so lhs_r = sqr^2 d^2
            ok_rat += lhs_r == F.pmul(F.pmul(sqr, sqr), d2)
    print(f"A. GF(2^{F.m}): general identity (K = 1, 2, 3) {ok_gen}/{trials}; quintic closed form {ok_quintic}/{nq}; "
          f"quintic, rational P and Q {ok_rat}/{nq}")
    return ok_gen == trials and ok_quintic == nq and ok_rat == nq


def test_B(F, rnd, trials=30):
    okS = okI = okII = 0
    for _ in range(trials):
        # random E = sum_k E_k(X) Y^k, k <= 5
        Ek = [F.rand_poly(rnd, rnd.randrange(0, 7), exact=False) for _ in range(6)]
        P = F.rand_poly(rnd, 4, exact=False)
        EP = []
        pw = [1]
        for c in Ek:
            EP = F.padd(EP, F.pmul(c, pw))
            pw = F.pmul(pw, P)
        es = [Ek[1], Ek[3], Ek[5]]                                    # E_1(X, Z) = sum es[i] Z^i
        e0 = [Ek[0], Ek[2], Ek[4]]                                    # E_0(X, Z)
        P2 = F.pmul(P, P)
        E01 = []
        pw = [1]
        for c in e0:
            E01 = F.padd(E01, F.pmul(F.pderiv(c), pw))                # (c P^2i)' = c' P^2i
            pw = F.pmul(pw, P2)
        okS += F.pderiv(EP) == F.padd(wedge(F, P, eps(F, es, P)), E01)
        # case (I) with a polynomial centre: c_i = (psi e_i)', E = sum_i (e_i Y^(2i+1) + X c_i Y^(2i)).
        # Then E - (Y + psi) E_Y = sum_i (X c_i + psi e_i) Y^(2i) has coefficients in F[X^2], and psi is a section:
        # G(X, psi, psi') = sum_i (c_i + e_i' psi + e_i psi') psi^(2i) = 0.
        psi = F.rand_poly(rnd, 5)
        cs = [F.pderiv(F.pmul(psi, e)) for e in es]
        inF2 = all(F.is_square_poly(F.padd(F.pmul([0, 1], c), F.pmul(psi, e))) for c, e in zip(cs, es))
        Gpsi = []
        pw = [1]
        psi2 = F.pmul(psi, psi)
        for c, e in zip(cs, es):
            term = F.padd(F.padd(c, F.pmul(F.pderiv(e), psi)), F.pmul(e, F.pderiv(psi)))
            Gpsi = F.padd(Gpsi, F.pmul(term, pw))
            pw = F.pmul(pw, psi2)
        okI += inF2 and Gpsi == []
        # case (II): E_Y = rho q(X^2, Y^2)
        rho = F.rand_poly(rnd, 5)
        qs = [F.psqr(F.rand_poly(rnd, 3, exact=False)) for _ in range(3)]   # coefficients in F[X^2]
        esII = [F.pmul(rho, q) for q in qs]
        e = eps(F, esII, P)
        if e:
            quo = F.pdiv_exact(e, rho)
            okII += F.is_square_poly(quo)
        else:
            okII += 1
    print(f"B. section equation (S) {okS}/{trials}; case (I) E = (Y + psi) E_Y mod F[X^2][Y^2] and psi a section {okI}/{trials}; "
          f"case (II) eps_P / rho a square {okII}/{trials}")
    return okS == okI == okII == trials


def interpolate(F, xs, ys):
    """Lagrange interpolation."""
    Lall = F.locator(xs)
    res = []
    for x, y in zip(xs, ys):
        q = F.pdiv_exact(Lall, [x, 1])
        res = F.padd(res, F.pscale(q, F.mul(y, F.inv(F.peval(q, x)))))
    return res


def test_C(F, rnd, trials=10):
    ok = 0
    tot = 0
    for _ in range(trials):
        n = 8
        D = rnd.sample(range(F.q), n)
        y = [rnd.randrange(F.q) for _ in D]
        yh = interpolate(F, D, y)
        LD = F.locator(D)
        e5 = F.rand_poly(rnd, 5)
        e3 = F.pmul(LD, F.rand_poly(rnd, 4))
        y2 = F.pmul(yh, yh)
        e1 = F.padd(F.padd(F.pmul(e3, y2), F.pmul(e5, F.pmul(y2, y2))), F.pmul(F.ppow(LD, 3), F.rand_poly(rnd, 3)))
        es = [e1, e3, e5]
        mu = minors(F, es)
        for a, ya in zip(D, y):
            # E_Y in m^3 at (a, ya): eps_{ya} vanishes to order 3 and e3(a) = 0
            assert F.mult_at(eps(F, es, [ya] if ya else []), a) >= 3 and F.peval(e3, a) == 0
            m01, m02, m12 = (F.peval(mu[k], a) for k in ((0, 1), (0, 2), (1, 2)))
            tot += 1
            ok += (m02 == F.mul(m12, ya)) and (m01 == F.mul(m12, F.mul(ya, ya))) and \
                  (F.peval(e1, a) == F.mul(F.peval(e5, a), F.pow(ya, 4)))
    print(f"C. Proposition 2.5 (contact 4): mu02 = mu12 y, mu01 = mu12 y^2, e1 = e5 y^4 at {ok}/{tot} received points")
    return ok == tot


def test_D(F, rnd):
    res = True
    for N in (5, 6):
        basis = F.rand_basis(rnd, N)
        D = F.span(basis)
        V = F.span(basis[:2])
        c = basis[2]
        cV = [c ^ v for v in V]
        rest = [a for a in D if a not in V and a not in cV]
        R = rnd.sample(rest, 20)
        S1, S2 = V + R, cV + R
        T = V + cV
        ps = []
        for k in range(0, 8):
            s = 0
            for a in T:
                s ^= F.pow(a, k)
            ps.append(s)
        d = F.padd(F.locator(S1), F.locator(S2))
        p = len(S1)
        LV = F.locator(V)
        print(f"D. N = {N}: |S_i| = {p}, power sums p_0..p_7 of S_1 xor S_2: {ps}; deg(Lambda_S1 + Lambda_S2) = "
              f"{F.deg(d)} (= p - 4: {F.deg(d) == p - 4}); equals L_V(c) Lambda_R: "
              f"{d == F.pscale(F.locator(R), F.peval(LV, c))}")
        res &= all(v == 0 for v in ps[:7]) and F.deg(d) == p - 4
    return res


def test_E(F, N, rnd):
    """The 11/16 family (note 45, Theorem 6; quoted): D a subspace, L_D = X^n + eps X^(n/2) + M, psi = X^(3n/4-1),
    E_Y = X^3 M (Y - psi)^4 + X (eps M + e_{N-2}^2) L_D (Y - psi)^2 + (M / X) L_D^3, E = (Y - psi) E_Y.
    Statements of note 53 about it: polynomial centre with p_inf - Delta = n/4 (Delta = n/2 - 1); the minors drop by
    n/4, n/4, n/2 (Proposition 2.4 (2)); the word is mu02 / mu12 on D (Proposition 2.5); eps_psi = (M / X) L_D^3,
    whose roots outside D are the n/4 - 1 nonzero roots of M."""
    n = 1 << N
    D = F.span(F.rand_basis(rnd, N))
    LD = F.locator(D)
    epsc = LD[n // 2]
    M = F.trim(LD[:n // 2])
    assert F.deg(M) == n // 4 and M[0] == 0
    eN2 = M[n // 4]
    psi = [0] * (3 * n // 4 - 1) + [1]
    e5 = F.pmul([0, 0, 0, 1], M)
    e3 = F.pmul(F.pmul([0, 1], F.padd(F.pscale(M, epsc), [F.mul(eN2, eN2)])), LD)
    nu = M[1:]
    psi2 = F.pmul(psi, psi)
    e1 = F.padd(F.padd(F.pmul(e5, F.pmul(psi2, psi2)), F.pmul(e3, psi2)), F.pmul(nu, F.ppow(LD, 3)))
    es = [e1, e3, e5]
    Delta = n // 2 - 1
    cs = [F.pderiv(F.pmul(psi, e)) for e in es]
    W = max([F.deg(e) + (2 * i + 1) * Delta for i, e in enumerate(es)] + [F.deg(c) + 2 * i * Delta for i, c in enumerate(cs) if c])
    mu = minors(F, es)
    drops = []
    for (i, j), v in sorted(mu.items()):
        gen = (W - (2 * i + 1) * Delta) + (W - (2 * j + 1) * Delta)
        drops.append(gen - 2 * F.deg(v) if v else None)
    okc = okw = 0
    for a in D:
        ya = F.pow(a, 3 * n // 4 - 1)
        okc += F.peval(e3, a) == 0 and F.mult_at(eps(F, es, [ya] if ya else []), a) >= 3
        m01, m02, m12 = (F.peval(mu[k], a) for k in ((0, 1), (0, 2), (1, 2)))
        okw += m02 == F.mul(m12, ya) and m01 == F.mul(m12, F.mul(ya, ya))
    nz12 = sum(1 for a in D if F.peval(mu[(1, 2)], a) != 0)
    eps_psi = eps(F, es, psi)
    okz = eps_psi == F.pmul(nu, F.ppow(LD, 3))
    out = F.pdiv_exact(nu, F.pgcd(nu, LD))
    sqfree = F.pgcd(out, F.pderiv(out)) == [1]
    p_inf = 3 * n // 4 - 1
    print(f"E. 11/16 family, n = {n} (GF(2^{F.m})): W = {W} (11n/4 - 2 = {11 * n // 4 - 2}); contact >= 4 at {okc}/{n} "
          f"points; p_inf - Delta = {p_inf - Delta}; drops of deg (e_i e_j)' below the generic value: {drops} "
          f"(Proposition 2.4 (2): each >= {p_inf - Delta}); mu02 = mu12 y and mu01 = mu12 y^2 at {okw}/{n} points "
          f"(mu12 != 0 at {nz12}); eps_psi = (M/X) L_D^3: {okz}; roots of M/X outside D: {F.deg(out)} "
          f"(squarefree: {sqfree}; n/4 - 1 = {n // 4 - 1})")
    return okc == n and okw == n and okz and all(d is not None and d >= p_inf - Delta for d in drops) and \
        W == 11 * n // 4 - 2 and F.deg(out) == n // 4 - 1


def main():
    rnd = random.Random(55)
    ok = True
    for m in (8, 12):
        ok &= test_A(L.GFs(m), rnd)
    F = L.GFs(8)
    ok &= test_B(F, rnd)
    ok &= test_C(L.GFs(10), rnd)
    ok &= test_D(L.GFs(12), rnd)
    ok &= test_E(L.GFs(8), 4, rnd)
    ok &= test_E(L.GFs(8), 5, rnd)
    ok &= test_E(L.GFs(12), 6, rnd)
    print("ALL OK" if ok else "FAILURE")


if __name__ == "__main__":
    main()
