#!/usr/bin/env python3
"""54_sections.py: tests of Lemma 3.1 and of Propositions 4.2 and 4.4 of note 51, and of the working form (D2).

Exact arithmetic over GF(2^16) (54_gf.py).  x = sqrt(X), L = F(x), K = F(X) = F(x^2), D = d/dx (kernel K).
Polynomials of F[x] and of F[X] are coefficient lists; an element of F[X] is embedded in F[x] by X -> x^2.

A  Proposition 4.4 (pairs are free) and Proposition 4.2 (i), (iii) on synthetic pairs: two polynomials P1, P2 of
   degree <= Delta, two sets S1, S2 of points (and optional extra roots R1, R2, the factors r_P); the centre
   s = p1 + lambda1 D((p1 + p2) lambda2) / D(lambda1 lambda2) is computed, psi~ = s^2 = N_psi / M0^2 in lowest terms,
   and every statement is tested: f_P Lambda_S r_P is a square, the squarefree part Pi_P, gcd(g_P, M0) = 1, the
   identity (g g' kappa)^2 Theta' = M0^2 (f_P d)', (M0*)^2 | Theta', and the distance bound
   |S1 xor S2| >= 2 mu* + 1 + (max p - Delta)_+ - deg r_P - deg r_P'.
B  three members: the compatibility condition sum_cyc D(p_i lambda_i) D(lambda_j lambda_k) = 0.
C  the working form (D2): for random degenerate quintics (M0 C = M1 A + M2 B), E = (Y - psi~) E_Y modulo F(X^2)[Y^2]
   and M0^2 (dE)(X, P, P') = (f_P E_Y(X, P))' for random P.
D  Lemma 3.1 (dependent conics): W >= 3 Delta + sum_{S_P} j_alpha, on a family where it is an equality; the contact
   orders are measured from the definition of the contact ideal.

Run:  python3 54_sections.py
"""
import random
from importlib import import_module

gf = import_module("54_gf")
T = import_module("54_lemmaB_thm4")
mul, inv, fsqrt, fpow = gf.mul, gf.inv, gf.fsqrt, gf.fpow
padd, pmul, pdeg, pderiv, pdivmod, pgcd = gf.padd, gf.pmul, gf.pdeg, gf.pderiv, gf.pdivmod, gf.pgcd

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print("   FAILURE: " + msg)


def up(p):
    """F[X] -> F[x], X -> x^2."""
    out = [0] * (2 * len(p))
    for i, c in enumerate(p):
        out[2 * i] = c
    return gf.ptrim(out)


def even(p):
    return gf.ptrim(p[0::2])


def odd(p):
    return gf.ptrim(p[1::2])


def inK(p):
    return all(c == 0 for c in p[1::2])


def sqrt_poly_X(P):
    """p in F[x] with p(x)^2 = P(x^2)."""
    return gf.ptrim([fsqrt(c) for c in P])


def prod_lin(roots):
    out = [1]
    for r in roots:
        out = pmul(out, [r, 1])
    return out


def exact_div(p, q):
    d, r = pdivmod(p, q)
    assert not r
    return d


def centre(p1, p2, l1, l2):
    """s = (snum, den) with den in K, the unique s with (p_i - s) lambda_i in K (Proposition 4.4)."""
    den = pderiv(pmul(l1, l2))
    numt = pderiv(pmul(padd(p1, p2), l2))
    assert den, "lambda1, lambda2 are K-proportional"
    return padd(pmul(p1, den), pmul(l1, numt)), den


def lowest_terms(snum, den):
    """s = (M2 + x M1)/M0 with (M1, M2, M0) primitive in F[X]."""
    M2, M1, M0 = even(snum), odd(snum), even(den)
    g = pgcd(pgcd(M0, M1), M2)
    return exact_div(M1, g) if M1 else [], exact_div(M2, g) if M2 else [], exact_div(M0, g)


def prime_to(M0, Npsi):
    h = M0[:]
    while True:
        g = pgcd(h, Npsi)
        if pdeg(g) <= 0:
            return h
        h = exact_div(h, g)


def test_pair(rng, n, Delta, sI, s1, s2, nr1, nr2, common_word, stats, structured=0):
    if structured:
        # the symmetric difference S1 xor S2 contains an F2-subspace U of dimension `structured` (its square roots
        # form a subspace, whose annihilator polynomial is linearized: D(lambda) is a constant); the rest is random
        dim = n.bit_length() - 1
        dom = gf.subspace(rng, dim)
        U, rest = dom[:1 << structured], dom[1 << structured:]
        rng.shuffle(U)
        rng.shuffle(rest)
        half = len(U) // 2
        e1, e2 = s1 - half, s2 - half
        assert e1 >= 0 and e2 >= 0 and sI + e1 + e2 <= len(rest)
        I = rest[:sI]
        S1x = U[:half] + rest[sI:sI + e1]
        S2x = U[half:] + rest[sI + e1:sI + e1 + e2]
        extra = [z for z in gf.rand_points(rng, nr1 + nr2 + 40) if z not in dom]
        R1, R2 = extra[:nr1], extra[nr1:nr1 + nr2]
    else:
        pts = gf.rand_points(rng, n + nr1 + nr2 + 2)
        rng.shuffle(pts)
        I, S1x, S2x = pts[:sI], pts[sI:sI + s1], pts[sI + s1:sI + s1 + s2]
        R1 = pts[n:n + nr1]
        R2 = pts[n + nr1:n + nr1 + nr2]
    P1 = gf.rand_poly(rng, Delta)
    if common_word:
        # P2 = P1 on I (both agree with the same word there); needs |I| <= Delta
        P2 = padd(P1, pmul(prod_lin(I), gf.rand_poly(rng, Delta - len(I))))
    else:
        P2 = gf.rand_poly(rng, Delta)
    S1, S2 = I + S1x, I + S2x
    Lam1, Lam2 = prod_lin(S1 + R1), prod_lin(S2 + R2)           # Lambda_S r_P, in F[X]
    l1, l2 = prod_lin([fsqrt(a) for a in S1 + R1]), prod_lin([fsqrt(a) for a in S2 + R2])
    p1, p2 = sqrt_poly_X(P1), sqrt_poly_X(P2)
    snum, den = centre(p1, p2, l1, l2)
    check(inK(den), "D(lambda1 lambda2) not in K")
    for p, l in ((p1, l1), (p2, l2)):
        check(inK(pmul(padd(pmul(p, den), snum), l)), "Proposition 4.4: (p_i - s) lambda_i not in K")
    M1, M2, M0 = lowest_terms(snum, den)
    mu = pdeg(M0)
    Npsi = padd(pmul(M2, M2), [0] + pmul(M1, M1))
    sym = len(S1x) + len(S2x)
    symr = sym + len(R1) + len(R2)
    if common_word:
        check(2 * mu + 1 <= symr, "Proposition 4.4: mu = %d > (|S1 xor S2| + deg r - 1)/2, sym diff %d" % (mu, symr))
    f1 = padd(pmul(pmul(M0, M0), P1), Npsi)
    f2 = padd(pmul(pmul(M0, M0), P2), Npsi)
    for f, Lam in ((f1, Lam1), (f2, Lam2)):
        check(not pderiv(pmul(f, Lam)), "f_P Lambda_S r_P is not a square")
    Pi1, Pi2 = gf.psqfree(f1), gf.psqfree(f2)
    check(Pi1 == Lam1 and Pi2 == Lam2, "squarefree part of f_P is not Lambda_S r_P")
    g1, g2 = gf.psqrt(exact_div(f1, Pi1)), gf.psqrt(exact_div(f2, Pi2))
    check(pdeg(pgcd(g1, M0)) == 0 and pdeg(pgcd(g2, M0)) == 0, "Proposition 4.2 (i): gcd(g_P, M0) != 1")
    kap = pgcd(Pi1, Pi2)
    Theta = exact_div(pmul(Pi1, Pi2), pmul(kap, kap))
    check(pdeg(Theta) == symr, "Theta is not Lambda of the symmetric difference")
    d = padd(P1, P2)
    lhs = pmul(pmul(pmul(g1, g2), pmul(g1, g2)), pmul(pmul(kap, kap), pderiv(Theta)))
    rhs = pmul(pmul(M0, M0), pderiv(pmul(f1, d)))
    # g_P is defined up to a constant: compare up to a scalar
    ok = (not lhs and not rhs) or (lhs and rhs and len(lhs) == len(rhs) and gf.pscale(lhs, mul(rhs[-1], inv(lhs[-1]))) == rhs)
    check(ok, "identity (g g' kappa)^2 Theta' = M0^2 (f_P d)' fails")
    M0s = prime_to(M0, Npsi)
    mus = pdeg(M0s)
    dT = pderiv(Theta)
    check(dT and not pdivmod(dT, pmul(M0s, M0s))[1], "(M0*)^2 does not divide Theta'")
    pP = max(pdeg(f1), pdeg(f2)) - 2 * mu
    bound = 2 * mus + 1 + max(pP - Delta, 0)
    check(symr >= bound, "PROPOSITION 4.2 (iii): |S xor S'| + deg r + deg r' = %d < %d" % (symr, bound))
    stats.append((symr - bound, mu, mus, pP - Delta, symr))


def test_triple(rng, n, Delta):
    """three members: consistent data satisfy the cyclic relation, a perturbed third member does not."""
    lam = [gf.rand_poly(rng, rng.randint(3, 9)) for _ in range(3)]
    s = gf.rand_poly(rng, 11)                                   # a polynomial centre, M0 = 1
    ks = [up(gf.rand_poly(rng, 2)) for _ in range(3)]
    ps = [padd(s, pmul(k, l)) for k, l in zip(ks, lam)]          # (p_i - s) lambda_i = k_i lambda_i^2 in K
    snum, den = centre(ps[0], ps[1], lam[0], lam[1])
    check(snum == pmul(s, den), "Proposition 4.4: the formula does not return the planted centre")

    def cyc(ps):
        tot = []
        for i in range(3):
            j, k = (i + 1) % 3, (i + 2) % 3
            tot = padd(tot, pmul(pderiv(pmul(ps[i], lam[i])), pderiv(pmul(lam[j], lam[k]))))
        return tot
    check(not cyc(ps), "three members: the cyclic sum does not vanish on consistent data")
    bad = ps[:2] + [padd(ps[2], [0, 0, 0, 1])]                   # p_3 + x^3: (p_3' - s) lambda_3 not in K in general
    in_k = inK(pmul(padd(bad[2], s), lam[2]))
    check((not cyc(bad)) == in_k, "three members: the cyclic sum does not detect the inconsistent third member")
    return in_k


def test_working_form(rng, Delta):
    """random degenerate quintic: A_k = t_k M2 + M0 u_k, B_k = t_k M1 + M0 v_k, C_k = M1 u_k + M2 v_k."""
    dm = rng.randint(1, 3)
    M0, M1, M2 = gf.rand_poly(rng, dm), gf.rand_poly(rng, rng.randint(0, 3)), gf.rand_poly(rng, rng.randint(0, 3))
    if pdeg(pgcd(pgcd(M0, M1), M2)) > 0:
        return
    A, B, C = {}, {}, {}
    for k in range(3):
        t, u, v = gf.rand_poly(rng, 2), gf.rand_poly(rng, 3), gf.rand_poly(rng, 3)
        for P, q in ((A, padd(pmul(t, M2), pmul(M0, u))), (B, padd(pmul(t, M1), pmul(M0, v))), (C, padd(pmul(M1, u), pmul(M2, v)))):
            for i, cf in enumerate(q):
                if cf:
                    P[(i, k)] = cf
    # M0 C = M1 A + M2 B
    for k in range(3):
        col = lambda P: gf.ycoeffs(P)[k] if k < len(gf.ycoeffs(P)) else []
        check(pmul(M0, col(C)) == padd(pmul(M1, col(A)), pmul(M2, col(B))), "construction: M0 C != M1 A + M2 B")
    E = {}
    for (i, k), cf in A.items():
        E[(2 * i, 2 * k + 1)] = mul(cf, cf)
    for (i, k), cf in C.items():
        E[(2 * i + 1, 2 * k)] = mul(cf, cf)
    for (i, k), cf in B.items():
        E[(2 * i + 1, 2 * k + 1)] = mul(cf, cf)
    a, c = gf.dY(E), gf.dX(E)
    Npsi = padd(pmul(M2, M2), [0] + pmul(M1, M1))
    M02 = pmul(M0, M0)
    # M0^2 E + (M0^2 Y + N_psi) E_Y has only monomials X^even Y^even
    tot = {}
    for (i, k), cf in E.items():
        for e, m in enumerate(M02):
            if m:
                tot[(i + e, k)] = tot.get((i + e, k), 0) ^ mul(cf, m)
    for (i, k), cf in a.items():
        for e, m in enumerate(M02):
            if m:
                tot[(i + e, k + 1)] = tot.get((i + e, k + 1), 0) ^ mul(cf, m)
        for e, m in enumerate(Npsi):
            if m:
                tot[(i + e, k)] = tot.get((i + e, k), 0) ^ mul(cf, m)
    check(all((i % 2 == 0 and k % 2 == 0) for (i, k), cf in tot.items() if cf), "(D2): E != (Y - psi~) E_Y modulo F(X^2)[Y^2]")
    for _ in range(3):
        P = gf.rand_poly(rng, Delta)
        fP = padd(pmul(M02, P), Npsi)
        aP, cP = gf.subs_poly(a, P), gf.subs_poly(c, P)
        lhs = pmul(M02, padd(cP, pmul(aP, pderiv(P))))
        check(lhs == pderiv(pmul(fP, aP)), "working form: M0^2 dE(X, P, P') != (f_P E_Y(X, P))'")


def test_lemma31(rng, n, Delta, nz, stats):
    """Q = (Y - P1)(Y - P2), A = rho1 Q, B = rho2 Q, C = sigma Q; the word is P1 = P2 on I and P1 or P2 elsewhere.
    rho1 = xi_alpha and sigma = zeta_alpha on a set Z of nz points of I, rho2 = 1: one more unit of j on Z."""
    pts = gf.rand_points(rng, n)
    rng.shuffle(pts)
    I = pts[:Delta]                                             # |I| = Delta: P1 = P2 there
    rest = pts[Delta:]
    P1 = gf.rand_poly(rng, Delta)
    P2 = padd(P1, gf.pscale(prod_lin(I), rng.randrange(1, 1 << gf.M)))
    half = len(rest) // 2
    ys = {}
    for al in I:
        ys[al] = gf.peval(P1, al)
    for al in rest[:half]:
        ys[al] = gf.peval(P1, al)
    for al in rest[half:]:
        ys[al] = gf.peval(P2, al)
    Z = I[:nz]
    if nz:
        xs = Z
        rho1 = gf.pinterp(xs, [fsqrt(al) for al in xs])
        sigma = gf.pinterp(xs, [fsqrt(ys[al]) for al in xs])
        rho2 = [1]
    else:
        rho1, rho2, sigma = [1], [], gf.rand_poly(rng, Delta // 2)
    # Q as a dict polynomial: Y^2 + (P1 + P2) Y + P1 P2
    Qc = [pmul(P1, P2), padd(P1, P2), [1]]

    def times(r):
        out = {}
        for k, q in enumerate(Qc):
            for i, cf in enumerate(pmul(r, q)):
                if cf:
                    out[(i, k)] = cf
        return out
    A, B, C = times(rho1), times(rho2), times(sigma)
    E = {}
    for (i, k), cf in A.items():
        E[(2 * i, 2 * k + 1)] = mul(cf, cf)
    for (i, k), cf in C.items():
        E[(2 * i + 1, 2 * k)] = mul(cf, cf)
    for (i, k), cf in B.items():
        E[(2 * i + 1, 2 * k + 1)] = mul(cf, cf)
    a, c = gf.dY(E), gf.dX(E)
    W = T.wdeg_dE(E, Delta)
    cap = 12
    j = {al: T.contact_order(gf.taylor(a, al, ys[al], cap), gf.taylor(c, al, ys[al], cap), cap) // 2 for al in pts}
    rho = padd(pmul(rho1, rho1), [0] + pmul(rho2, rho2))
    best = None
    # third polynomials: P1 + c * prod over Delta points (agreement with P1 on them), several choices of the points
    for trial in range(12):
        if trial < 4:
            sub = I                                             # the Delta points of contact >= 4
        else:
            sub = rng.sample(pts, Delta)
        P3 = padd(P1 if trial % 2 == 0 else P2, gf.pscale(prod_lin(sub), rng.randrange(1, 1 << gf.M)))
        if pdeg(P3) > Delta:
            continue
        QP = padd(padd(pmul(P3, P3), pmul(padd(P1, P2), P3)), pmul(P1, P2))
        if not QP:
            continue
        SP = [al for al in pts if gf.peval(P3, al) == ys[al]]
        tot = sum(j[al] for al in SP)
        slack = W - 3 * Delta - tot
        check(slack >= 0, "LEMMA 3.1: W = %d < 3 Delta + sum j = %d" % (W, 3 * Delta + tot))
        best = slack if best is None else min(best, slack)
    prof = {}
    for al in pts:
        prof[j[al]] = prof.get(j[al], 0) + 1
    stats.append((best, W, pdeg(rho), dict(sorted(prof.items()))))


def main():
    rng = random.Random(5401)
    print("A. Propositions 4.4 and 4.2 (i), (iii) on synthetic pairs (GF(2^16))")
    for label, cw, cfgs in (
        ("common word (P1 = P2 on S1 and S2), r = 1", True, [(32, 15, 14, 9, 9, 0, 0), (32, 15, 15, 8, 8, 0, 0), (24, 11, 10, 7, 6, 0, 0), (32, 15, 12, 10, 9, 0, 0)]),
        ("common word, with factors r_P (extra roots)", True, [(32, 15, 14, 9, 9, 1, 2), (32, 15, 13, 9, 8, 2, 2), (24, 11, 11, 6, 6, 1, 0)]),
        ("no common word (algebra only)", False, [(32, 15, 14, 9, 9, 0, 0), (24, 11, 4, 9, 8, 1, 1), (20, 9, 0, 9, 10, 0, 1)]),
    ):
        stats = []
        for cfg in cfgs:
            for _ in range(8):
                test_pair(rng, *cfg, cw, stats)
        sl = [s[0] for s in stats]
        print("   %s: %d pairs; slack of the distance bound: min %d, max %d; mu in [%d, %d], mu* in [%d, %d], max(p) - Delta in [%d, %d]; pairs with mu* < mu: %d"
              % (label, len(stats), min(sl), max(sl), min(s[1] for s in stats), max(s[1] for s in stats), min(s[2] for s in stats),
                 max(s[2] for s in stats), min(s[3] for s in stats), max(s[3] for s in stats), sum(1 for s in stats if s[2] < s[1])))
    for label, dimU, cfgs in (
        ("common word, S1 xor S2 an F2-subspace of 16 points (structured)", 4, [(32, 15, 14, 8, 8, 0, 0), (32, 15, 15, 8, 8, 0, 0)]),
        ("common word, S1 xor S2 = a subspace of 8 points and 8 or 9 random points", 3, [(32, 15, 14, 8, 8, 0, 0), (32, 15, 13, 9, 8, 0, 0)]),
        ("common word, S1 xor S2 = a subspace of 16 points and 2 or 3 random points, one factor r", 4, [(32, 15, 13, 9, 9, 1, 0), (32, 15, 12, 10, 9, 0, 0)]),
    ):
        stats = []
        for cfg in cfgs:
            for _ in range(8):
                test_pair(rng, *cfg, True, stats, structured=dimU)
        sl = [s[0] for s in stats]
        print("   %s: %d pairs; slack: min %d, max %d; mu in [%d, %d], mu* in [%d, %d], max(p) - Delta in [%d, %d]"
              % (label, len(stats), min(sl), max(sl), min(s[1] for s in stats), max(s[1] for s in stats), min(s[2] for s in stats),
                 max(s[2] for s in stats), min(s[3] for s in stats), max(s[3] for s in stats)))
    print("B. three members: the cyclic relation")
    nin = sum(test_triple(rng, 32, 15) for _ in range(20))
    print("   20 triples: the relation holds on consistent data and fails on the perturbed ones (%d perturbed triples stayed consistent)" % nin)
    print("C. the working form (D2) on random degenerate quintics")
    for _ in range(30):
        test_working_form(rng, 6)
    print("   30 potentials, 3 random P each")
    print("D. Lemma 3.1 on Q = (Y - P1)(Y - P2)")
    for nz in (0, 2, 3):
        stats = []
        for _ in range(6):
            test_lemma31(rng, 24, 8, nz, stats)
        print("   |Z| = %d: 6 words; smallest slack W - 3 Delta - sum_{S_P} j_alpha over the third polynomials: %s; W = %s, deg rho = %s; profile of the first word %s"
              % (nz, sorted(set(s[0] for s in stats)), sorted(set(s[1] for s in stats)), sorted(set(s[2] for s in stats)), stats[0][3]))
    print("\n%d failures" % len(FAIL))


if __name__ == "__main__":
    main()
