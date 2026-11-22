#!/usr/bin/env python3
"""Checks of Section 2 of 43-low-rate-residuals.md: the cubic first integrals dE, E = A3 Y^3 + A2 Y^2 + A1 Y + A0.

Part A (random cubics with two planted polynomial sections, GF(2^8)): identities (I1), (I2); the section criterion
  lambda_P * M_P = delta*P + U with lambda_P = (A3 P)' + A2', M_P = A3 P^2 + A1; Q = U/delta is a section with
  lambda = 0; the chord law P1 (+) P2 = (A3 P1 P2 + A1)/(A3 (P1 + P2)) gives sections; lambda, 1/M and
  zeta = Disc/(delta^2 M) are additive; zeta^2 + zeta = A3 Disc lambda^2/delta^4; the inverse map (lambda, zeta) -> P;
  M_P divides Disc for polynomial sections; zeta_P takes the values 0, 1 at the simple roots of Disc in the field,
  1 exactly where P^2 = A1/A3; the surface equation G = N*lam2 + lam0.
Part B (the flat cubic on subspace domains): delta = e0, U = e0 X^(n/2-1), Disc = e0^2 L_D/X, lambda_P = even part
  of P; for every hyperplane V the flat P_V is a section with lambda = e0/theta_V, M = theta_V L_V/X and
  agreement n/2 - 1 = n/2 - 1 - 2 deg lambda; the flats are not closed under the chord law (P_V1 (+) P_V2 has a
  pole at 0) and P_V (+) Q = P_V + theta_V/X.  The slack-1 cubic E' = Y^3 + (L_D - X^n) Y + e0 X^(n/2+1) of note 41
  has E'(X, X Y) = X^2 E(X, Y): its polynomial sections of degree <= n/4 at agreement n/2 with x^(n/2) are the
  2(n-1) polynomials X P_V and X (P_V (+) Q) = X P_V + theta_V.
Part C (Lemma D, D = F_64): for all pairs among 300 polynomial sections of the flat cubic (agreements 31, 27, 23),
  the squarefree part nu of P1 - P2 = xi^2 nu divides X * gcd(M_1, M_2): every root of odd multiplicity of the
  difference is a common agreement point or the root 0 of A3.
Part D (Section 6): the quintics Q8 = E_theta on a random subspace (N = 6, GF(2^12)): all lines of x^(n/4-1)
  are critical for a random theta, and for 60 random subspaces V of codimension 2 the flat P_V is a section of
  E_theta with theta = theta_2(V); on an F_4-subspace domain (n = 64): L_D and the L_V of the 21 F_4-hyperplanes are
  4-polynomials, P_V has degree <= n/16 - 1, agrees with x^(n/4-1) exactly on V minus 0 and is a section of E_4 = E_0.
Run: python3 43_structure.py   (about 1 minute)
"""
import random
import sys
import importlib

sys.path.insert(0, sys.path[0] or ".")
gfm = importlib.import_module("43_gf")


def invariants(F, E):
    A3, A2, A1, A0 = E
    b2, c2, b0, c0 = F.pderiv(A3), F.pderiv(A2), F.pderiv(A1), F.pderiv(A0)
    delta = F.pderiv(F.pmul(A1, A3))
    U = F.padd(F.pmul(c2, A1), F.pmul(c0, A3))
    Disc = F.padd(F.pmul(A1, F.psq(delta)), F.pmul(A3, F.psq(U)))
    return b2, c2, b0, c0, delta, U, Disc


class Cubic:
    def __init__(self, F, E):
        self.F = F
        self.E = E
        self.b2, self.c2, self.b0, self.c0, self.delta, self.U, self.Disc = invariants(F, E)

    def r(self, p):
        return self.F.rat(p)

    def Eval(self, P):
        F = self.F
        A3, A2, A1, A0 = [self.r(a) for a in self.E]
        P2 = F.rmul(P, P)
        return F.radd(F.radd(F.rmul(A3, F.rmul(P2, P)), F.rmul(A2, P2)), F.radd(F.rmul(A1, P), A0))

    def is_section(self, P):
        return self.F.r_in_Ft(self.Eval(P))

    def M(self, P):
        F = self.F
        return F.radd(F.rmul(self.r(self.E[0]), F.rmul(P, P)), self.r(self.E[2]))

    def lam(self, P):
        F = self.F
        return F.radd(F.rderiv(F.rmul(self.r(self.E[0]), P)), self.r(self.c2))

    def zeta(self, P):
        F = self.F
        return F.rdiv(self.r(self.Disc), F.rmul(self.r(F.psq(self.delta)), self.M(P)))

    def oplus(self, P1, P2):
        F = self.F
        A3, A1 = self.r(self.E[0]), self.r(self.E[2])
        return F.rdiv(F.radd(F.rmul(A3, F.rmul(P1, P2)), A1), F.rmul(A3, F.radd(P1, P2)))

    def Q(self):
        return self.F.rdiv(self.r(self.U), self.r(self.delta))


def partA(seed=1, trials=12):
    F = gfm.GF(8)
    rnd = random.Random(seed)
    rp = lambda d: F.trim([rnd.randrange(256) for _ in range(d)] + [rnd.randrange(1, 256)])
    done = 0
    while done < trials:
        A3, A1 = rp(rnd.randrange(1, 4)), rp(rnd.randrange(2, 6))
        P1, P2 = rp(rnd.randrange(1, 4)), rp(rnd.randrange(1, 4))
        if P1 == P2:
            continue
        r1 = F.pderiv(F.padd(F.pmul(A3, F.ppow(P1, 3)), F.pmul(A1, P1)))
        r2 = F.pderiv(F.padd(F.pmul(A3, F.ppow(P2, 3)), F.pmul(A1, P2)))
        Dd = F.psq(F.padd(P1, P2))
        E = (F.pmul(Dd, A3), [0] + F.padd(r1, r2), F.pmul(Dd, A1),
             [0] + F.padd(F.pmul(Dd, r1), F.pmul(F.padd(r1, r2), F.psq(P1))))
        C = Cubic(F, E)
        if not C.delta or not C.Disc:
            continue
        A3, A2, A1, A0 = E
        # (I1), (I2) as polynomial identities in Y: compare coefficients
        dY_U = [C.U, C.delta]  # delta*Y + U as a polynomial in Y with coefficients in F[X]
        lhs1 = [F.pmul(A3, C.c0), F.pmul(A3, C.b0), F.pmul(A3, C.c2), F.pmul(A3, C.b2)]  # A3*E_X
        rhs1 = [F.padd(F.pmul(C.c2, A1), C.U), F.padd(F.pmul(C.b2, A1), C.delta), F.pmul(C.c2, A3), F.pmul(C.b2, A3)]
        assert lhs1 == rhs1, "(I1)"
        lhs2 = [F.pmul(A3, F.psq(C.U)), [], F.pmul(A3, F.psq(C.delta))]
        rhs2 = [F.padd(F.pmul(F.psq(C.delta), A1), C.Disc), [], F.pmul(F.psq(C.delta), A3)]
        assert lhs2 == rhs2, "(I2)"
        R1, R2 = F.rat(P1), F.rat(P2)
        Q = C.Q()
        secs = {"P1": R1, "P2": R2, "Q": Q}
        secs["P1+P2"] = C.oplus(R1, R2)
        secs["P1+Q"] = C.oplus(R1, Q)
        secs["P2+Q"] = C.oplus(R2, Q)
        secs["P1+P2+Q"] = C.oplus(secs["P1+P2"], Q)
        rdelta, rU, rDisc, rA3 = C.r(C.delta), C.r(C.U), C.r(C.Disc), C.r(A3)
        omega = F.rdiv(F.rmul(rA3, rDisc), C.r(F.ppow(C.delta, 4)))
        for name, P in secs.items():
            assert C.is_section(P), name
            lam, M, zeta = C.lam(P), C.M(P), C.zeta(P)
            assert F.r_in_Ft(lam), "lambda in F(X^2)"
            assert F.rmul(lam, M) == F.radd(F.rmul(rdelta, P), rU), "lambda*M = delta*P + U"
            assert F.radd(F.rmul(zeta, zeta), zeta) == F.rmul(omega, F.rmul(lam, lam)), "Artin-Schreier"
            # inverse map
            if lam[0]:
                M2 = F.rdiv(rDisc, F.rmul(C.r(F.psq(C.delta)), zeta))
                assert F.rdiv(F.radd(F.rmul(lam, M2), rU), rdelta) == P, "inverse map"
        assert not C.lam(Q)[0] and C.zeta(Q) == F.rat([1])
        # additivity
        for a, b, c in (("P1", "P2", "P1+P2"), ("P1", "Q", "P1+Q"), ("P1+P2", "Q", "P1+P2+Q")):
            for fn in (C.lam, C.zeta, lambda P: F.rinv(C.M(P))):
                assert F.radd(fn(secs[a]), fn(secs[b])) == fn(secs[c]), "additivity"
        assert C.oplus(secs["P1+P2"], R2) == R1, "involution"
        # a non-section is rejected by the criterion
        Pbad = F.rat(rp(2))
        if not C.is_section(Pbad):
            assert F.rmul(C.lam(Pbad), C.M(Pbad)) != F.radd(F.rmul(rdelta, Pbad), rU)
        # polynomial sections: M | Disc, zeta in {0,1} at simple roots of Disc
        nroots = 0
        for P in (P1, P2):
            M = F.padd(F.pmul(A3, F.psq(P)), A1)
            q, rem = F.pdivmod(C.Disc, M)
            assert not rem, "M_P | Disc"
            dDisc = F.pderiv(C.Disc)
            for beta in range(256):
                if F.peval(C.Disc, beta) == 0 and F.peval(dDisc, beta) and F.peval(C.delta, beta) and F.peval(A3, beta):
                    nroots += 1
                    z = F.div(F.peval(q, beta), F.mul(F.peval(C.delta, beta), F.peval(C.delta, beta)))
                    agree = F.mul(F.peval(A3, beta), F.mul(F.peval(P, beta), F.peval(P, beta))) == F.peval(A1, beta)
                    assert z == (1 if agree else 0), "zeta at a root of Disc"
                    # and the word value Q(beta) = U/delta there is sqrt(A1/A3)
                    yb = F.div(F.peval(C.U, beta), F.peval(C.delta, beta))
                    assert F.mul(F.peval(A3, beta), F.mul(yb, yb)) == F.peval(A1, beta)
        # the surface: d/dX E(X,P) = N*lam2(g,h) + lam0(g,h) for a random polynomial P = g(X^2) + X h(X^2)
        P = rp(5)
        g, h = F.even_odd(P)
        gX, hX = F.subst_sq(g), F.subst_sq(h)
        a2, bb2 = F.even_odd(A3)
        a0, bb0 = F.even_odd(A1)
        a2, bb2, a0, bb0 = [F.subst_sq(t) for t in (a2, bb2, a0, bb0)]
        assert bb2 == C.b2 and bb0 == C.b0
        N = F.psq(P)
        lam2 = F.padd(F.padd(F.pmul(a2, hX), F.pmul(bb2, gX)), C.c2)
        lam0 = F.padd(F.padd(F.pmul(a0, hX), F.pmul(bb0, gX)), C.c0)
        dE = F.pderiv(C.Eval(F.rat(P))[0])
        assert dE == F.padd(F.pmul(N, lam2), lam0), "surface equation"
        done += 1
    print(f"A: {trials} random cubics with planted sections over GF(2^8): all identities hold "
          f"(7 sections each; last one had {nroots} simple roots of Disc in the field)")


def partB():
    for (m, N, kind) in ((16, 5, "span"), (16, 6, "span"), (5, 5, "field"), (6, 6, "field"), (12, 6, "rand")):
        F = gfm.GF(m)
        n = 1 << N
        rnd = random.Random(7)
        if kind == "span":
            basis = [1 << i for i in range(N)]
        elif kind == "field":
            basis = [1 << i for i in range(N)]
        else:
            while True:
                basis = [rnd.randrange(1, F.q) for _ in range(N)]
                if len(set(F.span(basis))) == n:
                    break
        D = F.span(basis)
        LD = F.subspace_poly(basis)
        e0 = LD[1]
        # gamma_D(X^2)*X + e0 = (L_D + X^n)/X
        A1 = F.trim(LD[1:n])
        A0 = [0] * (n // 2 - 1) + [e0]
        E = ([0, 1], [], A1, A0)
        C = Cubic(F, E)
        assert C.delta == [e0]
        assert C.U == F.pscale([0] * (n // 2 - 1) + [1], e0)
        assert C.Disc == F.pscale(LD[1:], F.mul(e0, e0)), "Disc = e0^2 L_D/X"
        Q = C.Q()
        assert Q == F.rat([0] * (n // 2 - 1) + [1])
        y = {a: F.pow(a, n // 2 - 1) for a in D if a}
        flats = []
        for f in range(1, n):
            ker = [x for x in range(n) if bin(x & f).count("1") % 2 == 0]
            vb, sp = [], {0}
            for x in ker:
                if x not in sp:
                    vb.append(x)
                    sp |= {s ^ x for s in sp}
            vbF = []
            for x in vb:
                e = 0
                for i in range(N):
                    if x >> i & 1:
                        e ^= basis[i]
                vbF.append(e)
            LV = F.subspace_poly(vbF)
            P = F.trim(LV[1:n // 2])  # (L_V - X^(n/2))/X
            assert LV[0] == 0 and F.deg(P) < n // 4
            V = set(F.span(vbF))
            lam_out = next(a for a in D if a not in V)
            theta = F.peval(LV, lam_out)
            RP = F.rat(P)
            assert C.is_section(RP)
            assert C.lam(RP) == F.rat([F.div(e0, theta)]), "lambda = e0/theta"
            assert F.even_odd(P)[0] == [F.div(e0, theta)]
            M = C.M(RP)
            assert M[1] == [1]
            assert F.pscale(M[0], 1) == F.pscale(F.trim(LV[1:]), theta), "M = theta L_V/X"
            ag = sum(1 for a in D if a and F.peval(P, a) == y[a])
            assert ag == n // 2 - 1 and all(F.peval(P, a) == y[a] for a in V if a)
            PQ = C.oplus(RP, Q)
            assert PQ == F.radd(RP, F.rat([theta], [0, 1])), "P_V (+) Q = P_V + theta/X"
            flats.append(RP)
        # slack-1 cubic of note 41, Section 4.4: sections are X times the sections of the flat cubic, and both
        # P_V and P_V (+) Q become polynomials: the 2(n-1) affine flats at agreement n/2 with the word x^(n/2)
        E1 = ([1], [], F.trim(LD[:n]), [0] * (n // 2 + 1) + [e0])
        C1 = Cubic(F, E1)
        assert C1.delta == [e0] and C1.Disc == F.pscale(LD, F.mul(e0, e0)) and C1.Q() == F.rat([0] * (n // 2) + [1])
        yy = {a: F.pow(a, n // 2) for a in D}
        cnt = 0
        for RP in flats:
            XP = F.rmul(F.rat([0, 1]), RP)
            XPQ = F.rmul(F.rat([0, 1]), C.oplus(RP, Q))
            for S in (XP, XPQ):
                assert S[1] == [1] and F.deg(S[0]) <= n // 4 and C1.is_section(S)
                assert sum(1 for a in D if F.peval(S[0], a) == yy[a]) == n // 2
                assert F.rderiv(S) == C1.lam(S)          # lambda = odd part (A3 = 1, A2 = 0)
                cnt += 1
            assert C1.oplus(XP, C1.Q()) == XPQ
        assert cnt == 2 * (n - 1)
        s = C.oplus(flats[0], flats[1])
        assert C.is_section(s) and s[1] == [0, 1], "chord of two flats has a simple pole at 0"
        print(f"B: {kind:5s} domain, GF(2^{m}), n = {n}: all {n - 1} flats are sections with constant lambda, "
              f"agreement n/2-1; Disc = e0^2 L_D/X; chord of two flats is not a polynomial; "
              f"slack-1 cubic: {cnt} affine flats = X*{{P_V, P_V (+) Q}} at agreement n/2")


def partC(limit=300):
    fs = importlib.import_module("43_flat_sections")
    N = 6
    F = gfm.GF(N)
    n = 1 << N
    basis = [1 << i for i in range(N)]
    D = F.span(basis)
    LD = F.subspace_poly(basis)
    y = {a: F.pow(a, n // 2 - 1) for a in D if a}
    ker = fs.lam_space(F, LD, N, 4)
    rnd = random.Random(2)
    secs = []
    seen = set()
    while len(secs) < limit:
        g = [0] * 5
        for t in range(len(ker)):
            if rnd.random() < 0.5:
                g = [a ^ b for a, b in zip(g, ker[t])]
        if tuple(g) in seen or not any(g):
            continue
        seen.add(tuple(g))
        for (P, ag) in fs.sections_of(F, LD, N, D, y, g):
            secs.append((P, ag, F.padd([0] + F.psq(P), [1])))   # M_P = X P^2 + 1 (gamma = 0, e0 = 1)
    pairs = nontrivial = 0
    for i in range(len(secs)):
        for j in range(i):
            dP = F.padd(secs[i][0], secs[j][0])
            d1 = F.pderiv(dP)
            if d1:
                nu = F.pdivmod(dP, F.pgcd(dP, d1))[0]
            else:
                nu = [1]
            common = F.pgcd(secs[i][2], secs[j][2])
            assert not F.pdivmod([0] + common, nu)[1], "Lemma D"
            # converse: common roots of M_1, M_2 are roots of the difference
            assert not F.pdivmod(dP, common)[1]
            pairs += 1
            if F.deg(nu) < F.deg(dP):
                nontrivial += 1
    hist = {}
    for (_, ag, _) in secs:
        hist[ag] = hist.get(ag, 0) + 1
    print(f"C: Lemma D on F_64: {pairs} pairs of polynomial sections (agreements {dict(sorted(hist.items()))}): "
          f"squarefree part of P1 - P2 divides X*gcd(M1, M2) in all; {nontrivial} pairs have a nontrivial square part")


def quintic(F, LD, n, theta):
    """E_theta = X^3 Y^5 + theta X Y^3 + (theta X^(n/2-1) + (L_D - X^n)/X) Y + e0 X^(n/4-1), as {deg_Y: coeff}."""
    e0 = LD[1]
    A1 = F.padd(F.trim(LD[1:n]), F.pscale([0] * (n // 2 - 1) + [1], theta))
    return {5: [0, 0, 0, 1], 3: [0, theta] if theta else [], 1: A1, 0: [0] * (n // 4 - 1) + [e0]}


def quintic_eval(F, Eq, P):
    r = []
    for d, c in Eq.items():
        r = F.padd(r, F.pmul(c, F.ppow(P, d)))
    return r


def quintic_critical(F, Eq, a, y):
    ey = 0
    ex = 0
    for d, c in Eq.items():
        if d % 2:
            ey ^= F.mul(F.peval(c, a), F.pow(y, d - 1))
        ex ^= F.mul(F.peval(F.pderiv(c), a), F.pow(y, d))
    return ey == 0 and ex == 0


def partD():
    F = gfm.GF(12)
    N = 6
    n = 1 << N
    rnd = random.Random(4)
    # (i) a random F_2-subspace
    while True:
        basis = [rnd.randrange(1, F.q) for _ in range(N)]
        D = F.span(basis)
        if len(set(D)) == n:
            break
    LD = F.subspace_poly(basis)
    y = {a: F.pow(a, n // 4 - 1) for a in D if a}
    Eq = quintic(F, LD, n, rnd.randrange(1, F.q))
    assert all(quintic_critical(F, Eq, a, y[a]) for a in D if a)
    done = 0
    while done < 60:
        vb = []
        sp = {0}
        while len(vb) < N - 2:
            x = rnd.choice(D)
            if x not in sp:
                vb.append(x)
                sp |= {t ^ x for t in sp}
        LV = F.subspace_poly(vb)
        # L_D = L_V^4 + theta2 L_V^2 + theta1 L_V
        cs = sorted({F.peval(LV, d) for d in D} - {0})
        assert len(cs) == 3
        theta2 = F.mul(cs[0], cs[0]) ^ F.mul(cs[0], cs[1]) ^ F.mul(cs[1], cs[1])
        P = F.trim(LV[1:n // 4])
        assert F.is_even(quintic_eval(F, quintic(F, LD, n, theta2), P)), "flat is a section of E_theta2"
        assert all((F.peval(P, a) == y[a]) == (a in sp) for a in D if a)
        done += 1
    # (ii) an F_4-subspace domain
    om = F.EXP[F.order // 3]
    while True:
        b4 = [rnd.randrange(1, F.q) for _ in range(3)]
        basis = b4 + [F.mul(om, b) for b in b4]
        D = F.span(basis)
        if len(set(D)) == n:
            break
    LD = F.subspace_poly(basis)
    assert all(LD[1 << s] == 0 for s in range(1, N, 2)), "L_D is a 4-polynomial"
    y = {a: F.pow(a, n // 4 - 1) for a in D if a}
    E4 = quintic(F, LD, n, 0)
    assert all(quintic_critical(F, E4, a, y[a]) for a in D if a)
    f4 = [0, 1, om, F.mul(om, om)]
    seen = set()
    cnt = 0
    for f in [(x, yv, zv) for x in f4 for yv in f4 for zv in f4][1:]:
        V = frozenset(F.mul(c0, b4[0]) ^ F.mul(c1, b4[1]) ^ F.mul(c2, b4[2])
                      for c0 in f4 for c1 in f4 for c2 in f4
                      if F.mul(f[0], c0) ^ F.mul(f[1], c1) ^ F.mul(f[2], c2) == 0)
        if V in seen:
            continue
        seen.add(V)
        assert len(V) == n // 4
        vb, sp = [], {0}
        for x in sorted(V):
            if x not in sp:
                vb.append(x)
                sp |= {t ^ x for t in sp}
        LV = F.subspace_poly(vb)
        assert all(LV[1 << s] == 0 for s in range(1, N - 2, 2))
        P = F.trim(LV[1:n // 4])
        assert F.deg(P) <= n // 16 - 1
        assert all((F.peval(P, a) == y[a]) == (a in V) for a in D if a)
        assert F.is_even(quintic_eval(F, E4, P))
        cnt += 1
    assert cnt == (n - 1) // 3
    print(f"D: Q8 on a random subspace (n = {n}): all lines critical, 60 flats of codimension 2 are sections of E_theta2; "
          f"F_4-subspace domain: {cnt} = (n-1)/3 F_4-hyperplane flats of degree <= {n // 16 - 1}, agreement {n // 4 - 1}, on E_4")


if __name__ == "__main__":
    partA()
    partB()
    partC()
    partD()
