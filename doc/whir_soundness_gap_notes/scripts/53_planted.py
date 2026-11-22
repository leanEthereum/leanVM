#!/usr/bin/env python3
"""53_planted.py: Consequences 1 and 2 on planted pencil quintics with a rational centre (Section 3.2 of
53-goppa-structure-degenerate.md).

Over GF(2^8): pick psi = N/M with M = b0 m^2 (b0 squarefree, roots given), five polynomials P_1..P_5 of degree
<= Delta, and solve the five F(tau)-linear equations  (P_i + psi) ^ (e1 + P_i^2 e3 + P_i^4 e5) = 0  for
(e1, e3, e5) in F[X]^3 (six unknowns in F[tau], kernel by 5 x 5 minors). Then E = (Y + psi)(e1 + e3 Y^2 + e5 Y^4)
modulo F(tau)[Y^2] is a pencil quintic with centre psi and the P_i are sections. Checked, exactly:
  C1  psi = [(P_i eps_i)' eps_j + (P_j eps_j)' eps_i] / (eps_i eps_j)'  for all pairs; triples are concurrent;
  C2  at every root beta of M:  ord_beta dlog(eps_i eps_j) >= 2 floor((ord_beta M + ord_beta(P_i + P_j)) / 2),
      with equality reported; at infinity, when deg psi = p_inf > Delta:
      deg dlog(eps_i eps_j) <= -2 floor((p_inf - deg(P_i + P_j)) / 2) - 2;
  C2' dlog(eps_i) - N'/N - b0'/b0 vanishes modulo m^2 away from the roots of b0 (the lead's residue N'/N is
      corrected by b0'/b0);
  I   the intrinsic identity (eps_P eps_Q)' = ((P + Q)(mu01 + mu02 (P + Q) + mu12 P Q))^2, mu_ij^2 = (e_i e_j)',
      for random P, Q that are not sections, and that m divides gcd(mu01, mu02, mu12).

Run: python3 53_planted.py     (about 20 s)
"""
import importlib
import itertools
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("53_lib")
F = L.GF(8)


def even_odd(p):
    return F.even_odd(p)


def from_parts(g, h):
    return F.padd(F.subst_sq(g), F.pmul([0, 1], F.subst_sq(h)))


def det(Mx):
    """determinant of a square matrix of polynomials (characteristic 2, Laplace expansion)."""
    k = len(Mx)
    if k == 1:
        return Mx[0][0]
    tot = []
    for c in range(k):
        if not Mx[0][c]:
            continue
        minor = [[Mx[r][cc] for cc in range(k) if cc != c] for r in range(1, k)]
        tot = F.padd(tot, F.pmul(Mx[0][c], det(minor)))
    return tot


def plant(rnd, Delta, b0_roots, m_roots, degN, tie=None):
    b0 = L.locator(F, b0_roots)
    m = L.locator(F, m_roots)
    M = F.pmul(b0, F.psq(m))
    while True:
        Nn = [rnd.randrange(256) for _ in range(degN)] + [1]
        if len(F.pgcd(Nn, M)) == 1:
            break
    Ps = []
    for i in range(5):
        P = [rnd.randrange(256) for _ in range(Delta)] + [rnd.randrange(1, 256)]
        Ps.append(P)
    if tie is not None and b0_roots:
        # make P_1 and P_2 agree at the first root of b0
        be = b0_roots[0]
        Ps[1][0] ^= F.peval(Ps[1], be) ^ F.peval(Ps[0], be)
    rows = []
    for P in Ps:
        q = F.pmul(F.padd(F.pmul(P, M), Nn), M)       # (P + psi) M^2, same direction as P + psi
        q0, q1 = even_odd(q)
        Z = [F.mul(c, c) for c in P]                    # P^2 as a polynomial in tau
        Z2 = F.pmul(Z, Z)
        rows.append([q1, q0, F.pmul(Z, q1), F.pmul(Z, q0), F.pmul(Z2, q1), F.pmul(Z2, q0)])
    ker = [det([[rows[r][c] for c in range(6) if c != skip] for r in range(5)]) for skip in range(6)]
    g = []
    for v in ker:
        g = F.pgcd(g, v) if g else F.trim(v)
    ker = [F.pdivmod(v, g)[0] if v else [] for v in ker]
    e1, e3, e5 = (from_parts(ker[0], ker[1]), from_parts(ker[2], ker[3]), from_parts(ker[4], ker[5]))
    return dict(b0=b0, m=m, M=M, N=Nn, Ps=Ps, e=(e1, e3, e5), b0_roots=b0_roots, m_roots=m_roots)


def eps_of(pl, P):
    e1, e3, e5 = pl["e"]
    P2 = F.psq(P)
    return F.padd(F.padd(e1, F.pmul(e3, P2)), F.pmul(e5, F.psq(P2)))


def check(pl, Delta, label, rnd):
    Ps, M, Nn, b0, m = pl["Ps"], pl["M"], pl["N"], pl["b0"], pl["m"]
    eps = [eps_of(pl, P) for P in Ps]
    assert all(F.trim(e) for e in eps)
    sec = all(L.is_square(F, F.pmul(F.pmul(F.padd(F.pmul(P, M), Nn), M), e)) for P, e in zip(Ps, eps))
    # C1
    ok_psi, ok_conc = True, True
    for i, j in itertools.combinations(range(5), 2):
        ci, cj = F.pderiv(F.pmul(Ps[i], eps[i])), F.pderiv(F.pmul(Ps[j], eps[j]))
        den = F.pderiv(F.pmul(eps[i], eps[j]))
        num = F.padd(F.pmul(ci, eps[j]), F.pmul(cj, eps[i]))
        ok_psi &= bool(den) and F.pmul(num, M) == F.pmul(Nn, den)
    for i, j, k in itertools.combinations(range(5), 3):
        c = [F.pderiv(F.pmul(Ps[t], eps[t])) for t in (i, j, k)]
        tot = F.padd(F.padd(F.pmul(c[0], F.pderiv(F.pmul(eps[j], eps[k]))),
                            F.pmul(c[1], F.pderiv(F.pmul(eps[i], eps[k])))),
                     F.pmul(c[2], F.pderiv(F.pmul(eps[i], eps[j]))))
        ok_conc &= not F.trim(tot)
    # C2 at the finite poles and at infinity
    p_inf = F.deg(Nn) - F.deg(M)
    ok_fin, eq_fin, tot_fin, ok_inf, eq_inf, tot_inf = True, 0, 0, True, 0, 0
    for i, j in itertools.combinations(range(5), 2):
        ee = F.pmul(eps[i], eps[j])
        num, den = F.rat(F.pderiv(ee), ee)
        dP = F.padd(Ps[i], Ps[j])
        for be in set(pl["b0_roots"]) | set(pl["m_roots"]):
            p = L.mult_at(F, M, be)
            bound = 2 * ((p + L.mult_at(F, dP, be)) // 2)
            v = L.val_rat(F, num, den, be)
            ok_fin &= v >= bound
            eq_fin += v == bound
            tot_fin += 1
        if p_inf > Delta:
            bound = -2 * ((p_inf - F.deg(dP)) // 2) - 2
            dg = F.deg(num) - F.deg(den)
            ok_inf &= dg <= bound
            eq_inf += dg == bound
            tot_inf += 1
    # C2': dlog(eps_i) + N'/N + b0'/b0 modulo m^2
    ok_res = True
    base = F.radd(F.rat(F.pderiv(Nn), Nn), F.rat(F.pderiv(b0), b0))
    wrong = 0
    for e in eps:
        dl = F.rat(F.pderiv(e), e)
        diff = F.radd(dl, base)
        diff0 = F.radd(dl, F.rat(F.pderiv(Nn), Nn))
        for be in set(pl["m_roots"]):
            if F.peval(b0, be) == 0:
                continue
            mu = L.mult_at(F, m, be)
            ok_res &= (not diff[0]) or L.val_rat(F, diff[0], diff[1], be) >= 2 * mu
            wrong += bool(diff0[0]) and L.val_rat(F, diff0[0], diff0[1], be) < 2 * mu
    # intrinsic form: (eps_P eps_Q)' = ((P + Q) B(P, Q))^2 with B = mu01 + mu02 (P + Q) + mu12 P Q, for ALL P, Q
    e1, e3, e5 = pl["e"]
    mu = []
    for (a, b) in ((e1, e3), (e1, e5), (e3, e5)):
        d = F.pderiv(F.pmul(a, b))
        mu.append(F.psqrt(d) if d else [])
    gmu = []
    for v in mu:
        gmu = F.pgcd(gmu, v) if gmu else F.trim(v)
    m_div = not F.pdivmod(gmu, m)[1]
    ok_B = True
    for _ in range(5):
        Pc = [rnd.randrange(256) for _ in range(Delta + 1)]
        Qc = [rnd.randrange(256) for _ in range(Delta + 3)]
        B = F.padd(F.padd(mu[0], F.pmul(mu[1], F.padd(Pc, Qc))), F.pmul(mu[2], F.pmul(Pc, Qc)))
        lhs = F.pderiv(F.pmul(eps_of(pl, Pc), eps_of(pl, Qc)))
        ok_B &= F.trim(lhs) == F.psq(F.pmul(F.padd(Pc, Qc), B))
    print(f"  {label}: deg M = {F.deg(M)} (b0 {F.deg(b0)}, m {F.deg(m)}), p_inf = {p_inf}, Delta = {Delta}, "
          f"deg(e1, e3, e5) = {tuple(F.deg(x) for x in pl['e'])}")
    print(f"     sections: {sec}; C1 psi from 10 pairs: {ok_psi}, 10 triples concurrent: {ok_conc}; "
          f"C2 finite: {ok_fin} (equality {eq_fin}/{tot_fin}); C2 infinity: {ok_inf} (equality {eq_inf}/{tot_inf}); "
          f"C2' residue N'/N + b0'/b0: {ok_res} (N'/N alone fails at {wrong} of the (section, root) pairs); "
          f"intrinsic identity on 5 random (P, Q): {ok_B}; m divides gcd(mu01, mu02, mu12): {m_div} "
          f"(deg gcd = {F.deg(gmu)}, deg m = {F.deg(m)})")
    return sec and ok_psi and ok_conc and ok_fin and ok_inf and ok_res and ok_B and m_div


def main():
    rnd = random.Random(11)
    allok = True
    cases = [
        ("polynomial centre, p_inf > Delta", 4, [], [], 9, None),
        ("polynomial centre, p_inf = Delta + 1", 4, [], [], 5, None),
        ("double pole", 4, [], [7], 3, None),
        ("double pole and pole at infinity", 4, [], [7], 9, None),
        ("fourfold pole and a double pole", 4, [], [7, 7, 19], 5, None),
        ("simple pole (b0) only", 4, [33], [], 4, None),
        ("simple pole with P_1 = P_2 there", 4, [33], [], 4, True),
        ("triple pole (root of b0 and m) and a double pole", 4, [33], [33, 90], 6, None),
        ("triple pole with P_1 = P_2 there, pole at infinity", 4, [33], [33, 90], 12, True),
        ("two simple poles, two double poles, infinity", 5, [33, 34], [90, 91], 14, True),
    ]
    for (label, Delta, b0r, mr, degN, tie) in cases:
        for rep in range(2):
            pl = plant(rnd, Delta, b0r, mr, degN, tie)
            allok &= check(pl, Delta, label, rnd)
            sys.stdout.flush()
    print("ALL PLANTED CHECKS PASS" if allok else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
