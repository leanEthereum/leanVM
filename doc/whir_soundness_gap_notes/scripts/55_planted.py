#!/usr/bin/env python3
"""55_planted.py: referee tests of note 53, Sections 2.1, 2.3, 2.4 and Theorem 3.2 (1), on planted pencils.
Own code (55_lib.py); the construction is the one the note describes (a quintic E_Y = e1 + e3 Y^2 + e5 Y^4 with a
prescribed centre psi = N / M and prescribed polynomial sections, from an F(tau)-linear system), written
independently.

For a centre psi = N / M (M = b0 m^2, roots in F) and polynomials P_1, .., P_r (r <= 5) of degree <= Delta:
  unknowns x = (e1^0, e1^1, e3^0, e3^1, e5^0, e5^1) in F[tau]; P_i is a section iff (P_i + psi) ^ eps_{P_i} = 0, that is
  sum_j P_i^(2j) (v_i^0 e_j^1 + v_i^1 e_j^0) = 0 with v_i = (P_i M + N) M. The kernel is taken from the maximal minors
  (random rows are added when r < 5), the F[tau]-content is removed, and the result is scaled by the smallest element
  of F[tau] that makes E = sum_j (e_j Y^(2j+1) + X c_j Y^(2j)), c_j = (psi e_j)', a polynomial.
Checked on every instance:
  a. G(X, P, P') = 0 for the planted sections, G = E_X + E_Y Y_1 computed from E; not for random P
  b. (P + psi) eps_P is a square exactly for the sections
  c. Lemma 2.1: psi from pairs, triples concurrent
  d. Proposition 2.3 (1) at every finite POLE, (2) at infinity, (3) the residue N'/N + b0'/b0; N'/N alone
  e. Proposition 2.4: b0 | e_j, m^2 | (N e_j / b0)', b0 m | mu_ij, the degree drop of the minors
  f. (2.1): 2 deg(b0 m) + (p_inf - deg P)_+ >= |O_P| - deg P, Roots(b0) in O_P
  g. Theorem 3.2 (1): odd roots of eps_P that are not poles of psi are roots of eps_psi
Separately (test N): Proposition 2.3 (1) read literally "at every finite beta" fails at a point that is not a pole.
Run: python3 55_planted.py
"""
import importlib
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("55_lib")


def split(F, p):
    p0 = F.trim([c if i % 2 == 0 else 0 for i, c in enumerate(p)])
    p1 = F.trim([p[i + 1] if i % 2 == 0 and i + 1 < len(p) else 0 for i in range(len(p))])
    return p0, p1


def det(F, Mx):
    n = len(Mx)
    if n == 1:
        return Mx[0][0]
    r = []
    for j in range(n):
        if Mx[0][j]:
            sub = [row[:j] + row[j + 1:] for row in Mx[1:]]
            r = F.padd(r, F.pmul(Mx[0][j], det(F, sub)))
    return r


def eps(F, es, P):
    r = []
    P2 = F.pmul(P, P)
    pw = [1]
    for e in es:
        r = F.padd(r, F.pmul(e, pw))
        pw = F.pmul(pw, P2)
    return r


def plant(F, rnd, N, M, Ps):
    rows = []
    for P in Ps:
        v = F.pmul(F.padd(F.pmul(P, M), N), M)
        v0, v1 = split(F, v)
        row = []
        P2 = F.pmul(P, P)
        pw = [1]
        for _ in range(3):
            row += [F.pmul(pw, v1), F.pmul(pw, v0)]
            pw = F.pmul(pw, P2)
        rows.append(row)
    while len(rows) < 5:
        rows.append([F.psqr(F.rand_poly(rnd, 2, exact=False)) for _ in range(6)])
    x = [det(F, [row[:k] + row[k + 1:] for row in rows]) for k in range(6)]
    g = []
    for c in x:
        g = F.pgcd(g, c)
    assert g, "degenerate system"
    x = [F.pdiv_exact(c, g) for c in x]
    es = [F.padd(x[2 * j], F.pmul([0, 1], x[2 * j + 1])) for j in range(3)]
    # scale so that c_j = (psi e_j)' = (N e_j M)' / M^2 is a polynomial
    M2 = F.pmul(M, M)
    d = [1]
    for e in es:
        num = F.pderiv(F.pmul(F.pmul(N, e), M))
        need = F.pdiv_exact(M2, F.pgcd(M2, num)) if num else [1]
        d = F.pdiv_exact(F.pmul(d, need), F.pgcd(d, need))
    assert F.is_square_poly(d)
    es = [F.pmul(e, d) for e in es]
    cs = [F.pdiv_exact(F.pderiv(F.pmul(F.pmul(N, e), M)), M2) for e in es]
    return es, cs


def G_at(F, es, cs, P):
    """G(X, P, P') with G = E_X + E_Y Y_1, E = sum_j (e_j Y^(2j+1) + X c_j Y^(2j))."""
    P2 = F.pmul(P, P)
    pw = [1]
    r = []
    dP = F.pderiv(P)
    for e, c in zip(es, cs):
        assert F.is_square_poly(c)
        r = F.padd(r, F.pmul(pw, F.padd(F.padd(c, F.pmul(F.pderiv(e), P)), F.pmul(e, dP))))
        pw = F.pmul(pw, P2)
    return r


def val(F, f, beta):
    return F.mult_at(f, beta)


def run_case(F, rnd, name, b0_roots, m_roots, degN, Delta, r=5, verbose=True):
    """b0_roots: distinct simple factors of b0; m_roots: list of (root, multiplicity) of m (a root may also be in b0)."""
    b0 = F.locator(b0_roots)
    m = [1]
    for (b, k) in m_roots:
        m = F.pmul(m, F.ppow([b, 1], k))
    M = F.pmul(b0, F.pmul(m, m))
    while True:
        N = F.rand_poly(rnd, degN)
        if F.pgcd(N, M) == [1]:
            break
    Ps = [F.rand_poly(rnd, Delta if i < 2 else rnd.randrange(1, Delta + 1)) for i in range(r)]
    es, cs = plant(F, rnd, N, M, Ps)
    p_inf = F.deg(N) - F.deg(M)
    res = {}
    # a, b
    epsP = [eps(F, es, P) for P in Ps]
    assert all(e for e in epsP)
    res["a sections"] = all(G_at(F, es, cs, P) == [] for P in Ps)
    QM = [F.pmul(F.padd(F.pmul(P, M), N), M) for P in Ps]
    res["b square"] = all(F.is_square_poly(F.pmul(q, e)) for q, e in zip(QM, epsP))
    nonsec = 0
    for _ in range(5):
        P = F.rand_poly(rnd, Delta)
        g = G_at(F, es, cs, P)
        sq = F.is_square_poly(F.pmul(F.pmul(F.padd(F.pmul(P, M), N), M), eps(F, es, P)))
        nonsec += (g != []) and not sq
    res["a' random P not a section"] = nonsec == 5
    # c
    okpair = oktrip = True
    for i in range(r):
        for j in range(i + 1, r):
            w = F.pderiv(F.pmul(epsP[i], epsP[j]))
            num = F.padd(F.pmul(F.pderiv(F.pmul(Ps[i], epsP[i])), epsP[j]),
                         F.pmul(F.pderiv(F.pmul(Ps[j], epsP[j])), epsP[i]))
            okpair &= bool(w) and F.pmul(N, w) == F.pmul(M, num)
            for k in range(j + 1, r):
                s = []
                for (a, b, c) in ((i, j, k), (j, k, i), (k, i, j)):
                    s = F.padd(s, F.pmul(F.pderiv(F.pmul(Ps[a], epsP[a])), F.pderiv(F.pmul(epsP[b], epsP[c]))))
                oktrip &= s == []
    res["c psi from pairs"] = okpair
    res["c triples"] = oktrip
    # d. Proposition 2.3
    poles = {}
    for b in b0_roots:
        poles[b] = poles.get(b, 0) + 1
    for (b, k) in m_roots:
        poles[b] = poles.get(b, 0) + 2 * k
    ok1 = eq1 = n1 = 0
    ok2 = eq2 = n2 = 0
    for i in range(r):
        for j in range(i + 1, r):
            prod = F.pmul(epsP[i], epsP[j])
            dprod = F.pderiv(prod)
            dsum = F.padd(Ps[i], Ps[j])
            for b, pb in poles.items():
                order = val(F, dprod, b) - val(F, prod, b)
                bound = 2 * ((pb + val(F, dsum, b)) // 2)
                n1 += 1
                ok1 += order >= bound
                eq1 += order == bound
            if p_inf > max(F.deg(Ps[i]), F.deg(Ps[j])):
                dg = F.deg(dprod) - F.deg(prod)
                bound = -2 * ((p_inf - F.deg(dsum)) // 2) - 2
                n2 += 1
                ok2 += dg <= bound
                eq2 += dg == bound
    res["d1 finite poles"] = ok1 == n1
    res["d2 infinity"] = ok2 == n2
    ok3 = n3 = bad3 = 0
    b0set = set(b0_roots)
    for (b, k) in m_roots:
        if b in b0set:
            continue
        for e in epsP:
            n3 += 1
            v = val(F, e, b)
            Nb0 = F.pmul(N, b0)
            full = F.padd(F.pmul(F.pderiv(e), Nb0), F.pmul(e, F.pderiv(Nb0)))
            only = F.padd(F.pmul(F.pderiv(e), N), F.pmul(e, F.pderiv(N)))
            ok3 += (not full) or val(F, full, b) - v >= 2 * k
            bad3 += bool(only) and val(F, only, b) - v < 2 * k
    res["d3 residue N'/N + b0'/b0"] = ok3 == n3
    # e. Proposition 2.4
    okb0 = all(F.pdivmod(e, b0)[1] == [] for e in es)
    et = [F.pdiv_exact(e, b0) for e in es] if okb0 else None
    m2 = F.pmul(m, m)
    okm2 = okb0 and all(F.pdivmod(F.pderiv(F.pmul(N, e)), m2)[1] == [] for e in et)
    mu = {}
    okmu = True
    b0m = F.pmul(b0, m)
    for i in range(3):
        for j in range(i + 1, 3):
            dd = F.pderiv(F.pmul(es[i], es[j]))
            mu[(i, j)] = F.psqrt(dd)
            okmu &= (not mu[(i, j)]) or F.pdivmod(mu[(i, j)], b0m)[1] == []
    W = max([F.deg(e) + (2 * i + 1) * Delta for i, e in enumerate(es) if e] +
            [F.deg(c) + 2 * i * Delta for i, c in enumerate(cs) if c])
    okdrop = True
    slack = []
    for (i, j), v in mu.items():
        if v:
            bound = (W - (2 * i + 1) * Delta) + (W - (2 * j + 1) * Delta) - (p_inf - Delta)
            okdrop &= 2 * F.deg(v) <= bound
            slack.append(bound - 2 * F.deg(v))
    res["e b0 | e_j"] = okb0
    res["e m^2 | (N e_j/b0)'"] = okm2
    res["e b0 m | mu_ij"] = okmu
    res["e degree drop"] = okdrop
    # intrinsic identity with the true minors, on the sections and on random P, Q
    okid = True
    for _ in range(4):
        P, Q = F.rand_poly(rnd, Delta, exact=False), F.rand_poly(rnd, Delta, exact=False)
        B = F.padd(F.padd(mu[(0, 1)], F.pmul(mu[(0, 2)], F.padd(P, Q))), F.pmul(mu[(1, 2)], F.pmul(P, Q)))
        sq = F.pmul(F.padd(P, Q), B)
        okid &= F.pderiv(F.pmul(eps(F, es, P), eps(F, es, Q))) == F.pmul(sq, sq)
    res["e' identity"] = okid
    # f. (2.1)
    ok21 = eq21 = 0
    okb0O = True
    okg = True
    M2 = F.pmul(M, M)
    M4 = F.pmul(M2, M2)
    eps_psi_num = F.padd(F.padd(F.pmul(es[0], M4), F.pmul(es[1], F.pmul(F.pmul(N, N), M2))), F.pmul(es[2], F.ppow(N, 4)))
    assert eps_psi_num
    sizes = []
    for P, e in zip(Ps, epsP):
        O = F.odd_part(e)
        sizes.append(F.deg(O))
        lhs = 2 * F.deg(b0m) + max(p_inf - F.deg(P), 0)
        rhs = F.deg(O) - F.deg(P)
        ok21 += lhs >= rhs
        eq21 += lhs == rhs
        okb0O &= F.pdivmod(O, b0)[1] == []
        # g. odd roots that are not poles
        Onp = O
        while True:
            c = F.pgcd(Onp, M)
            if c == [1]:
                break
            Onp = F.pdiv_exact(Onp, c)
        okg &= F.pdivmod(eps_psi_num, Onp)[1] == []
    res["f (2.1)"] = ok21 == r
    res["f Roots(b0) in O_P"] = okb0O
    res["g odd roots are roots of eps_psi"] = okg
    e_inf = 2 * ((p_inf - Delta) // 2) + 2 if p_inf > Delta else 0
    degM = 2 * F.deg(b0m) + e_inf
    allok = all(res.values())
    if verbose:
        print(f"  {name}: deg b0 = {F.deg(b0)}, deg m = {F.deg(m)}, p_inf = {p_inf}, Delta = {Delta}, "
              f"deg(e1, e3, e5) = {tuple(F.deg(e) for e in es)}, W = {W}")
        print(f"     all checks: {allok}" + ("" if allok else f"  FAILED: {[k for k, v in res.items() if not v]}"))
        print(f"     2.3(1) at poles: {ok1}/{n1} (equality {eq1}); 2.3(2): {ok2}/{n2} (equality {eq2}); 2.3(3): {ok3}/{n3}, "
              f"N'/N alone fails at {bad3}/{n3}; degree drop slack {slack}")
        print(f"     |O_P| = {sizes}, deg P = {[F.deg(P) for P in Ps]}; (2.1) holds {ok21}/{r}, equality {eq21}/{r}; "
              f"deg of the divisor 2 deg(b0 m) + e_inf = {degM}; max |O_P| - Delta + [p_inf > Delta] = "
              f"{max(sizes) - Delta + (1 if p_inf > Delta else 0)}")
    return allok


def test_literal_nonpole(F, rnd, trials=6):
    """Proposition 2.3 (1) as printed ('at every finite beta') at a point beta that is not a pole of psi, where two
    sections take the value psi(beta) with the same derivative: ord_beta(P + P') >= 2, but dlog(eps_P eps_P') need not
    vanish at beta."""
    fails = 0
    done = 0
    for _ in range(trials):
        Delta = 4
        psi = F.rand_poly(rnd, 9)
        beta = rnd.randrange(1, F.q)
        y = F.peval(psi, beta)
        c1 = rnd.randrange(1, F.q)
        # P = y + c1 (X - beta) + (X - beta)^2 (random)
        Ps = []
        for _ in range(2):
            tail = F.pmul(F.ppow([beta, 1], 2), F.rand_poly(rnd, Delta - 2))
            Ps.append(F.padd(F.padd([y], F.pscale([beta, 1], c1)), tail))
        Ps += [F.rand_poly(rnd, Delta) for _ in range(3)]
        es, cs = plant(F, rnd, psi, [1], Ps)
        assert all(G_at(F, es, cs, P) == [] for P in Ps)
        e0, e1 = eps(F, es, Ps[0]), eps(F, es, Ps[1])
        prod = F.pmul(e0, e1)
        order = F.mult_at(F.pderiv(prod), beta) - F.mult_at(prod, beta)
        k = F.mult_at(F.padd(Ps[0], Ps[1]), beta)
        bound = 2 * (k // 2)
        done += 1
        fails += order < bound
        print(f"  N. non-pole beta: ord_beta(P + P') = {k}, printed bound 2 floor(k/2) = {bound}, "
              f"ord_beta dlog(eps_P eps_P') = {order}; ord_beta(P' + psi) = "
              f"{F.mult_at(F.padd(Ps[1], psi), beta)}")
    print(f"  N. the printed bound of Proposition 2.3 (1) fails at a non-pole in {fails}/{done} instances "
          f"(it is correct at poles: there P' + psi has a pole of order exactly p_beta)")
    return fails


def main():
    rnd = random.Random(5501)
    F = L.GFs(10)
    ok = True
    pts = rnd.sample(range(1, F.q), 12)
    cases = [
        ("polynomial centre, p_inf - Delta = 5", [], [], 9, 4),
        ("polynomial centre, p_inf - Delta = 4", [], [], 8, 4),
        ("polynomial centre, p_inf = Delta + 1", [], [], 5, 4),
        ("polynomial centre, p_inf = Delta (no divisor)", [], [], 4, 4),
        ("two simple poles, no pole at infinity", pts[:2], [], 2, 4),
        ("two simple poles, p_inf - Delta = 3", pts[:2], [], 9, 4),
        ("three simple poles, p_inf - Delta = 2", pts[:3], [], 9, 4),
        ("double pole, no pole at infinity", [], [(pts[3], 1)], 3, 4),
        ("double pole, p_inf - Delta = 3", [], [(pts[3], 1)], 9, 4),
        ("triple pole (b0 and m share the root)", [pts[4]], [(pts[4], 1)], 4, 4),
        ("fourfold pole", [], [(pts[5], 2)], 5, 4),
        ("simple + double + pole at infinity (p_inf - Delta = 2)", [pts[6]], [(pts[7], 1)], 9, 4),
        ("two simple + double, p_inf < 0", pts[8:10], [(pts[10], 1)], 2, 4),
        ("simple + fivefold pole", [pts[6], pts[11]], [(pts[11], 2)], 6, 4),
    ]
    for rep in range(2):
        for (name, b0r, mr, dN, Delta) in cases:
            ok &= run_case(F, rnd, name, b0r, mr, dN, Delta)
    # fewer planted sections (the kernel is then larger; one random element)
    for r in (2, 3, 4):
        ok &= run_case(F, rnd, f"{r} planted sections, simple + double pole, p_inf - Delta = 3", [pts[0]], [(pts[1], 1)],
                       10, 4, r=r)
    fails = test_literal_nonpole(F, rnd)
    print("ALL CHECKS OK" if ok else "SOME CHECK FAILED")
    print(f"literal reading of Proposition 2.3 (1) refuted at non-poles: {fails > 0}")


if __name__ == "__main__":
    main()
