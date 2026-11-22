#!/usr/bin/env python3
"""55_goppa.py: referee tests of note 53, Theorem 3.1 (the clean case), on real agreement sets. Own code (55_lib.py).

A. The flat cubic at rate 1/4, E = X Y^3 + ((L_D - X^n)/X) Y + e0 X^(n/2-1), word x^(n/2-1), centre X^(n/2-1),
   Delta = n/4 - 1. Sections: the n - 1 flats P_V = (X^(n/2) + L_V)/X on subspace domains; on the field domain
   GF(32) also the codewords of degree <= 7 with 11 agreements, found here by random interpolation and closed under
   x -> lambda x and Frobenius (each one re-verified from the definition). Checked: d/dX E(X, P) = 0;
   (P + psi) eps_P is a square; eps_P = c Lambda_{S_P}; the power sums p_0..p_{n/4} of S_i xor S_j vanish.
B. The 5n/8 family at rate 1/2 (note 05): S a disjoint union of flats, each a coset of a fixed W of codimension 3 or a
   flat of size >= n/4, |S| = 5n/8. Members are sampled here (four shapes), the top of the locator is verified from
   scratch, P_S = X^(n/2) L_W + Lambda_S, centre X^(n/2) L_W, Delta = n/2, p_inf - Delta = n/8: the power sums
   p_0..p_{n/8} of S xor S' vanish, and on a random basis in GF(2^64) the differences have Boolean degree <= 2.
C. A clean pencil with a FINITE pole. 3-subsets T_i of D with Lambda_{T_i} + Lambda_{T_1} = a_i (X - beta)^2 for one
   beta (found by search in a small field), a common part C. (C1) M = (X - beta)^2, S_i = C + T_i. (C2) beta in D,
   M = X - beta (a simple pole, b0 = M), S_i = C + T_i + {beta}. Checked: the P_i are polynomials of degree
   <= Delta, a word with agreement sets exactly S_i exists, Odd(P_i + psi) = S_i, and dlog Lambda_{S_i xor S_j}
   vanishes to order 2 at beta (membership in Gamma(D; b0 m, 0)); the degree of the divisor equals |S| - Delta
   (no "+1": there is no pole at infinity).
Run: python3 55_goppa.py
"""
import importlib
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("55_lib")


def power_sums(F, pts, g):
    """[p_0, .., p_g]"""
    out = [len(pts) & 1]
    pw = list(pts)
    for k in range(1, g + 1):
        s = 0
        for v in pw:
            s ^= v
        out.append(s)
        pw = [F.mul(v, a) for v, a in zip(pw, pts)]
    return out


def subspace_poly(F, basis):
    return F.locator(F.span(basis))


def flat_cubic(F, D_basis):
    N = len(D_basis)
    n = 1 << N
    D = F.span(D_basis)
    LD = F.locator(D)
    assert all(LD[i] == 0 for i in range(n + 1) if i & (i - 1)), "L_D is not linearized"
    e0 = LD[1]
    e1 = LD[1:n]                      # (L_D - X^n) / X
    e1 = F.trim(e1)
    psi = [0] * (n // 2 - 1) + [1]
    return D, LD, e0, e1, psi


def E_flat_at(F, e0, e1, n, P):
    """E(X, P) = X P^3 + e1 P + e0 X^(n/2-1)."""
    P3 = F.pmul(P, F.pmul(P, P))
    r = F.padd(F.pmul([0, 1], P3), F.pmul(e1, P))
    return F.padd(r, [0] * (n // 2 - 1) + [e0])


def hyperplanes(N):
    """the 2^N - 1 linear hyperplanes of F_2^N as lists of indices."""
    out = []
    for h in range(1, 1 << N):
        out.append([a for a in range(1 << N) if bin(a & h).count("1") % 2 == 0])
    return out


def check_flat(F, name, D_basis, extra_sections=None, max_pairs=4000, rnd=None):
    N = len(D_basis)
    n = 1 << N
    D, LD, e0, e1, psi = flat_cubic(F, D_basis)
    y = {a: F.pow(a, n // 2 - 1) for a in D}
    Delta = n // 4 - 1
    secs = []
    for H in hyperplanes(N):
        V = [D[a] for a in H]
        LV = F.locator(V)
        num = F.padd([0] * (n // 2) + [1], LV)
        assert num[0] == 0
        secs.append(F.trim(num[1:]))
    nflat = len(secs)
    if extra_sections:
        secs += extra_sections
    okdeg = oksec = oksq = okeps = 0
    sets = []
    agree_hist = {}
    for P in secs:
        okdeg += F.deg(P) <= Delta
        EP = E_flat_at(F, e0, e1, n, P)
        oksec += F.pderiv(EP) == []
        epsP = F.padd(F.pmul([0, 1], F.pmul(P, P)), e1)
        oksq += F.is_square_poly(F.pmul(F.padd(P, psi), epsP))
        S = [a for a in D if F.peval(P, a) == y[a]]
        agree_hist[len(S)] = agree_hist.get(len(S), 0) + 1
        okeps += epsP == F.pscale(F.locator(S), epsP[-1])
        sets.append(S)
    g = n // 4
    pairs = [(i, j) for i in range(len(secs)) for j in range(i + 1, len(secs))]
    if len(pairs) > max_pairs:
        pairs = rnd.sample(pairs, max_pairs)
    okg = okg1 = 0
    wts = set()
    for (i, j) in pairs:
        T = list(set(sets[i]) ^ set(sets[j]))
        ps = power_sums(F, T, g + 3)
        okg += all(v == 0 for v in ps[:g + 1])
        okg1 += all(v == 0 for v in ps[:g + 3])
        wts.add(len(T))
    tot = len(secs)
    print(f"A. {name}, n = {n}: {tot} sections ({nflat} flats), by agreement {dict(sorted(agree_hist.items()))}; "
          f"degree <= {Delta}: {okdeg}/{tot}; sections of dE: {oksec}/{tot}; (P + psi) eps_P square: {oksq}/{tot}; "
          f"eps_P = c Lambda_S: {okeps}/{tot}")
    print(f"     pairs with p_0..p_{g}(S_i xor S_j) = 0: {okg}/{len(pairs)} (and up to p_{g + 2}: {okg1}); weights "
          f"{sorted(wts)}; divisor degree e_inf = {g + 2} >= max|S| - Delta + 1 = {max(agree_hist) - Delta + 1}")
    return okdeg == oksec == oksq == okeps == tot and okg == len(pairs)


def interp(F, xs, ys):
    Lall = F.locator(xs)
    res = []
    for x, yv in zip(xs, ys):
        q = F.pdiv_exact(Lall, [x, 1])
        res = F.padd(res, F.pscale(q, F.mul(yv, F.inv(F.peval(q, x)))))
    return res


def gold_sections(F, rnd, want_agree=11, samples=60000):
    """codewords of degree <= 7 with exactly want_agree agreements with x^15 on GF(32)^*, by random interpolation of
    8 points; orbits under x -> lambda x and Frobenius are added, every polynomial is verified."""
    assert F.m == 5
    n = 32
    pts = list(range(1, 32))
    y = {a: F.pow(a, 15) for a in pts}
    found = {}

    def agreement(P):
        return sum(1 for a in pts if F.peval(P, a) == y[a])

    def orbit(P):
        out = []
        cur = P
        for _ in range(5):
            for lam in pts:
                Q = [F.mul(F.mul(c, F.pow(lam, i)), F.inv(F.pow(lam, 15))) for i, c in enumerate(cur)]
                out.append(tuple(F.trim(Q)))
            cur = [F.mul(c, c) for c in cur]
        return out
    for _ in range(samples):
        xs = rnd.sample(pts, 8)
        P = interp(F, xs, [y[a] for a in xs])
        if F.deg(P) <= 7 and tuple(P) not in found and agreement(P) == want_agree:
            for Q in orbit(P):
                if Q not in found:
                    assert agreement(list(Q)) == want_agree
                    found[Q] = True
    return [list(Q) for Q in found]


# ---------------- B: the 5n/8 family ----------------

def rand_flat(rnd, N, dim):
    """random affine flat of F_2^N of the given dimension, as a set of indices."""
    while True:
        vs = [rnd.randrange(1, 1 << N) for _ in range(dim)]
        if L.f2_rank(vs) == dim:
            break
    pts = [0]
    for v in vs:
        pts += [p ^ v for p in pts]
    c = rnd.randrange(1 << N)
    return frozenset(p ^ c for p in pts)


def sample_five_eighths(rnd, N, count):
    n = 1 << N
    Wd = N - 3
    Wset = frozenset(range(1 << Wd))                 # W = span of the first N - 3 basis vectors
    cosets = [frozenset(w ^ (c << Wd) for w in Wset) for c in range(8)]
    out = set()
    tries = 0
    while len(out) < count and tries < 200000:
        tries += 1
        shape = rnd.randrange(4)
        pieces = []
        if shape == 0:      # hyperplane + one W-coset
            pieces = [rand_flat(rnd, N, N - 1), rnd.choice(cosets)]
        elif shape == 1:    # two flats of size n/4 + one W-coset
            pieces = [rand_flat(rnd, N, N - 2), rand_flat(rnd, N, N - 2), rnd.choice(cosets)]
        elif shape == 2:    # one flat of size n/4 + three W-cosets
            pieces = [rand_flat(rnd, N, N - 2)] + rnd.sample(cosets, 3)
        else:               # five W-cosets
            pieces = rnd.sample(cosets, 5)
        S = frozenset().union(*pieces)
        if len(S) == sum(len(p) for p in pieces) and len(S) == 5 * n // 8:
            out.add((shape, S))
    return list(out)


def check_five_eighths(F, name, N, rnd, count, max_pairs=3000):
    n = 1 << N
    basis = F.rand_basis(rnd, N)
    D = F.span(basis)
    LW = F.locator(F.span(basis[:N - 3]))
    psi = [0] * (n // 2) + LW                         # X^(n/2) L_W, degree 5n/8
    members = sample_five_eighths(rnd, N, count)
    Delta = n // 2
    oktop = 0
    for (shape, S) in members:
        P = F.padd(psi, F.locator([D[a] for a in S]))
        oktop += F.deg(P) <= Delta
    shapes = {}
    for (shape, S) in members:
        shapes[shape] = shapes.get(shape, 0) + 1
    g = n // 8
    pairs = [(i, j) for i in range(len(members)) for j in range(i + 1, len(members))]
    if len(pairs) > max_pairs:
        pairs = rnd.sample(pairs, max_pairs)
    okg = okdeg = 0
    nxt = 0
    wts = {}
    for (i, j) in pairs:
        Tidx = members[i][1] ^ members[j][1]
        ps = power_sums(F, [D[a] for a in Tidx], g + 1)
        okg += all(v == 0 for v in ps[:g + 1])
        nxt += ps[g + 1] != 0
        mask = 0
        for a in Tidx:
            mask |= 1 << a
        okdeg += L.boolean_degree(N, mask) <= 2
        wts[len(Tidx)] = wts.get(len(Tidx), 0) + 1
    print(f"B. {name}, N = {N}: {len(members)} sampled members (by shape {dict(sorted(shapes.items()))}); "
          f"deg(X^(n/2) L_W + Lambda_S) <= n/2: {oktop}/{len(members)}")
    print(f"     pairs with p_0..p_{g}(S xor S') = 0: {okg}/{len(pairs)} (p_{g + 1} != 0 in {nxt}); Boolean degree <= 2: "
          f"{okdeg}/{len(pairs)}; weights {dict(sorted(wts.items()))}")
    return oktop == len(members) and okg == len(pairs) and okdeg == len(pairs)


# ---------------- C: a clean pencil with a finite pole ----------------

def find_finite_pencils(F, D, rnd):
    """families of 3-subsets T of D with Lambda_T + Lambda_T' = a (X - beta)^2 for one beta: key (e2; the class of
    (e1, e3) under (e1, e3) ~ (e1 + a, e3 + a beta^2))."""
    from itertools import combinations
    by_e2 = {}
    for T in combinations(D, 3):
        a, b, c = T
        e1 = a ^ b ^ c
        e2 = F.mul(a, b) ^ F.mul(a, c) ^ F.mul(b, c)
        e3 = F.mul(a, F.mul(b, c))
        by_e2.setdefault(e2, []).append((T, e1, e3))
    best = {"in": None, "out": None}
    Dset = set(D)
    for e2, lst in by_e2.items():
        if len(lst) < 3:
            continue
        for (T0, a0, c0) in lst[:6]:
            groups = {}
            for (T, a1, c1) in lst:
                if a1 == a0:
                    continue
                beta = F.sqrt(F.mul(c0 ^ c1, F.inv(a0 ^ a1)))
                groups.setdefault(beta, []).append(T)
            for beta, Ts in groups.items():
                fam = [T0] + Ts
                if any(beta in T for T in fam):
                    continue
                kind = "in" if beta in Dset else "out"
                if best[kind] is None or len(fam) > len(best[kind][1]):
                    best[kind] = (beta, fam)
    return best


def check_finite_pencil(F, D, beta, fam, simple, rnd, label):
    used = set()
    for T in fam:
        used |= set(T)
    used.add(beta)
    rest = [a for a in D if a not in used]
    C = rnd.sample(rest, min(len(rest), 10))
    LC = F.locator(C)
    Qs = [F.pmul(LC, F.locator(T)) for T in fam]
    M = [beta, 1] if simple else F.pmul([beta, 1], [beta, 1])
    N = F.pdivmod(Qs[0], M)[1]
    assert F.pgcd(N, M) == [1]
    Ps = []
    okpoly = True
    for Q in Qs:
        q, r = F.pdivmod(F.padd(Q, N), M)
        okpoly &= r == []
        Ps.append(q)
    Delta = max(F.deg(P) for P in Ps)
    sets = [set(C) | set(T) | ({beta} if simple else set()) for T in fam]
    # a word with agreement sets exactly S_i
    okword = True
    for a in D:
        vals = {}
        for i, P in enumerate(Ps):
            vals.setdefault(F.peval(P, a), []).append(i)
        ins = [i for i in range(len(Ps)) if a in sets[i]]
        if ins:
            v = F.peval(Ps[ins[0]], a)
            okword &= sorted(vals[v]) == ins          # exactly the members that contain a take this value
    # Odd(P + psi) = S: P + psi = Q / M
    okodd = True
    for Q, S in zip(Qs, sets):
        odd = F.odd_part(F.pmul(Q, M))                # Odd(Q / M) = Odd(Q M)
        okodd &= odd == F.locator(sorted(S))
    # Goppa membership: dlog Lambda_T has order >= 2 at beta
    okg = 0
    npairs = 0
    for i in range(len(fam)):
        for j in range(i + 1, len(fam)):
            T = sets[i] ^ sets[j]
            LT = F.locator(sorted(T))
            dLT = F.pderiv(LT)
            npairs += 1
            okg += F.mult_at(dLT, beta) - F.mult_at(LT, beta) >= 2
    S = len(sets[0])
    degdiv = 2
    print(f"C. {label}: beta {'in' if beta in set(D) else 'outside'} D, {len(fam)} members, |S| = {S}, Delta = {Delta}; "
          f"P_i polynomial: {okpoly}; a word with agreement sets S_i exists: {okword}; Odd(P_i + psi) = S_i: {okodd}; "
          f"S_i xor S_j in Gamma(D; X - beta, 0): {okg}/{npairs}; divisor degree {degdiv}, |S| - Delta = {S - Delta}")
    return okpoly and okword and okodd and okg == npairs and degdiv == S - Delta


def main():
    rnd = random.Random(5503)
    ok = True
    F8 = L.GFs(8)
    ok &= check_flat(F8, "random subspace of GF(2^8)", F8.rand_basis(rnd, 4), rnd=rnd)
    ok &= check_flat(F8, "random subspace of GF(2^8)", F8.rand_basis(rnd, 5), rnd=rnd)
    F12 = L.GFs(12)
    ok &= check_flat(F12, "random subspace of GF(2^12)", F12.rand_basis(rnd, 6), rnd=rnd)
    F16 = L.GFs(16)
    ok &= check_flat(F16, "span(1, x, .., x^6) in GF(2^16)", [1 << i for i in range(7)], max_pairs=1500, rnd=rnd)
    F5 = L.GFs(5)
    gold = gold_sections(F5, rnd)
    print(f"   GF(32): {len(gold)} codewords of degree <= 7 with exactly 11 agreements found by sampling "
          f"(note 43 quotes 186; completeness of the sampling is not proved here)")
    ok &= check_flat(F5, "field domain GF(32), flats and Gold codewords", [1 << i for i in range(5)],
                     extra_sections=gold, max_pairs=30000, rnd=rnd)
    Fb = L.GFb(64)
    ok &= check_five_eighths(Fb, "random basis in GF(2^64)", 5, rnd, 300)
    ok &= check_five_eighths(Fb, "random basis in GF(2^64)", 6, rnd, 200, max_pairs=1500)
    for (Ff, Nn) in ((F8, 5), (L.GFs(10), 6)):
        D = Ff.span(Ff.rand_basis(rnd, Nn))
        best = find_finite_pencils(Ff, D, rnd)
        for kind in ("out", "in"):
            if best[kind] is None:
                print(f"C. GF(2^{Ff.m}), N = {Nn}: no family with beta {kind}side D found")
                continue
            beta, fam = best[kind]
            ok &= check_finite_pencil(Ff, D, beta, fam, False, rnd, f"GF(2^{Ff.m}), N = {Nn}, double pole")
            if kind == "in":
                ok &= check_finite_pencil(Ff, D, beta, fam, True, rnd, f"GF(2^{Ff.m}), N = {Nn}, simple pole (b0)")
    print("ALL OK" if ok else "FAILURE")


if __name__ == "__main__":
    main()
