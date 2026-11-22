#!/usr/bin/env python3
"""53_flat.py: the pencil and Goppa structure on the flat cubic at rate 1/4 (Section 3.1 of
53-goppa-structure-degenerate.md).

D an F_2-subspace of dimension N, n = 2^N, word y = x^(n/2-1) on D \\ 0, potential
E = X Y^3 + ((L_D - X^n)/X) Y + e0 X^(n/2-1), so E_Y(X, P) = eps_P = X P^2 + (L_D - X^n)/X.
Centre psi = X^(n/2-1). For every polynomial section P of degree < n/4 (the flats, and on field domains the
Gold codewords) the script checks, exactly:
  (a) (P + psi) eps_P is a square (pencil),
  (b) eps_P = const * Lambda_{S_P}, S_P the agreement set on D \\ 0 (clean: r_P = 1),
  (c) psi is recovered from pairs, and triples are concurrent,
  (d) S_i xor S_j lies in Gamma_inf(g), g = 2 floor((p_inf - Delta)/2) = n/4, and not in Gamma_inf(g + 2) for
      at least one pair (sharpness),
  (e) the number of sections against |Gamma_inf(g)|, and against RM(1, N) = 2n.

Run: python3 53_flat.py            (about one minute)
"""
import importlib
import itertools
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("53_lib")
fs = importlib.import_module("43_flat_sections")


def flats(F, basis, N):
    """the n - 1 flats P_V = (X^(n/2) + L_V)/X, V a hyperplane of D."""
    n = 1 << N
    out = []
    for u in range(1, n):
        # hyperplane {a : <a, u> = 0}: basis by elimination on the coordinate vectors
        piv = (u & -u).bit_length() - 1
        vb = []
        for i in range(N):
            if i == piv:
                continue
            v = basis[i]
            if u >> i & 1:
                v ^= basis[piv]
            vb.append(v)
        LV = F.subspace_poly(vb)
        assert F.deg(LV) == n // 2 and LV[0] == 0
        P = F.trim(LV[1:n // 2])
        out.append(P)
    return out


def run(m, N, kind, gold_j=None, seed=3):
    F = L.GF(m)
    n = 1 << N
    basis = L.domain(F, N, kind, seed)
    D = F.span(basis)
    LD = F.subspace_poly(basis)
    e0 = LD[1]
    psi = [0] * (n // 2 - 1) + [1]
    rest = F.trim(LD[1:n])            # (L_D - X^n)/X
    y = {a: F.pow(a, n // 2 - 1) for a in D if a}
    secs = flats(F, basis, N)
    nfl = len(secs)
    if gold_j is not None:
        ker = fs.lam_space(F, LD, N, gold_j)
        seen = {tuple(P) for P in secs}
        for mask in range(1, 1 << len(ker)):
            g = [0] * (gold_j + 1)
            for t in range(len(ker)):
                if mask >> t & 1:
                    g = [a ^ b for a, b in zip(g, ker[t])]
            for (P, ag) in fs.sections_of(F, LD, N, D, y, g):
                if tuple(P) not in seen:
                    seen.add(tuple(P))
                    secs.append(P)
    Delta = max(F.deg(P) for P in secs)
    assert Delta <= n // 4 - 1
    eps, S, ok_pencil, ok_clean = [], [], True, True
    for P in secs:
        e = F.padd(F.pmul([0, 1], F.psq(P)), rest)
        eps.append(e)
        ok_pencil &= L.is_square(F, F.pmul(F.padd(P, psi), e))
        Sp = [a for a in D if a and F.peval(P, a) == y[a]]
        ok_clean &= (L.odd_part(F, e) == L.locator(F, Sp) and F.deg(e) == len(Sp))
        S.append(L.subset_mask(D, Sp))
    assert len(set(S)) == len(S)
    # (c) psi from pairs, concurrency of triples
    rnd = random.Random(1)
    ok_psi, ok_conc = True, True
    for _ in range(40):
        i, j, k = rnd.sample(range(len(secs)), 3)
        c = [F.pderiv(F.pmul(secs[t], eps[t])) for t in (i, j, k)]
        den = F.pderiv(F.pmul(eps[i], eps[j]))
        num = F.padd(F.pmul(c[0], eps[j]), F.pmul(c[1], eps[i]))
        ok_psi &= bool(den) and F.trim(num) == F.pmul(psi, den)
        tot = F.padd(F.padd(F.pmul(c[0], F.pderiv(F.pmul(eps[j], eps[k]))),
                            F.pmul(c[1], F.pderiv(F.pmul(eps[i], eps[k])))),
                     F.pmul(c[2], F.pderiv(F.pmul(eps[i], eps[j]))))
        ok_conc &= not F.trim(tot)
    # (d) the code at infinity
    p_inf = n // 2 - 1
    g = 2 * ((p_inf - Delta) // 2)
    rows = L.rows_inf(F, D, g)
    rows2 = L.rows_inf(F, D, g + 2)
    code = L.f2_kernel(rows)
    code2 = L.f2_kernel(rows2)
    pairs = list(itertools.combinations(range(len(secs)), 2))
    if len(pairs) > 30000:
        pairs = rnd.sample(pairs, 30000)
    inside = sum(1 for (i, j) in pairs if L.syndrome(rows, S[i] ^ S[j]) == 0)
    inside2 = sum(1 for (i, j) in pairs if L.syndrome(rows2, S[i] ^ S[j]) == 0)
    wts = sorted({L.weight(S[i] ^ S[j]) for (i, j) in pairs})
    ag = {}
    for s in S:
        ag[L.weight(s)] = ag.get(L.weight(s), 0) + 1
    print(f"{kind:5s} GF(2^{m}) N={N} n={n}: {len(secs)} polynomial sections of degree <= {Delta} "
          f"({nfl} flats), by agreement {dict(sorted(ag.items(), reverse=True))}")
    print(f"   (a) pencil with centre X^(n/2-1): {ok_pencil}; (b) eps_P = c Lambda_S: {ok_clean}; "
          f"(c) psi from 40 pairs: {ok_psi}, 40 triples concurrent: {ok_conc}")
    print(f"   (d) g = {g}: pairs with S_i xor S_j in Gamma_inf(g): {inside}/{len(pairs)}; in Gamma_inf(g+2): "
          f"{inside2}/{len(pairs)}; weights of S_i xor S_j: {wts[:6]}{'...' if len(wts) > 6 else ''}")
    print(f"   (e) dim Gamma_inf({g}) = {len(code)} (RM(1,N): {N + 1}, RM(2,N): {L.rm_dim(2, N)}), "
          f"dim Gamma_inf({g + 2}) = {len(code2)}; sections {len(secs)} <= 2^{len(code)}: {len(secs) <= 1 << len(code)}")
    sys.stdout.flush()


if __name__ == "__main__":
    print("# subspace domains (only the flats are enumerated)")
    run(8, 4, "span")
    run(8, 5, "span")
    run(8, 5, "rand")
    run(12, 6, "span")
    run(12, 6, "rand")
    run(16, 7, "span")
    run(16, 8, "span")
    print("# field domains: flats and Gold codewords (all sections with lambda of tau-degree <= j)")
    run(5, 5, "field", gold_j=2)
    run(6, 6, "field", gold_j=2)
    run(7, 7, "field", gold_j=4)
