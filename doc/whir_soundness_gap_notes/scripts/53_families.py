#!/usr/bin/env python3
"""53_families.py: the pencil and the intrinsic Goppa divisor on the known rate 1/2 objects (Sections 3.3 to 3.5
of 53-goppa-structure-degenerate.md).

A  The 11/16 family of note 45 (subspace domains, word psi = X^(3n/4-1)) and the 27/40 family (D = F_n, word
   X^(3n/4-j)): E = (Y + psi) a, a = e5 Y^4 + e3 Y^2 + e1. Checked: the minors mu_ij (mu_ij^2 = (e_i e_j)'),
   their gcd g_mu and their degree drops at infinity, the word as mu02/mu12 = mu01/mu02 on D, e3 = 0 and
   e1 = e5 y^4 on D, the identity (eps_P eps_Q)' = ((P + Q) B(P, Q))^2 for random P, Q, and the odd roots of
   eps_psi (the extended support D+).
B  The 5n/8 family of note 05 (1400 and 3192 codewords at n = 32, 64 on span(1, x, .., x^(N-1)) in GF(2^16)) as
   a pencil at infinity: centre psi = X^(n/2) L_W, P_i = psi + Lambda_{S_i}, theta = 1; all S_i xor S_j lie in
   Gamma_inf(n/8), which is RM(2, N) there; the number of members against the number of words of the coset.
C  The converse "equal size and S_1 xor S_2 in Gamma_inf(g) implies deg(Lambda_{S_1} + Lambda_{S_2}) < p - g"
   is false: two cosets of a plane plus a common part; and, on the 5n/8 coset, how many words of weight 5n/8 of
   the coset S_1 + Gamma_inf(n/8) are list members (the even elementary symmetric functions are not controlled
   by the power sums in characteristic 2).

Run: python3 53_families.py      (about 2 minutes)
"""
import importlib
import itertools
import random
import sys

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("53_lib")


def minors(F, e1, e3, e5):
    mu = []
    for (a, b) in ((e1, e3), (e1, e5), (e3, e5)):
        d = F.pderiv(F.pmul(a, b))
        assert L.is_square(F, d)
        mu.append(F.psqrt(d) if d else [])
    return mu


def gcd_all(F, ps):
    g = []
    for v in ps:
        v = F.trim(v)
        if v:
            g = F.pgcd(g, v) if g else v
    return g


def eps(F, e, P):
    P2 = F.psq(P)
    return F.padd(F.padd(e[0], F.pmul(e[1], P2)), F.pmul(e[2], F.psq(P2)))


def report(F, name, D, e, psi, W, Delta, rnd):
    n = len(D)
    LD = L.locator(F, D)
    mu = minors(F, *e)
    g = gcd_all(F, mu)
    # degree drops: (W - i Delta) + (W - j Delta) - deg (e_i e_j)'
    drops = []
    for (i, j), v in zip(((1, 3), (1, 5), (3, 5)), mu):
        drops.append(None if not F.trim(v) else 2 * W - (i + j) * Delta - 2 * F.deg(v))
    y = [F.peval(psi, a) for a in D]
    w_ok = all(F.peval(mu[1], a) == F.mul(F.peval(mu[2], a), b) and
               F.peval(mu[0], a) == F.mul(F.peval(mu[1], a), b) for a, b in zip(D, y))
    e3_ok = not F.pdivmod(e[1], LD)[1] if F.trim(e[1]) else True
    e1_ok = all(F.peval(e[0], a) == F.mul(F.peval(e[2], a), F.pow(b, 4)) for a, b in zip(D, y))
    idok = True
    for _ in range(4):
        P = [rnd.randrange(F.q) for _ in range(Delta + 1)]
        Q = [rnd.randrange(F.q) for _ in range(Delta + 1)]
        B = F.padd(F.padd(mu[0], F.pmul(mu[1], F.padd(P, Q))), F.pmul(mu[2], F.pmul(P, Q)))
        idok &= F.trim(F.pderiv(F.pmul(eps(F, e, P), eps(F, e, Q)))) == F.psq(F.pmul(F.padd(P, Q), B))
    ep = eps(F, e, psi)
    odd = L.odd_part(F, ep)
    inD = [a for a in D if F.peval(odd, a) == 0]
    mult = sorted({L.mult_at(F, ep, a) for a in D})
    gD = [a for a in D if g and F.peval(g, a) == 0]
    p_inf = F.deg(psi)
    print(f"  {name}: n = {n}, Delta = {Delta}, W = {W}, deg(e1, e3, e5) = {tuple(L.deg(F, x) for x in e)}, "
          f"bounds {(W - Delta, W - 3 * Delta, W - 5 * Delta)}")
    print(f"     deg(mu01, mu02, mu12) = {tuple(L.deg(F, x) for x in mu)}, deg gcd = {L.deg(F, g) if g else None} "
          f"({len(gD)} of its roots in D); degree drops of (e_i e_j)' at infinity: {drops}; "
          f"p_inf - Delta = {p_inf - Delta}")
    print(f"     word = mu02/mu12 = mu01/mu02 on D: {w_ok}; Lambda_D | e3: {e3_ok}; e1 = e5 y^4 on D: {e1_ok}; "
          f"identity (eps_P eps_Q)' = ((P+Q) B)^2: {idok}")
    print(f"     eps_psi: degree {F.deg(ep)}, multiplicities on D {mult}, odd part of degree {F.deg(odd)} "
          f"with {len(inD)} roots in D: |D+ \\ D| = {F.deg(odd) - len(inD)}")


def part_A():
    print("# A. rate 1/2 families")
    rnd = random.Random(5)
    for (m, N, kind, seed) in ((8, 4, "rand", 3), (8, 5, "rand", 4), (12, 6, "rand", 5), (12, 6, "span", 0)):
        F = L.GF(m)
        n = 1 << N
        basis = L.domain(F, N, kind, seed)
        D = F.span(basis)
        LD = F.subspace_poly(basis)
        epsc = LD[n // 2]
        M = F.trim(LD[: n // 4 + 1])
        c = F.mul(LD[n // 4], LD[n // 4])
        psi = [0] * (3 * n // 4 - 1) + [1]
        e5 = F.pmul([0, 0, 0, 1], M)
        e3 = F.pmul(F.padd(F.pmul([0, epsc], M), [0, c]), LD)
        e1h = F.pmul(M[1:], F.pmul(LD, F.psq(LD)))
        psi2 = F.psq(psi)
        e1 = F.padd(F.padd(e1h, F.pmul(e3, psi2)), F.pmul(e5, F.psq(psi2)))
        report(F, f"11/16 family, {kind} subspace in GF(2^{m})", D, (e1, e3, e5), psi, 11 * n // 4 - 2, n // 2 - 1, rnd)
    for (m, N, j) in ((8, 4, 2), (12, 6, 4)):
        F = L.GF(m)
        n = 1 << N
        D = [x for x in range(F.q) if F.pow(x, n) == x]
        assert len(D) == n
        Delta = n // 2 - 1
        e = 3 * n // 4 - j
        psi = [0] * e + [1]
        e5 = [0] * (4 * j) + [1]
        Ln = F.padd([0] * n + [1], [0, 1])
        e1h = F.padd([0] * (n + 2) + [1], F.pmul([0, 1], F.psq(Ln)))
        e1 = e1h                                  # note 45, Theorem 7: a = (X^(2j) Y^2 + X^(n/2+1))^2 + X (X^n + X)^2
        W = max(4 * j + 5 * Delta, 2 * n + 1 + Delta, 2 * n + e)
        report(F, f"27/40 family, D = F_{n} in GF(2^{m}), j = {j}", D, (e1, [], e5), psi, W, Delta, rnd)


def part_B_C():
    print("# B. the 5n/8 family as a pencil at infinity; C. the converse")
    five = importlib.import_module("05_check_five_eighths")
    F = L.GF(16)
    rnd = random.Random(9)
    for N in (5, 6):
        n = 1 << N
        D = list(range(n))                     # span(1, x, .., x^(N-1)); bit i of a mask = the point i
        members = sorted(five.enumerate_class(N))
        LW = F.subspace_poly([1 << i for i in range(N - 3)])
        psi = F.pmul([0] * (n // 2) + [1], LW)
        p = 5 * n // 8
        Delta = n // 2
        sample = members if N == 5 else rnd.sample(members, 400)
        okdeg = True
        for msk in sample:
            S = L.mask_pts(D, msk)
            assert len(S) == p
            P = F.padd(psi, L.locator(F, S))
            okdeg &= L.deg(F, P) <= Delta
        g = 2 * ((p - Delta) // 2)
        rows = L.rows_inf(F, D, g)
        code = L.f2_kernel(rows)
        base = members[0]
        allin = all(L.syndrome(rows, msk ^ base) == 0 for msk in members)
        dists = {}
        for _ in range(4000):
            a, b = rnd.sample(members, 2)
            w = L.weight(a ^ b)
            dists[w] = dists.get(w, 0) + 1
        # words of weight p in the coset base + Gamma_inf(g), and how many are members (exact test)
        tot_w, mem_w = None, None
        if len(code) <= 22:
            mset = set(members)
            tot_w = mem_w = 0
            cur = base
            for i in range(1, 1 << len(code)):
                cur ^= code[(i & -i).bit_length() - 1]
                if L.weight(cur) == p:
                    tot_w += 1
                    mem_w += cur in mset
            if L.weight(base) == p:
                tot_w += 1
                mem_w += 1
        print(f"  N = {N}: {len(members)} members (56 n - 392 = {56 * n - 392}); P_i = psi + Lambda_S of degree <= n/2 on "
              f"{len(sample)} checked: {okdeg}; g = {g}: dim Gamma_inf(g) = {len(code)} (RM(2,N): {L.rm_dim(2, N)}); "
              f"all S_i xor S_1 in the code: {allin}; distances seen {dict(sorted(dists.items()))}")
        if tot_w is not None:
            print(f"     words of weight {p} in the coset S_1 + Gamma_inf({g}): {tot_w}, of which list members "
                  f"(same top as psi): {mem_w}")
        sys.stdout.flush()
    # C: explicit counterexample to the converse
    F = L.GF(8)
    N = 6
    basis = L.domain(F, N, "rand", 7)
    D = F.span(basis)
    V = F.span(basis[:2])
    cst = basis[2]
    R = [d for d in D if d not in set(V) | {v ^ cst for v in V}][:20]
    S1, S2 = V + R, [v ^ cst for v in V] + R
    T = L.subset_mask(D, V) ^ L.subset_mask(D, [v ^ cst for v in V])
    g = 6
    rows = L.rows_inf(F, D, g)
    dd = L.deg(F, F.padd(L.locator(F, S1), L.locator(F, S2)))
    print(f"  C: N = 6, S_1 = V + R, S_2 = (c + V) + R, |V| = 4, |R| = 20, p = 24: S_1 xor S_2 in Gamma_inf({g}): "
          f"{L.syndrome(rows, T) == 0}; deg(Lambda_S1 + Lambda_S2) = {dd}; the claimed bound p - g - 1 = {24 - g - 1}")


if __name__ == "__main__":
    part_A()
    sys.stdout.flush()
    part_B_C()
