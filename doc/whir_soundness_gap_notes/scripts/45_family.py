#!/usr/bin/env python3
"""45_family.py: closed form of the singular first integral of efficiency 11/16 (note 40, Observation 12),
for 45-rate-half-second-attempt.md, Theorem 6.

D an F2-subspace of dimension N, n = 2^N, L_D = X^n + eps X^(n/2) + M(X), M = sum_{j <= N-2} e_j X^(2^j),
psi = X^(3n/4 - 1). Claim:
    a = X^3 M (Y - psi)^4 + X (eps M + e_{N-2}^2) L_D (Y - psi)^2 + (M / X) L_D^3,      E = (Y - psi) a,
has dE of contact order >= 4 on all n lines of the word psi, deg_X a(X, 0) = 2n + n/4 - 1, and
wdeg(dE) = 11n/4 - 2 for the weights (1, D, D), D = n/2 - 1; gcd(E_Y, E_X) = 1.

Checks, over GF(2^8), for several subspaces: (1) the 7 Taylor conditions of note 40 Proposition 9 at every point,
(2) the weighted degree, (3) coprimality of E_Y and E_X at random X, (4) that E agrees, modulo F[X^2, Y^2] and a
scalar, with the unique solution of smallest weighted degree found by linear algebra (45_lattice).

(5) the family of Theorem 7 on D = F_16: the 7 conditions and the weighted degree formula (at n = 256 the family is
the solution of smallest weighted degree for X^178 on GF(256): DOM=fk8 ./45_scale 8 178 gives W_min = 691 = W(14)).

Run: python3 45_family.py [N ...]      default N = 4 5 6
"""
import sys
import random
from importlib import import_module

lib = import_module("40_lib")
lat = import_module("45_lattice")
srch = import_module("40_search")
mul, inv, fpow = lib.mul, lib.inv, lib.fpow


def padd(p, q):
    r = [0] * max(len(p), len(q))
    for i, a in enumerate(p):
        r[i] ^= a
    for i, a in enumerate(q):
        r[i] ^= a
    return r


def pmul(p, q):
    if not p or not q:
        return []
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] ^= mul(a, b)
    return r


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def closed_form(D, n):
    """coefficient lists e_k(X), k = 0..5, of E = (Y - psi) a."""
    LD = [1]
    for al in D:
        LD = pmul(LD, [al, 1])
    eps = LD[n // 2]
    M = LD[: n // 4 + 1]
    c = mul(LD[n // 4], LD[n // 4])
    psi = [0] * (3 * n // 4 - 1) + [1]
    psi2, psi4 = pmul(psi, psi), pmul(pmul(psi, psi), pmul(psi, psi))
    e5 = [0, 0, 0] + M
    m3 = padd([0] + [mul(eps, x) for x in M], [0, c])
    e3 = pmul(m3, LD)
    nu = M[1:]
    e1 = padd(padd(pmul(e5, psi4), pmul(e3, psi2)), pmul(nu, pmul(LD, pmul(LD, LD))))
    a = {4: e5, 2: e3, 0: trim(e1)}
    E = {}
    for k, co in a.items():       # (Y - psi) * a
        E[k + 1] = padd(E.get(k + 1, []), co)
        E[k] = padd(E.get(k, []), pmul(psi, co))
    return {k: trim(v) for k, v in E.items()}, a, LD


def reduce_mod_squares(E):
    """drop monomials X^i Y^k with i, k both even."""
    return {(i, k): c for k, co in E.items() for i, c in enumerate(co) if c and ((i & 1) or (k & 1))}


def wdeg_dE(Er, Dc):
    W = -1
    for (i, k) in Er:
        W = max(W, i + Dc * k if (k & 1) else i - 1 + Dc * k)
    return W


def run(N, seed, rng):
    n = 1 << N
    Dc = n // 2 - 1
    D = lib.subspace_domain(N, seed=seed)
    E, a, LD = closed_form(D, n)
    Er = reduce_mod_squares(E)
    monos = sorted(Er)
    vec = [Er[m] for m in monos]
    y = [fpow(al, 3 * n // 4 - 1) for al in D]
    bad = 0
    for al, be in zip(D, y):
        for (r, q) in lib.contact_conditions(2):
            row = lib.taylor_row(monos, al, be, r, q)
            t = 0
            for cf, x in zip(row, vec):
                t ^= mul(cf, x)
            bad += 1 if t else 0
    W = wdeg_dE(Er, Dc)
    degs = srch.coprime_test(monos, vec, D, rng)
    msg = (f"  N = {N}, seed {seed}: violated conditions {bad} of {7 * n}; wdeg(dE) = {W} (11n/4 - 2 = {11 * n // 4 - 2}); "
           f"deg e_1 of a = {len(a[0]) - 1} (2n + n/4 - 1 = {2 * n + n // 4 - 1}); gcd degrees at 3 random X: {degs}")
    if N <= 5:
        # compare with the unique solution of the linear system at W = 11n/4 - 2
        ms = lat.support(11 * n // 4 - 2, Dc)
        basis = lib.nullspace(lat.rows_for(ms, list(zip(D, y))), len(ms))
        sol = {m: c for m, c in zip(ms, basis[0]) if c}
        same = set(sol) == set(Er)
        if same:
            m0 = next(iter(sol))
            sc = mul(Er[m0], inv(sol[m0]))
            same = all(Er[m] == mul(sc, sol[m]) for m in sol)
        msg += f"; nullity at that W: {len(basis)}; equal to the closed form up to a scalar: {same}"
    print(msg)


def field_family(rng):
    """Theorem 7: D = F_16 inside GF(2^8), word X^(3n/4 - j), j even,
    E = (Y - X^e) a,  a = (X^(2j) Y^2 + X^(n/2+1))^2 + X (X^n + X)^2,
    W(j) = max(4j + 5D, 2n + 1 + D, 11n/4 - j); and the section equation eta A(X, P) = (gamma + X^(e/2)) (X^n + X)."""
    n = 16
    D = [x for x in range(256) if fpow(x, 16) == x]
    print("  family on D = F_16 (GF(16) inside GF(2^8)):")
    for Dc in (n // 2 - 1, n // 2 + 1):
        for j in (2, 4):
            e = 3 * n // 4 - j
            psi = [0] * e + [1]
            a = {4: [0] * (4 * j) + [1], 0: trim(padd(padd([0] * (2 * n + 1) + [1], [0] * (n + 2) + [1]), [0, 0, 0, 1]))}
            E = {}
            for k, co in a.items():
                E[k + 1] = padd(E.get(k + 1, []), co)
                E[k] = padd(E.get(k, []), pmul(psi, co))
            Er = reduce_mod_squares({k: trim(v) for k, v in E.items()})
            monos = sorted(Er)
            vec = [Er[m] for m in monos]
            bad = 0
            for al in D:
                be = fpow(al, e)
                for (r, q) in lib.contact_conditions(2):
                    row = lib.taylor_row(monos, al, be, r, q)
                    t = 0
                    for cf, x in zip(row, vec):
                        t ^= mul(cf, x)
                    bad += 1 if t else 0
            W = wdeg_dE(Er, Dc)
            Wf = max(4 * j + 5 * Dc, 2 * n + 1 + Dc, 2 * n + e)
            degs = srch.coprime_test(monos, vec, D, rng)
            # the section identity: odd part of E(X, P) = X (eta A(X, P) + (gamma + X^(e/2)) (X^n + X))^2 for P = gamma^2 + X eta^2
            ok = True
            for _ in range(5):
                ga = [rng.randrange(256) for _ in range(4)]
                et = [rng.randrange(256) for _ in range(4)]
                P = padd(pmul(ga, ga), [0] + pmul(et, et))
                P2 = pmul(P, P)
                AP = padd(pmul([0] * (2 * j) + [1], P2), [0] * (n // 2 + 1) + [1])
                Bp = padd([0] * n + [1], [0, 1])
                aP = padd(pmul(AP, AP), [0] + pmul(Bp, Bp))
                EP = pmul(padd(P, psi), aP)
                odd = [c if (i & 1) else 0 for i, c in enumerate(EP)]
                br = padd(pmul(et, AP), pmul(padd(ga, [0] * (e // 2) + [1]), Bp))
                ok = ok and trim(odd) == trim([0] + pmul(br, br))
            print(f"    D = {Dc}, j = {j}, word X^{e}: violated conditions {bad} of {7 * n}; wdeg(dE) = {W}, formula {Wf}; gcd degrees {degs}; "
                  f"section identity on 5 random P: {ok}")


def main():
    Ns = [int(x) for x in sys.argv[1:]] or [4, 5, 6]
    rng = random.Random(7)
    for N in Ns:
        for seed in (3, 4, 5):
            run(N, seed, rng)
            sys.stdout.flush()
    field_family(rng)


if __name__ == "__main__":
    main()
