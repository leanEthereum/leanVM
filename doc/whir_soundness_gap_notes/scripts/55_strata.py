#!/usr/bin/env python3
"""55_strata.py: referee recomputation of note 53, Section 5 (Propositions 5.1 and 5.2). Own code (55_lib.py).

A. Proposition 5.1 (formal model), emulated: a random basis of an N-dimensional subspace of GF(2^607), N = 6..10.
   The whole profile g -> dim Gamma_inf(g), 0 <= g <= n/2, is computed exactly by one F_2-elimination and compared
   with dim RM(N - 1 - w(g), N), w(g) = max binary weight of k <= g. The endpoints g = 2^j - 2, 2^j - 1 are printed.
   The same on a random basis in GF(2^64) for N = 6..9, with the entries where the dimension exceeds the formal one.
B. Proposition 5.2 on the real field GF(2^64) = F_2[x]/(x^64 + x^4 + x^3 + x + 1): D = span(1, x, .., x^(N-1)) and
   one random subspace, N = 8, 10, 12: exact dim Gamma_inf(g) at g = floor(c n), c in {0.175, 0.19, 0.2065, 0.238,
   0.25}, against the stratum bound max_d [dim RM(d, N) - 64 c_g(d)]; and the check that the bound is a lower bound
   for every g <= n/4.
C. The stratum bound at real sizes (exact integers), N = 25, 28, m = 64, 128, at the thresholds of the note; the
   smallest m for which the bound equals the formal value.
Run: python3 55_strata.py [quick]
"""
import importlib
import random
import sys
import time

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("55_lib")


def w_of(g):
    return max(bin(k).count("1") for k in range(g + 1))


def formal_dim(N, g):
    # w(g) = j for 2^j - 1 <= g < 2^(j+1) - 1
    j = (g + 1).bit_length() - 1
    return L.rm_dim(N - 1 - j, N)


def part_A(quick):
    rnd = random.Random(5504)
    assert all(formal_dim(8, g) == L.rm_dim(8 - 1 - w_of(g), 8) for g in range(0, 200))
    F = L.GFb(607)
    print("A. formal model emulated in GF(2^607), random bases; profile on 0 <= g <= n/2")
    for N in range(6, (9 if quick else 11)):
        t = time.time()
        n = 1 << N
        D = F.span(F.rand_basis(rnd, N))
        gmax = n // 2
        prof = L.gamma_inf_profile(F, D, gmax)
        bad = [g for g in range(gmax + 1) if prof[g] != formal_dim(N, g)]
        ends = []
        for j in range(1, N):
            for g in ((1 << j) - 2, (1 << j) - 1):
                if 0 <= g <= gmax:
                    ends.append(f"g={g}: {prof[g]}")
        print(f"   N = {N}: dim Gamma_inf(g) = dim RM(N-1-w(g), N) for all g in [0, {gmax}]: {not bad}"
              + (f" MISMATCH at {bad[:10]}" if bad else "") + f"   [{time.time() - t:.1f} s]")
        print(f"      endpoints: {', '.join(ends)}")
        print(f"      RM(2,N) range: g = n/8 - 2 = {n // 8 - 2}: {prof[n // 8 - 2]} (RM(3,N): {L.rm_dim(3, N)}); "
              f"g = n/8 - 1 = {n // 8 - 1}: {prof[n // 8 - 1]} (RM(2,N): {L.rm_dim(2, N)}); "
              f"g = n/4 - 2 = {n // 4 - 2}: {prof[n // 4 - 2]}; g = n/4 - 1: {prof[n // 4 - 1]} (RM(1,N): {N + 1}); "
              f"g = n/2 - 2: {prof[n // 2 - 2]}; g = n/2 - 1: {prof[n // 2 - 1]}")
    F64 = L.GFb(64)
    print("   the same on a random basis in GF(2^64) (not generic enough from N = 9 on):")
    for N in range(6, (8 if quick else 10)):
        n = 1 << N
        D = F64.span(F64.rand_basis(rnd, N))
        prof = L.gamma_inf_profile(F64, D, n // 2)
        bad = [(g, prof[g], formal_dim(N, g)) for g in range(n // 2 + 1) if prof[g] != formal_dim(N, g)]
        lowb = all(prof[g] >= L.stratum_bound(N, 64, g)[0] for g in range(n // 2 + 1))
        eqb = sum(prof[g] == max(L.stratum_bound(N, 64, g)[0], formal_dim(N, g)) for g in range(n // 2 + 1))
        print(f"   N = {N}: entries above the formal value: {len(bad)}"
              + (f", first (g, dim, formal): {bad[:4]}" if bad else "")
              + f"; stratum bound is a lower bound everywhere: {lowb}; equal to max(stratum, formal) at {eqb}/{n // 2 + 1} g")


def part_B(quick):
    rnd = random.Random(5505)
    F = L.GFb(64)
    assert F.mod == (1 << 64) | 0b11011
    print("B. GF(2^64) = F_2[x]/(x^64 + x^4 + x^3 + x + 1): exact dim Gamma_inf(g) / stratum bound (formal value)")
    claimed = {8: (41, 37, 37, 37, 9), 10: (112, 56, 56, 56, 11), 12: (235, 171, 171, 79, 16)}
    cs = ((175, 1000), (19, 100), (2065, 10000), (238, 1000), (25, 100))
    for N in ((8, 10) if quick else (8, 10, 12)):
        n = 1 << N
        gs = [c * n // d for (c, d) in cs]
        for kind in ("span", "rand"):
            t = time.time()
            basis = [1 << i for i in range(N)] if kind == "span" else F.rand_basis(rnd, N)
            D = F.span(basis)
            prof = L.gamma_inf_profile(F, D, n // 4)
            cells = []
            for g in gs:
                sb = L.stratum_bound(N, 64, g)
                cells.append(f"g={g}: {prof[g]}/{sb[0]} ({formal_dim(N, g)})")
            lowb = all(prof[g] >= max(L.stratum_bound(N, 64, g)[0], formal_dim(N, g)) for g in range(n // 4 + 1))
            neq = sum(prof[g] != max(L.stratum_bound(N, 64, g)[0], formal_dim(N, g)) for g in range(n // 4 + 1))
            match = "" if kind != "span" else f"  matches the table of note 53: {tuple(prof[g] for g in gs) == claimed[N]}"
            print(f"   N = {N}, {kind}: {'; '.join(cells)}{match}")
            print(f"      max(stratum, formal) <= dim for all g <= n/4: {lowb}; strict at {neq} of {n // 4 + 1} values of g"
                  f"   [{time.time() - t:.1f} s]")


def part_B2():
    """five more random 12-dimensional subspaces of GF(2^64): the entry g = n/4 (16 on the span, 15 or 16 on a
    random subspace)."""
    F = L.GFb(64)
    N = 12
    n = 1 << N
    gs = [c * n // d for (c, d) in ((175, 1000), (19, 100), (2065, 10000), (238, 1000), (25, 100))]
    for seed in (1, 2, 3, 4, 5):
        rnd = random.Random(seed)
        prof = L.gamma_inf_profile(F, F.span(F.rand_basis(rnd, N)), n // 4)
        neq = sum(prof[g] != max(L.stratum_bound(N, 64, g)[0], formal_dim(N, g)) for g in range(n // 4 + 1))
        print(f"   N = 12, random subspace, seed {seed}: {[prof[g] for g in gs]}; above max(stratum, formal) at {neq} "
              f"values of g <= n/4")


def part_C():
    print("C. stratum bound at real sizes, g = A - Delta - 1, Delta = rho n + 5 (value, degree d, c_g(d))")
    rows = (("1/2", 2, 700840), ("1/2", 2, 706500), ("1/4", 4, 488109), ("1/8", 8, 340086), ("1/16", 16, 237478))
    claimed = {("1/2", 700840): ((56706, 216554), (11446, 48198)), ("1/2", 706500): ((47938, 204330), (9644, 45638)),
               ("1/4", 488109): ((16566, 54086), (4780, 12126)), ("1/8", 340086): ((36598, 178730), (9388, 40390)),
               ("1/16", 237478): ((122178, 637202), (33718, 139114))}
    allok = True
    for (name, inv, a6) in rows:
        out = []
        got = []
        for m in (64, 128):
            vals = []
            for N in (25, 28):
                n = 1 << N
                A = -(-a6 * n // 10 ** 6)
                Delta = n // inv + 5
                g = A - Delta - 1
                v = L.stratum_bound(N, m, g)
                vals.append(v[0])
                out.append(f"m={m}, N={N}: {v[0]} (d={v[1]}, c={v[2]})")
            got.append(tuple(vals))
        ok = tuple(got) == claimed[(name, a6)]
        allok &= ok
        n = 1 << 25
        g = -(-a6 * n // 10 ** 6) - (n // inv + 5) - 1
        print(f"   rate {name}, a = {a6 / 1e6}: g/n = {g / n:.4f}; " + "; ".join(out) + f"; as in note 53: {ok}")
    for N in (25, 28):
        n = 1 << N
        g = -(-7065 * n // 10000) - (n // 2 + 5) - 1
        formal = formal_dim(N, g)
        # smallest m with stratum bound <= formal
        lo, hi = 1, 1 << 20
        while lo < hi:
            mid = (lo + hi) // 2
            if L.stratum_bound(N, mid, g)[0] <= formal:
                hi = mid
            else:
                lo = mid + 1
        print(f"   N = {N}, g = 0.2065 n: formal dimension {formal}; the stratum bound equals it only for m >= {lo}")
    print(f"   all real-size numbers as in note 53: {allok}")


def inv_euclid(F, a):
    """inverse in GF(2^m) by the extended Euclidean algorithm on F_2-polynomials."""
    r0, r1, s0, s1 = F.mod, a, 0, 1
    while r1:
        d = r0.bit_length() - r1.bit_length()
        if d < 0:
            r0, r1, s0, s1 = r1, r0, s1, s0
            continue
        r0 ^= r1 << d
        s0 ^= s1 << d
    assert r0 == 1
    return L.polymod(s0, F.mod, F.m)


def part_D():
    """Section 3.2 (ii): in the formal model a Boolean function of degree exactly r has its first nonzero power sum
    at k = 2^(N-r) - 1 (so deg_X 1_T = n - 2^(N-r)). Proposition 5.3 (a): the elements 1/(beta - alpha) are
    F_2-independent for beta in D, beta algebraic over F_2, beta generic."""
    rnd = random.Random(5507)
    F = L.GFb(607)
    N = 7
    n = 1 << N
    alpha = F.span(F.rand_basis(rnd, N))
    ok = tot = 0
    for r in range(1, N):
        for _ in range(4):
            # random function of degree exactly r: random ANF with a monomial of degree r
            anf = [0] * n
            for a in range(n):
                if bin(a).count("1") <= r and rnd.random() < 0.3:
                    anf[a] = 1
            top = rnd.choice([a for a in range(n) if bin(a).count("1") == r])
            anf[top] = 1
            f = list(anf)
            for i in range(N):
                for a in range(n):
                    if a & (1 << i):
                        f[a] ^= f[a ^ (1 << i)]
            pts = [alpha[a] for a in range(n) if f[a]]
            k0 = None
            pw = [1] * len(pts)
            for k in range(0, n):
                if k:
                    pw = [F.mul(v, x) for v, x in zip(pw, pts)]
                sm = len(pts) & 1 if k == 0 else 0
                if k:
                    for v in pw:
                        sm ^= v
                if sm:
                    k0 = k
                    break
            tot += 1
            ok += k0 == (1 << (N - r)) - 1
    print(f"D. formal model emulated (GF(2^607), N = {N}): first nonzero power sum of a function of degree exactly r is "
          f"p_(2^(N-r) - 1): {ok}/{tot}")
    res = []
    for N in (5, 6, 7):
        n = 1 << N
        D = F.span(F.rand_basis(rnd, N))
        for kind in ("beta in D", "beta = 1 (algebraic)", "beta random"):
            beta = D[rnd.randrange(1, n)] if kind == "beta in D" else (1 if kind.startswith("beta = 1") else rnd.getrandbits(600) | 1)
            vals = [inv_euclid(F, beta ^ a) for a in D if a != beta]
            res.append(f"N={N}, {kind}: rank {L.f2_rank(vals)} of {len(vals)}")
    F64 = L.GFb(64)
    # an element of GF(16) inside GF(2^64): a root of x^16 = x other than 0, 1: t^((2^64-1)/15)
    t = 2
    w = F64.pow(t, ((1 << 64) - 1) // 15)
    assert w not in (0, 1) and F64.pow(w, 16) == w
    D = F64.span(F64.rand_basis(rnd, 5))
    vals = [F64.inv(w ^ a) for a in D]
    res.append(f"N=5 in GF(2^64), beta in GF(16) \\ F_2: rank {L.f2_rank(vals)} of {len(vals)}")
    print("   Proposition 5.3 (a), emulated: " + "; ".join(res))


def part_E():
    """spot checks of the other tables of note 53: Section 4 (dim Gamma_inf(n/4)), Section 5.3 (the span effect at
    small g in GF(2^64)), Section 7 (iii) (stratum bound at g = n/4, N = 25)."""
    rnd = random.Random(5508)
    out = []
    for (m, N, kind, claim) in ((8, 4, "rand", 5), (8, 5, "rand", 8), (12, 6, "rand", 10), (16, 7, "span", 13),
                                (16, 8, "span", 21), (5, 5, "field", 11), (6, 6, "field", 18), (7, 7, "field", 29)):
        F = L.GFs(m)
        basis = F.rand_basis(rnd, N) if kind == "rand" else [1 << i for i in range(N)]
        n = 1 << N
        d = L.gamma_inf_profile(F, F.span(basis), n // 4)[n // 4]
        out.append(f"GF(2^{m}) N={N} {kind}: {d} (note: {claim}, stratum max(N+1, dim RM(2,N) - m) = "
                   f"{max(N + 1, L.rm_dim(2, N) - m)})")
    print("E. dim Gamma_inf(n/4), Section 4 of note 53: " + "; ".join(out))
    F = L.GFb(64)
    claims = {5: {3: (17, 16)}, 6: {3: (45, 42), 5: (42, 42), 7: (24, 22)}, 7: {3: (105, 99), 7: (74, 64)}}
    out = []
    for N, cl in claims.items():
        n = 1 << N
        ps = L.gamma_inf_profile(F, F.span([1 << i for i in range(N)]), 8)
        pr = L.gamma_inf_profile(F, F.span(F.rand_basis(rnd, N)), 8)
        for g, (cs, cr) in cl.items():
            out.append(f"N={N}, g={g}: span {ps[g]}, random {pr[g]} (note: {cs}, {cr})")
    print("   Section 5.3, GF(2^64): " + "; ".join(out))
    v = L.stratum_bound(25, 64, 1 << 23)
    print(f"   Section 7 (iii): stratum bound for Gamma_inf(n/4), N = 25, m = 64: {v[0]} (d = {v[1]}); note: 1154")


def main():
    quick = len(sys.argv) > 1 and sys.argv[1] == "quick"
    part_C()
    part_A(quick)
    part_B(quick)
    if not quick:
        part_B2()
    part_D()
    part_E()


if __name__ == "__main__":
    main()
