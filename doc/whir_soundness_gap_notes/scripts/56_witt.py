#!/usr/bin/env python3
"""Researcher 56. Checks of Theorem 1 (Witt criterion with the exact order), Lemma 2 (digit degrees and leading
carry coefficients) and Theorem 3 (active conditions on a Walsh level) of 56-witt-real-field.md.

 A  ord_X(Lambda_c - 1) = min over odd k of k 2^v2(sum c(s)[s]^k), for integer vectors c on arbitrary supports
    (sets, multisets, and pencil members S + 2 Roots(theta) with roots outside D).
 B  The multilinear coefficients h_A^(k) of x -> [s(x)]^k have valuation >= (|A| - wt(k))^+, and
    (h_A / 2^(|A| - wt k) mod 2)^(2^(|A| - wt k)) = sum over ordered ways of writing k 2^(|A| - wt k) as a sum
    of |A| powers of two of prod b_i^(2^t_i).
 C  For c with Walsh spectrum = c^(0) mod 2^r: v2(sum c(s)[s]^k) >= r - wt(k), the first block of Lambda_c is
    given by the leading coefficients, and the image of the lattice in the units modulo X^(g+1) has at most
    |K|^C_g(r) elements, C_g(r) = #{i < g : wt(i) >= r - 1}; its exact order is printed.
 D  The deepest non-formal pair found by 56_acc32 at n = 32 (GF(2^6), D = span(1, .., x^4), two 10-sets):
    Z_S - Z_S' is a constant, the hyperplane counts agree modulo 4 and not modulo 8 (Walsh level 3).
usage: 56_witt.py [A|B|C|D|all]"""
import importlib.util
import os
import random
import sys
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lib56", os.path.join(HERE, "56_lib.py"))
lib = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lib)
GF, GR, wt, v2 = lib.GF, lib.GR, lib.wt, lib.v2


def check_A(rng):
    print("== A. Theorem 1: ord_X(Lambda_c - 1) = min_k k 2^v2(p~_k(c)) ==")
    total = 0
    hist = {}
    for m in (4, 5, 6, 8, 11):
        F = GF(m)
        G = 40
        R = GR(F, 8)
        # (i) random integer vectors on random supports
        for _ in range(300):
            supp = rng.sample(range(1, F.q), rng.randrange(2, min(F.q - 1, 14)))
            c = {s: rng.choice([-3, -2, -1, 1, 2, 3, 4, -4, 8]) for s in supp}
            o = F.order_of(F.lam(c, G))
            assert o == lib.witt_order(R, c, G), (m, c)
            hist[o] = hist.get(o, 0) + 1
            total += 1
        # (ii) lattice elements of Walsh level r on a subspace: large orders
        for N in (4, 5):
            if N > m:
                continue
            for basis in (lib.power_basis(F, N), lib.random_basis(F, N, rng)):
                pts = lib.span(F, basis)
                for r in range(1, N + 1):
                    for _ in range(40):
                        c = [0] * (1 << N)
                        for A in range(1, 1 << N):
                            g = rng.randrange(-2, 3) << max(0, r - wt(A))
                            if g:
                                B = A
                                while True:
                                    c[B] += g if (wt(A) - wt(B)) % 2 == 0 else -g
                                    if B == 0:
                                        break
                                    B = (B - 1) & A
                        cd = {pts[x]: c[x] for x in range(1 << N) if c[x]}
                        o = F.order_of(F.lam(cd, G))
                        assert o == lib.witt_order(R, cd, G), (m, N, r)
                        assert o >= min(G + 1, 1 << (r - 1)), "Theorem W violated"
                        hist[o] = hist.get(o, 0) + 1
                        total += 1
    # (iii) pairs of sets with a long common top in small fields (exhaustive, n = 16)
    for m in (4, 5, 6):
        F = GF(m)
        R = GR(F, 6)
        pts = lib.span(F, lib.power_basis(F, 4) if m > 4 else [1, 2, 4, 8])
        for T in (5, 6, 7):
            seen = {}
            pairs = 0
            for S in combinations(range(16), T):
                key = tuple(F.lam([(pts[x], 1) for x in S], 4)[1:])
                seen.setdefault(key, []).append(S)
            for cls in seen.values():
                for i in range(1, min(len(cls), 6)):
                    c = {}
                    for x in cls[0]:
                        c[pts[x]] = c.get(pts[x], 0) + 1
                    for x in cls[i]:
                        c[pts[x]] = c.get(pts[x], 0) - 1
                    c = {s: e for s, e in c.items() if e}
                    o = F.order_of(F.lam(c, 16))
                    assert o >= 5 and o == lib.witt_order(R, c, 16)
                    # direct: the degree of Z_S - Z_S'
                    za, zb = F.locator([pts[x] for x in cls[0]]), F.locator([pts[x] for x in cls[i]])
                    d = max([j for j in range(T + 1) if za[j] != zb[j]], default=-1)
                    assert d == T - o, (d, T, o)
                    pairs += 1
                    total += 1
            print(f"   n=16 in GF(2^{m}), {T}-sets sharing e_1..e_4: {pairs} pairs checked, "
                  f"deg(Z_S - Z_S') = T - (Witt order) in all")
    # (iv) pencil members: S_i + 2 Roots(theta_i), roots of theta anywhere in K
    for m in (6, 8):
        F = GF(m)
        R = GR(F, 8)
        pts = lib.span(F, lib.random_basis(F, 5, rng))
        for _ in range(300):
            c = {}
            for sign in (1, -1):
                for x in rng.sample(range(32), rng.randrange(3, 12)):
                    c[pts[x]] = c.get(pts[x], 0) + sign
                for _ in range(rng.randrange(0, 5)):
                    rho = rng.randrange(1, F.q)
                    c[rho] = c.get(rho, 0) + 2 * sign
            c = {s: e for s, e in c.items() if e}
            o = F.order_of(F.lam(c, 40))
            assert o == lib.witt_order(R, c, 40)
            total += 1
    print(f"   {total} vectors, no failure; orders seen: "
          + ", ".join(f"{o}:{hist[o]}" for o in sorted(hist)))


def compositions_pow2(M, parts):
    """All tuples (t_1..t_parts), t_i >= 0, with sum 2^t_i = M."""
    if parts == 0:
        if M == 0:
            yield ()
        return
    if M < parts:
        return
    t = 0
    while (1 << t) <= M - (parts - 1):
        for rest in compositions_pow2(M - (1 << t), parts - 1):
            yield (t,) + rest
        t += 1


def coeffs_h(R, pts, N, k):
    """h_A = sum_{B subset A} (-1)^(|A|-|B|) [s_B]^k for all A (Moebius transform), as GR elements."""
    m, mask = R.m, R.mask
    h = [list(R.teich(pts[x], k)) if pts[x] else [0] * m for x in range(1 << N)]
    for i in range(N):
        for x in range(1 << N):
            if x >> i & 1:
                a, b = h[x], h[x ^ (1 << i)]
                h[x] = [(a[j] - b[j]) & mask for j in range(m)]
    return h


def check_B(rng):
    print("== B. Lemma 2: digit degrees of x -> [s(x)]^k and the leading carry coefficients ==")
    for m, N, kind in ((7, 6, "power"), (12, 6, "random"), (16, 7, "power"), (16, 7, "random")):
        F = GF(m)
        R = GR(F, 10)
        basis = lib.power_basis(F, N) if kind == "power" else lib.random_basis(F, N, rng)
        pts = lib.span(F, basis)
        tested = exact = lead = 0
        for k in range(1, 40, 2):
            h = coeffs_h(R, pts, N, k)
            w = wt(k)
            for A in range(1, 1 << N):
                a = wt(A)
                val = R.val(h[A])
                lo = max(0, a - w)
                assert val >= lo, (m, N, k, A, val)
                tested += 1
                exact += val == lo
                if a >= w:
                    u = a - w
                    idx = [i for i in range(N) if A >> i & 1]
                    acc = 0
                    for t in compositions_pow2(k << u, a):
                        p = 1
                        for i, ti in zip(idx, t):
                            p = F.mul(p, F.pow(basis[i], 1 << ti))
                        acc ^= p
                    eta = R.red(h[A], u)
                    assert F.pow(eta, 1 << u) == acc, (m, N, k, A)
                    lead += 1
        print(f"   GF(2^{m}), N={N}, {kind} basis, odd k < 40: {tested} coefficients, valuation >= (|A| - wt k)^+ "
              f"in all, equal in {exact}; leading coefficient formula checked {lead} times")


def lattice_generators(N, r):
    """Generators 2^((r - |A|)^+) eps_A of L^(r), as integer vectors on F_2^N."""
    gens = []
    for A in range(1, 1 << N):
        g = 1 << max(0, r - wt(A))
        c = [0] * (1 << N)
        B = A
        while True:
            c[B] = g if (wt(A) - wt(B)) % 2 == 0 else -g
            if B == 0:
                break
            B = (B - 1) & A
        gens.append((A, c))
    return gens


def module_order_log2(rows, L):
    """log2 of the order of the Z-span of integer rows modulo 2^L (all columns modulo 2^L)."""
    mask = (1 << L) - 1
    rows = [[x & mask for x in r] for r in rows]
    rows = [r for r in rows if any(r)]
    total = 0
    ncol = len(rows[0]) if rows else 0
    for col in range(ncol):
        best, bv = None, L
        for i, r in enumerate(rows):
            x = r[col]
            if x:
                v = (x & -x).bit_length() - 1
                if v < bv:
                    best, bv = i, v
        if best is None:
            continue
        p = rows.pop(best)
        total += L - bv
        u = pow(p[col] >> bv, -1, 1 << L)
        p = [(x * u) & mask for x in p]            # pivot entry is now 2^bv
        new = []
        for r in rows:
            x = r[col]
            if x:
                f = x >> bv
                r = [(a - f * b) & mask for a, b in zip(r, p)]
            new.append(r)
        # the pivot row times 2^(L - bv) is still in the module: keep it for later columns
        q = [(x << (L - bv)) & mask for x in p]
        if any(q):
            new.append(q)
        rows = [r for r in new if any(r)]
    return total


def C_count(g, r):
    return sum(1 for i in range(g) if wt(i) >= r - 1)


def formal_index_log2(N, r, g):
    a = g.bit_length() - 1                           # 2^a <= g < 2^(a+1)
    tot = 0
    from math import comb
    for t in range(1, N + 1):
        tot += comb(N, t) * (max(0, a + 2 - t) - max(0, r - t))
    return tot


def check_C(rng):
    print("== C. Theorem 3: Walsh level r, valuations, first block, order of the image ==")
    # valuations and the first block formula
    for m, N, kind in ((8, 5, "power"), (11, 6, "random"), (13, 6, "power")):
        F = GF(m)
        R = GR(F, 9)
        basis = lib.power_basis(F, N) if kind == "power" else lib.random_basis(F, N, rng)
        pts = lib.span(F, basis)
        nval = nblk = 0
        for r in range(1, N):
            gens = lattice_generators(N, r)
            for _ in range(25):
                c = [0] * (1 << N)
                gam = {}
                for A, gvec in gens:
                    z = rng.randrange(-2, 3)
                    if z:
                        gam[A] = z
                        for x in range(1 << N):
                            c[x] += z * gvec[x]
                cd = {pts[x]: c[x] for x in range(1 << N) if c[x] and pts[x]}
                for k in range(1, 64, 2):
                    assert R.val(R.psum(cd, k)) >= min(R.L, r - wt(k)), (m, N, r, k)
                    nval += 1
                # first block: for j = 2^r - 2^(r-w), 1 <= w <= r, the coefficient of X^j is
                # sum over |A| in [w, r] of gbar_A M_A(j), M_A(j) = sum over t with sum 2^t_i = j of prod b_i^(2^t_i)
                lam = F.lam(cd, (1 << r) - 1)
                for j in range(1, 1 << r):
                    pred = 0
                    if wt(j - 1) == r - 1 and j >= 1 << (r - 1):
                        for A, z in gam.items():
                            if z & 1 and wt(A) <= r:
                                idx = [i for i in range(N) if A >> i & 1]
                                for t in compositions_pow2(j, len(idx)):
                                    p = 1
                                    for i, ti in zip(idx, t):
                                        p = F.mul(p, F.pow(basis[i], 1 << ti))
                                    pred ^= p
                    assert lam[j] == pred, (m, N, r, j)
                    nblk += 1
        print(f"   GF(2^{m}), N={N}, {kind}: v2(p~_k(c)) >= r - wt(k) in {nval} cases; coefficients of X^j, j < 2^r, "
              f"equal to the first-block formula in {nblk} cases")
    # exact order of the image of L^(r) in the units modulo X^(g+1)
    print("   log2 of the order of the image of L^(r) in (1 + X K[[X]]) / (1 + X^(g+1)):")
    print("   field, domain          r   g   image   m*C_g(r)   formal index   m*g")
    for m, N, kind in ((5, 5, "power"), (6, 5, "power"), (7, 5, "random"), (6, 6, "power"), (7, 6, "power"),
                       (8, 6, "random"), (7, 7, "power"), (9, 7, "random")):
        F = GF(m)
        basis = lib.power_basis(F, N) if kind == "power" else lib.random_basis(F, N, rng)
        pts = lib.span(F, basis)
        for r in range(2, N + 1):
            for g in sorted({(1 << (r - 1)) + 1, 3 << (r - 2), (1 << r) + 1, (5 << r) // 4, min(1 << (N - 1), 3 << (r - 1))}):
                if g < 2 or g >= (1 << N) - 1 or g > 40:
                    continue
                L = g.bit_length()
                R = GR(F, L)
                gens = lattice_generators(N, r)
                rows = []
                for A, gvec in gens:
                    cd = {pts[x]: gvec[x] for x in range(1 << N) if gvec[x] and pts[x]}
                    row = []
                    for k in range(1, g + 1, 2):
                        lk = (g // k).bit_length()         # 1 + floor(log2(g / k))
                        row += [x << (L - lk) for x in R.psum(cd, k)]
                    rows.append(row)
                img = module_order_log2(rows, L)
                cg = C_count(g, r)
                assert img <= m * cg, (m, N, r, g, img, cg)
                fi = formal_index_log2(N, r, g)
                assert img <= fi
                print(f"   GF(2^{m}), N={N} {kind:6s}  {r:2d}  {g:2d}   {img:5d}   {m * cg:8d}   {fi:12d}   {m * g:4d}"
                      + ("   = min" if img == min(m * cg, fi) else ""))


def check_D():
    print("== D. Explicit pair from 56_acc32: n = 32, GF(2^6) = F_2[x]/(x^6 + x + 1), D = span(1, x, .., x^4) ==")
    F = GF(6)
    assert F.mod == 0x43
    R = GR(F, 6)
    pts = lib.span(F, lib.power_basis(F, 5))
    S1 = [x for x in range(32) if 0x85948062 >> x & 1]
    S2 = [x for x in range(32) if 0x4a684091 >> x & 1]
    za, zb = F.locator([pts[x] for x in S1]), F.locator([pts[x] for x in S2])
    deg = max([j for j in range(11) if za[j] != zb[j]], default=-1)
    c = {}
    for x in S1:
        c[pts[x]] = c.get(pts[x], 0) + 1
    for x in S2:
        c[pts[x]] = c.get(pts[x], 0) - 1
    c = {s: e for s, e in c.items() if e}
    o = lib.witt_order(R, c, 16)
    lvl = 0
    while all((sum(bin(phi & x).count("1") & 1 for x in S1) - sum(bin(phi & x).count("1") & 1 for x in S2))
              % (1 << lvl) == 0 for phi in range(1, 32)):
        lvl += 1
    print(f"   S  = {S1}")
    print(f"   S' = {S2}   (points as bit masks of the coordinates)")
    print(f"   |S| = |S'| = {len(S1)}, |S meet S'| = {len(set(S1) & set(S2))}, deg(Z_S - Z_S') = {deg}, "
          f"Witt order = {o}, hyperplane counts congruent modulo {1 << (lvl - 1)} and not modulo {1 << lvl}")
    print("   Witt data: " + ", ".join(f"v2(p~_{k}) = {R.val(R.psum(c, k))}" for k in (1, 3, 5, 7, 9)))
    assert deg == 0 and o == 10 and lvl == 3


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = random.Random(56)
    if which in ("D", "all"):
        check_D()
    if which in ("A", "all"):
        check_A(rng)
    if which in ("B", "all"):
        check_B(rng)
    if which in ("C", "all"):
        check_C(rng)
