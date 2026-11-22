"""Researcher 37: numerical check of the transfer lemma (note 37, Lemma 4.1) and of the gap theorem (Theorem 4.3).

For a random N-dimensional subspace D of GF(2^64) (leanVM modulus; a random specialization of the formal model) the
script builds rational functions xi = xi_0 o L_Pi, xi_0 a function of generic type on D/Pi with a prescribed fibre
pattern (r_0, r_1, r_2), r_0 + r_1 + r_2 = 2 delta_0 + 1 (unique solution of a linear system), computes the true
fibres R_i of xi over 0, infinity, 1 in D and checks, for every direction z != 0:

  there is l(z) in {none, 0, 1, 2} such that for every l != l(z):  |R_i n (R_j + z)| <= s_l = delta - r_l
  and, if l(z) = l,                                                |R_i n (R_j + z)| >= r_i - s_j        ({i,j,l} = {0,1,2}).

It also prints the smallest value of s n / delta^2 over the non-flat examples (Theorem 4.3 says it is >= 1/4) and
checks the rigidity statement (a is a period iff sum_i |R_i n (R_i + a)| >= 2 delta) on every example.

Run: python3 37_transfer_check.py [seed]      (about one minute)
"""
import random
import sys

MOD_LOW = 0x1B
MASK = (1 << 64) - 1


def mul(a, b):
    r = 0
    while b:
        low = b & -b
        r ^= a << (low.bit_length() - 1)
        b ^= low
    # reduce modulo x^64 + x^4 + x^3 + x + 1
    for _ in range(2):
        hi = r >> 64
        if not hi:
            break
        r = (r & MASK) ^ hi ^ (hi << 1) ^ (hi << 3) ^ (hi << 4)
    return r


def inv(a):
    r, e = 1, (1 << 64) - 2
    while e:
        if e & 1:
            r = mul(r, a)
        a = mul(a, a)
        e >>= 1
    return r


def span(basis):
    pts = [0]
    for b in basis:
        pts += [p ^ b for p in pts]
    return pts


def poly_mul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] ^= mul(a, b)
    return r


def poly_eval(p, x):
    v = 0
    for c in reversed(p):
        v = mul(v, x) ^ c
    return v


def locator(S):
    p = [1]
    for s in S:
        p = poly_mul(p, [s, 1])
    return p


def kernel_vector(M, ncols):
    """One nonzero kernel vector of the matrix M (list of rows) over GF(2^64), or None; also returns the nullity."""
    M = [row[:] for row in M]
    piv = []
    r = 0
    for c in range(ncols):
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        iv = inv(M[r][c])
        M[r] = [mul(iv, v) for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [v ^ mul(f, w) for v, w in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    free = [c for c in range(ncols) if c not in piv]
    if not free:
        return None, 0
    v = [0] * ncols
    v[free[0]] = 1
    for i, c in enumerate(piv):
        v[c] = M[i][free[0]]
    return v, len(free)


def generic_type(D0, pattern, rng):
    """xi_0 = u_0/u_1 of degree <= delta_0 on D0 with r_i prescribed points in the fibres; returns (u_0, u_1) or None."""
    r0, r1, r2 = pattern
    d0 = (r0 + r1 + r2 - 1) // 2
    pts = rng.sample(D0, r0 + r1 + r2)
    R = [pts[:r0], pts[r0:r0 + r1], pts[r0 + r1:]]
    Z = [locator(S) for S in R]
    cols = []
    for i in range(3):
        for j in range(d0 - len(R[i]) + 1):
            col = [0] * j + Z[i]
            cols.append(col + [0] * (d0 + 1 - len(col)))
    ncols = len(cols)
    M = [[cols[c][row] for c in range(ncols)] for row in range(d0 + 1)]
    v, nullity = kernel_vector(M, ncols)
    if v is None or nullity != 1:
        return None
    hs, pos = [], 0
    for i in range(3):
        m = d0 - len(R[i]) + 1
        hs.append(v[pos:pos + m])
        pos += m
    u0 = poly_mul(Z[0], hs[0])
    u1 = poly_mul(Z[1], hs[1])
    return u0, u1, d0


def degree(p):
    d = len(p) - 1
    while d >= 0 and p[d] == 0:
        d -= 1
    return d


def run(N, dimPi, pattern, rng, stats):
    basis = [rng.getrandbits(64) for _ in range(N)]
    D = span(basis)
    if len(set(D)) != len(D):
        return
    Pi = D[: 1 << dimPi]  # span of the first dimPi basis vectors
    LPi = locator(Pi)
    img = {x: poly_eval(LPi, x) for x in D}
    D0 = sorted(set(img.values()))
    res = generic_type(D0, pattern, rng)
    if res is None:
        stats["skipped"] += 1
        return
    u0, u1, _ = res
    u2 = [a ^ b for a, b in zip(u0 + [0] * (len(u1) - len(u0)), u1 + [0] * (len(u0) - len(u1)))]
    us = [u0, u1, u2]
    d0 = max(degree(u) for u in us)
    # the triple must be coprime: check that no point of D0 is a common root, and that degrees are as expected
    R0 = [set(y for y in D0 if poly_eval(u, y) == 0) for u in us]
    if R0[0] & R0[1]:
        stats["skipped"] += 1
        return
    delta = d0 << dimPi
    R = [set(x for x in D if img[x] in R0[i]) for i in range(3)]
    r = [len(S) for S in R]
    s = [delta - ri for ri in r]
    n = len(D)
    nu = sum(r)
    stats["examples"] += 1
    flat = all(si == 0 for si in s)
    if not flat:
        stats["min_ratio"] = min(stats["min_ratio"], sum(s) * n / delta ** 2)
    # periods of xi: a with xi(X + a) = xi(X), tested at 3 random field points
    def is_period(a):
        for _ in range(3):
            t = rng.getrandbits(64)
            x0, x1 = img.get(t) or poly_eval(LPi, t), poly_eval(LPi, t ^ a)
            if mul(poly_eval(u0, x0), poly_eval(u1, x1)) != mul(poly_eval(u1, x0), poly_eval(u0, x1)):
                return False
        return True
    for z in D:
        if z == 0:
            continue
        T = {}
        for i in range(3):
            for j in range(3):
                T[i, j] = sum(1 for x in R[j] if (x ^ z) in R[i])
        ok_types = []
        for lz in (None, 0, 1, 2):
            ok = True
            for l in range(3):
                i, j = [t for t in range(3) if t != l]
                if l != lz:
                    ok &= T[i, j] <= s[l]
                else:
                    ok &= T[i, j] >= r[i] - s[j]
            if ok:
                ok_types.append(lz)
        if not ok_types:
            stats["transfer_violations"] += 1
            print("VIOLATION transfer", N, dimPi, pattern, r, s, T)
        if ok_types and ok_types != [None] and None not in ok_types:
            stats["typed_directions"] += 1
        # control: the same test on random disjoint sets of the same sizes
        if z == D[1]:
            pts = rng.sample(D, nu)
            C = [set(pts[: r[0]]), set(pts[r[0] : r[0] + r[1]]), set(pts[r[0] + r[1] :])]
            bad = False
            for zz in D[1:]:
                TT = {(i, j): sum(1 for x in C[j] if (x ^ zz) in C[i]) for i in range(3) for j in range(3)}
                good = False
                for lz in (None, 0, 1, 2):
                    ok = True
                    for l in range(3):
                        i, j = [t for t in range(3) if t != l]
                        ok &= (TT[i, j] <= s[l]) if l != lz else (TT[i, j] >= r[i] - s[j])
                    good |= ok
                bad |= not good
            stats["control_total"] += 1
            stats["control_violating"] += bad
        same = T[0, 0] + T[1, 1] + T[2, 2]
        per = is_period(z)
        if (same >= 2 * delta) != per:
            if same >= 2 * delta and not per:
                stats["rigidity_violations"] += 1
                print("VIOLATION rigidity", N, dimPi, pattern, r, same, delta)
        if per and same != nu:
            stats["rigidity_violations"] += 1
    stats["types"].add((delta, nu, sum(1 for z in D if is_period(z))))


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    stats = {"examples": 0, "skipped": 0, "transfer_violations": 0, "rigidity_violations": 0, "min_ratio": 1e9, "types": set(), "typed_directions": 0, "control_total": 0, "control_violating": 0}
    jobs = []
    for N0 in (3, 4):
        n0 = 1 << N0
        for d0 in range(1, n0 // 2):
            pats = set()
            for r0 in range(0, d0 + 1):
                for r1 in range(r0, d0 + 1):
                    r2 = 2 * d0 + 1 - r0 - r1
                    if r1 <= r2 <= d0:
                        pats.add((r0, r1, r2))
            for pat in sorted(pats):
                for dimPi in (0, 1, 2):
                    if N0 + dimPi <= 6:
                        jobs.append((N0 + dimPi, dimPi, pat))
    for N, dimPi, pat in jobs:
        for _ in range(3 if N <= 5 else 1):
            run(N, dimPi, pat, rng, stats)
    print("examples:", stats["examples"], "skipped:", stats["skipped"])
    print("transfer-lemma violations:", stats["transfer_violations"])
    print("directions whose type is forced to be a transfer type:", stats["typed_directions"])
    print("control (random disjoint sets of the same sizes): %d of %d violate the lemma" % (stats["control_violating"], stats["control_total"]))
    print("rigidity violations:", stats["rigidity_violations"])
    print("min s*n/delta^2 over non-flat examples: %.4f (Theorem 4.3: >= 0.25)" % stats["min_ratio"])
    print("types (delta, nu, |Pi|):", sorted(stats["types"]))


if __name__ == "__main__":
    main()
