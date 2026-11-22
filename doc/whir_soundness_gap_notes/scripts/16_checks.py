#!/usr/bin/env python3
"""Researcher 16: three small checks for note 16, on GF(2^6). Standard library, a few seconds.

  lines     Proposition 3.1 with a running claim: k near pairs that share s-1 answers win k lines of fold challenges
            with one prover message, (i) with the zero weight, (ii) with a weight for which every pair violates the
            running claim, the message being solved for. Counted by brute force over all q^2 challenges.
  barrier   Proposition 4.1: an abstract list system (three candidates per challenge on a twisted plane) for which
            every pair of points has an answer vector winning at least 3q challenges with no three in one class,
            and the exact frequency of exceptional triples of points.
  roots     the graph of X^(2^j) over GF(2^6): every line through two of its points meets it in exactly 2^j points.

Usage: python3 16_checks.py [lines|barrier|roots|all] [seed]
"""
import random
import sys

M = 6
Q = 1 << M
IRR = 0x43  # x^6 + x + 1


def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & Q:
            a ^= IRR
    return r


MUL = [[gmul(a, b) for b in range(Q)] for a in range(Q)]
INV = [0] * Q
for _a in range(1, Q):
    for _b in range(1, Q):
        if MUL[_a][_b] == 1:
            INV[_a] = _b


def gpow(a, e):
    r = 1
    for _ in range(e):
        r = MUL[r][a]
    return r


def peval(co, x):
    r = 0
    for c in reversed(co):
        r = MUL[r][x] ^ c
    return r


def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) ^ (b[i] if i < len(b) else 0) for i in range(n)]


def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i + j] ^= MUL[x][y]
    return r


def pscale(a, s):
    return [MUL[x][s] for x in a]


def dot(w, p):
    r = 0
    for i, x in enumerate(p):
        if x:
            r ^= MUL[w[i]][x]
    return r


def solve(rows, rhs, nvars, rng):
    """One solution of a linear system over GF(2^6), free variables random; None if inconsistent."""
    a = [r[:] + [b] for r, b in zip(rows, rhs)]
    piv = []
    row = 0
    for col in range(nvars):
        p = next((i for i in range(row, len(a)) if a[i][col]), None)
        if p is None:
            continue
        a[row], a[p] = a[p], a[row]
        iv = INV[a[row][col]]
        a[row] = [MUL[x][iv] for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                f = a[i][col]
                a[i] = [x ^ MUL[f][y] for x, y in zip(a[i], a[row])]
        piv.append(col)
        row += 1
    if any(r[nvars] for r in a[row:]):
        return None
    x = [rng.randrange(Q) for _ in range(nvars)]
    for i, col in enumerate(piv):
        v = a[i][nvars]
        for c in range(nvars):
            if c != col and a[i][c]:
                v ^= MUL[a[i][c]][x[c]]
        x[col] = v
    return x


def check_lines(rng, k=3, d=3, s=2):
    """k pairs (F, G + R H_j), R = X - rho. Points: zeta_1..zeta_{s-1} = rho (with different theta), zeta_s random.
    Returns the number of winning challenges with the zero weight and with a weight that every pair violates."""
    rho = rng.randrange(1, Q)
    F = [rng.randrange(Q) for _ in range(d)]  # degree d-1
    G = [rng.randrange(Q) for _ in range(d + 1)]
    R = [rho, 1]
    Gs = []
    for _ in range(k):
        H = [rng.randrange(Q) for _ in range(d)]
        Gs.append(padd(G, pmul(R, H)))
    XF = [0] + F
    zeta = [rho] * (s - 1)
    while True:
        zl = rng.randrange(1, Q)
        if zl != rho and len({peval(g, zl) for g in Gs}) == k:
            break
    zeta.append(zl)
    theta = [rng.randrange(Q) for _ in range(s)]
    # carried values: honest at the first s-1 points, wrong for every pair at the last
    v = [peval(G, z) ^ MUL[t][peval(F, z)] for z, t in zip(zeta, theta)]
    honest_last = {peval(g, zl) ^ MUL[theta[-1]][peval(F, zl)] for g in Gs}
    v[-1] = next(x for x in range(Q) if x not in honest_last)
    eps = [v[-1] ^ peval(g, zl) ^ MUL[theta[-1]][peval(F, zl)] for g in Gs]  # carried-claim errors, nonzero
    phi_off = rng.randrange(1, Q)
    phi = [peval(F, z) for z in zeta]
    phi[-1] ^= phi_off
    gam = [MUL[e][INV[phi_off]] for e in eps]  # line j: theta_s + alpha + beta zeta_s = gam_j

    def winners(W0, W1, sigma, msg):
        vG, vF, s0, s1 = msg
        won = set()
        for al in range(Q):
            for be in range(Q):
                for g in Gs:
                    P = padd(g, padd(pscale(F, al), pscale(XF, be)))
                    ok = True
                    for z, t, vm, ph in zip(zeta, theta, v, phi):
                        if peval(P, z) != vm ^ MUL[t ^ al ^ MUL[be][z]][ph]:
                            ok = False
                            break
                    if not ok:
                        continue
                    lhs = MUL[1 ^ al][dot(W0, P)] ^ MUL[al][dot(W1, P)]
                    rhs = vG ^ MUL[al][vG ^ sigma] ^ MUL[MUL[al][al]][vF] ^ MUL[be][s0] ^ MUL[MUL[al][be]][s0 ^ s1]
                    if lhs == rhs:
                        won.add((al, be))
                        break
        return len(won)

    zero = [0] * (d + 1)
    n_zero = winners(zero, zero, 0, (0, 0, 0, 0))
    # (ii) every pair violates the running claim: delta_F = 0, delta_0 = delta_1 = dl,
    # delta_G^j = c_j dl / zeta, e_j = (1 + c_j) dl / zeta with c_j = theta_s + gam_j (the value of alpha + beta zeta_s on line j)
    dl = rng.randrange(1, Q)
    cj = [theta[-1] ^ g for g in gam]
    if any(c == 1 for c in cj):
        return n_zero, None, None
    vG, sigma = rng.randrange(Q), rng.randrange(Q)
    izl = INV[zl]
    W0 = solve([g[:] for g in Gs], [vG ^ MUL[MUL[c][dl]][izl] for c in cj], d + 1, rng)
    if W0 is None:
        return n_zero, None, None
    w0F = dot(W0, F)
    W1 = solve([g[:] for g in Gs], [sigma ^ w0F ^ MUL[MUL[1 ^ c][dl]][izl] for c in cj], d + 1, rng)
    if W1 is None:
        return n_zero, None, None
    vF = dot(W0, F) ^ dot(W1, F)
    msg = (vG, vF, dot(W0, XF) ^ dl, dot(W1, XF) ^ dl)
    errs = [sigma ^ dot(W0, F) ^ dot(W1, g) for g in Gs]  # sigma - <W, U_j>, all nonzero
    return n_zero, winners(W0, W1, sigma, msg), all(e != 0 for e in errs)


def check_roots(j):
    """Every line through two points of the graph of X^(2^j) meets it in exactly 2^j points (j divides 6)."""
    e = 1 << j
    g = [gpow(x, e) for x in range(Q)]
    sizes = set()
    for z1 in range(Q):
        for z2 in range(z1 + 1, Q):
            u1 = MUL[g[z1] ^ g[z2]][INV[z1 ^ z2]]
            u2 = g[z1] ^ MUL[u1][z1]
            sizes.add(sum(1 for z in range(Q) if g[z] == MUL[u1][z] ^ u2))
    return sizes


def check_barrier(rng, j=2, lam=3, trials=40):
    """Abstract list system: P_c = G + alpha F1 + beta F2 + x for x in X_c, |X_c| = lam, F2 + X F1 = X^(2^j), d = 2^j - 1.
    For points zeta_1, zeta_2 the answers yF_i = F1(zeta_i) + u1, yG_i = G(zeta_i) + v0 with
    u1 = (zeta_1^(2^j) + zeta_2^(2^j)) / (zeta_1 + zeta_2), u2 = zeta_i^(2^j) + u1 zeta_i are consistent with every (c, x)
    with x = v0 + u1 alpha + u2 beta. Returns the least, over the sampled point pairs, of the best block size (max over v0),
    checked by direct evaluation, and the largest number of block elements on one line of challenges."""
    e = 1 << j
    d = e - 1
    F1 = [rng.randrange(Q) for _ in range(d)] + [1]  # degree d, leading coefficient 1
    F2 = padd([0] + F1, [0] * e + [1])  # X F1 + X^(d+1): degree at most d
    assert len(F2) == d + 2 and F2[d + 1] == 0
    F2 = F2[: d + 1]
    G = [rng.randrange(Q) for _ in range(d + 1)]
    X = {(al, be): rng.sample(range(Q), lam) for al in range(Q) for be in range(Q)}
    worst, worst_line = None, 0
    for _ in range(trials):
        z1, z2 = rng.sample(range(Q), 2)
        u1 = MUL[gpow(z1, e) ^ gpow(z2, e)][INV[z1 ^ z2]]
        u2 = gpow(z1, e) ^ MUL[u1][z1]
        assert u2 == gpow(z2, e) ^ MUL[u1][z2]
        best, bestv = 0, 0
        for v0 in range(Q):
            n = sum(1 for (al, be), xs in X.items() if (v0 ^ MUL[u1][al] ^ MUL[u2][be]) in xs)
            if n > best:
                best, bestv = n, v0
        # direct check of consistency for the best block
        block = [(al, be) for (al, be), xs in X.items() if (bestv ^ MUL[u1][al] ^ MUL[u2][be]) in xs]
        for al, be in block:
            x = bestv ^ MUL[u1][al] ^ MUL[u2][be]
            P = padd(padd(G, pscale(F1, al)), pscale(F2, be))
            P[0] ^= x
            for z in (z1, z2):
                yF = peval(F1, z) ^ u1
                yG = peval(G, z) ^ bestv
                assert peval(P, z) == yG ^ MUL[al ^ MUL[be][z]][yF]
        # the classes of a twisted plane are its lines of challenges: largest number of block elements on a line
        lines = {}
        for al, be in block:
            for x0 in range(Q):
                key = (x0, al ^ MUL[x0][be])
                lines[key] = lines.get(key, 0) + 1
            lines[("inf", be)] = lines.get(("inf", be), 0) + 1
        worst_line = max(worst_line, max(lines.values()))
        worst = best if worst is None else min(worst, best)
    # exceptional triples of points: collinear triples of the graph of X^(2^j)
    g = [gpow(x, e) for x in range(Q)]
    col = tot = 0
    for z1 in range(Q):
        for z2 in range(Q):
            if z2 == z1:
                continue
            u1 = MUL[g[z1] ^ g[z2]][INV[z1 ^ z2]]
            u2 = g[z1] ^ MUL[u1][z1]
            for z3 in range(Q):
                tot += 1
                if g[z3] == MUL[u1][z3] ^ u2:
                    col += 1
    return d, worst, worst_line, col, tot


def main():
    what = sys.argv[1] if len(sys.argv) > 1 else "all"
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 16)
    if what in ("lines", "all"):
        print(f"== lines: k near pairs sharing s-1 answers, q = {Q}; expected k q winning challenges")
        for k, d, s in ((3, 3, 2), (4, 4, 2), (3, 3, 3), (5, 5, 2)):
            for _ in range(2):
                n0, n1, viol = check_lines(rng, k, d, s)
                while n1 is None:  # a line with alpha + beta zeta = 1, or a degenerate system: draw again
                    n0, n1, viol = check_lines(rng, k, d, s)
                print(f"k={k} d={d} s={s}: zero weight {n0} challenges; weight violated by every pair: {n1} challenges (all violate: {viol}); k q = {k * Q}, 2.72 q = {2.72 * Q:.0f}")
    if what in ("roots", "all"):
        print("== roots: sizes of the intersections of the graph of X^(2^j) with the lines through two of its points")
        for j in (1, 2, 3):
            print(f"j={j}: {sorted(check_roots(j))} (expected [{1 << j}])")
    if what in ("barrier", "all"):
        print(f"== barrier: abstract list system with 3 candidates per challenge, q = {Q}")
        for j in (2, 3):
            d, worst, worst_line, col, tot = check_barrier(rng, j)
            print(
                f"d={d}: least best block over 40 point pairs = {worst} (3q = {3 * Q}, K0 = {int(2.72 * Q) + 1}); most block elements on one line of challenges = {worst_line};"
                f" exceptional triples of points: {col} of {tot} = {col / tot:.5f} (predicted {((1 << j) / Q):.5f})"
            )


if __name__ == "__main__":
    main()
