#!/usr/bin/env python3
"""51_planted.py: small-case search for a (degenerate) quintic potential carrying two list members, for
51-degenerate-quintics.md.

n = 32, Delta = n/2 - 1 = 15 (as in notes 40, 45), GF(2^8), subspace domain of 40_lib (seed 3), A = 23 = ceil(0.7065 n).
For each word: the smallest W_1 such that a quintic potential E (mod squares) exists whose total derivative has
contact >= 4 on all lines and weighted degree <= W_1 (linear algebra of 45_lattice.py), the nullity there, whether
a random element of the solution space is degenerate (det of the 3 x 3 matrix of the conics A, B, C of note 45),
and whether the planted codewords are sections (E(X, P) in F[X^2]; automatic when W_1 < 4 A = 92).
Scaled window of note 48 at n = 32: W in [Delta + 3A, 2.6352 n) = [84, 84.3], that is W = 84.

Run: python3 51_planted.py [seed]
"""
import sys
import random
from importlib import import_module

lib = import_module("40_lib")
lat = import_module("45_lattice")
mul, inv, fpow, fsqrt = lib.mul, lib.inv, lib.fpow, lib.fsqrt


def padd(p, q):
    r = [0] * max(len(p), len(q))
    for i, c in enumerate(p):
        r[i] ^= c
    for i, c in enumerate(q):
        r[i] ^= c
    return r


def pmul(p, q):
    r = [0] * (len(p) + len(q) - 1) if p and q else []
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] ^= mul(a, b)
    return r


def locator(S):
    p = [1]
    for s in S:
        p = pmul(p, [s, 1])
    return p


def first_W(pts, Dc, lo, hi):
    for W in range(lo, hi + 1):
        monos = lat.support(W, Dc)
        rows = lat.rows_for(monos, pts)
        basis = lib.nullspace(rows, len(monos))
        if basis:
            return W, monos, basis
    return None, None, None


def conic_matrix(monos, vec):
    A, B, C = lat.split_sqrt(monos, vec)
    def col(P, k):
        d = max([i for (i, kk) in P if kk == k], default=-1)
        return [P.get((i, k), 0) for i in range(d + 1)]
    return [[col(P, k) for k in range(3)] for P in (A, B, C)]


def det3(M):
    def m2(a, b, c, d):
        return padd(pmul(a, d), pmul(b, c))
    t = [0]
    for j in range(3):
        o = [c for c in range(3) if c != j]
        t = padd(t, pmul(M[0][j], m2(M[1][o[0]], M[1][o[1]], M[2][o[0]], M[2][o[1]])))
    return t


def is_section(monos, vec, P):
    """E(X, P(X)) has no odd-degree term."""
    acc = {}
    pw = {0: [1]}
    for (i, k), e in zip(monos, vec):
        if not e:
            continue
        if k not in pw:
            q = [1]
            for _ in range(k):
                q = pmul(q, P)
            pw[k] = q
        for d, c in enumerate(pw[k]):
            if c:
                acc[i + d] = acc.get(i + d, 0) ^ mul(e, c)
    return all(v == 0 for d, v in acc.items() if d & 1)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    rng = random.Random(seed)
    N, n = 5, 32
    Dc, A = 15, 23
    D = lib.subspace_domain(N, seed=3)
    words = []
    words.append(("random", [rng.randrange(256) for _ in D], []))
    # one planted codeword with 23 agreements
    P1 = [rng.randrange(256) for _ in range(Dc + 1)]
    S = rng.sample(D, A)
    words.append(("one codeword, 23 agreements", [lib.peval(P1, al) if al in S else rng.randrange(256) for al in D], [P1]))
    # two codewords, |I| = 15, T1, T2 of size 8, one free point
    perm = rng.sample(D, n)
    I, T1, T2 = perm[:15], perm[15:23], perm[23:31]
    P2 = padd(P1, pmul([rng.randrange(1, 256)], locator(I)))
    y = [lib.peval(P1, al) if (al in I or al in T1) else lib.peval(P2, al) if al in T2 else rng.randrange(256) for al in D]
    words.append(("two codewords, |I| = 15, random sets", y, [P1, P2]))
    # two codewords, |I| = 14, T1, T2 of size 9 (the whole domain)
    I, T1, T2 = perm[:14], perm[14:23], perm[23:32]
    P2 = padd(P1, pmul([rng.randrange(1, 256), 1], locator(I)))
    y = [lib.peval(P1, al) if (al in I or al in T1) else lib.peval(P2, al) for al in D]
    words.append(("two codewords, |I| = 14, random sets", y, [P1, P2]))
    # two codewords whose agreement sets differ by an affine hyperplane: S1 xor S2 = a hyperplane H (16 points),
    # I = 15 points of the other coset
    H = D[:16]
    rest = D[16:]
    Hs = rng.sample(H, 16)
    T1, T2 = Hs[:8], Hs[8:]
    I = rng.sample(rest, 15)
    P2 = padd(P1, pmul([rng.randrange(1, 256)], locator(I)))
    y = [lib.peval(P1, al) if (al in I or al in T1) else lib.peval(P2, al) if al in T2 else rng.randrange(256) for al in D]
    words.append(("two codewords, S1 xor S2 = a hyperplane", y, [P1, P2]))
    # same with T1, T2 the two cosets of a codimension-2 subspace inside H
    T1, T2 = D[:8], D[8:16]
    y = [lib.peval(P1, al) if (al in I or al in T1) else lib.peval(P2, al) if al in T2 else rng.randrange(256) for al in D]
    words.append(("two codewords, T1, T2 cosets of a subspace", y, [P1, P2]))
    print("n = 32, Delta = 15, A = 23, 4A = 92, scaled window W = 84; seed", seed)
    for name, y, planted in words:
        pts = list(zip(D, y))
        W, monos, basis = first_W(pts, Dc, 70, 96)
        if W is None:
            print("  %-45s no potential with W <= 96" % name)
            continue
        vec = [0] * len(monos)
        for b in basis:
            c = rng.randrange(1, 256)
            vec = [v ^ mul(c, x) for v, x in zip(vec, b)]
        d = det3(conic_matrix(monos, vec))
        deg = any(d)
        secs = [is_section(monos, vec, P) for P in planted]
        agr = [sum(1 for al, yy in pts if lib.peval(P, al) == yy) for P in planted]
        print("  %-45s W_1 = %d (%.3f n), nullity %d, degenerate: %s, planted agreements %s, sections: %s"
              % (name, W, W / n, len(basis), not deg, agr, secs))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
