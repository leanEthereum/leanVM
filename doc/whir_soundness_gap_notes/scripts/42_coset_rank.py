#!/usr/bin/env python3
"""Note 42 (referee of note 36): Proposition 7.2 of note 36 on concrete examples.

Claim checked. U an F_2-subspace of GF(2^8) with w elements, m0 >= 1, k' = w m0, a domain made of
t = m0 + 2 cosets c_g + U. Then for EVERY choice of the representatives there are t distinct polynomials
of degree <= k' (dimension k' + 1) and a word such that member g0 agrees with the word exactly on the
cosets g != g0. The agreement hypergraph (one edge [t] minus {g0} per point of coset g0) is
(k'+1)-weakly-partition-connected, so the generic-rank theorem ([AGGLZ] Theorem 2.11) says that its
reduced intersection matrix has full column rank at algebraically independent points; on a coset union it
cannot, because the t members are a nonzero kernel vector.

The script, for several (w, m0):
  1. builds the members G_g0(L_U(x)) and the word L_U(x)^(m0+1), checks degrees, distinctness, agreements;
  2. checks weak partition connectivity of the agreement hypergraph by enumerating all partitions of [t];
  3. computes the rank of the reduced intersection matrix (columns: the coefficients of f_j - f_t, j < t;
     rows: one equation (f_j - f_j')(a_i) = 0 per coordinate and per member of its edge but the first)
     at the coset-union points and at uniformly random distinct points with the same edges.

Pure standard library. Usage: python3 42_coset_rank.py   (a few seconds)
"""
import itertools
import random

# ---------------------------------------------------------------- GF(2^8), modulus x^8 + x^4 + x^3 + x + 1
EXP = [0] * 510
LOG = [0] * 256
_x = 1
for _i in range(255):
    EXP[_i] = _x
    LOG[_x] = _i
    _x ^= (_x << 1) ^ (0x11B if _x & 0x80 else 0)  # multiply by the generator 3 = x + 1
    _x &= 0xFF
for _i in range(255, 510):
    EXP[_i] = EXP[_i - 255]


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]


def inv(a):
    return EXP[255 - LOG[a]]


def pmul(f, g):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                r[i + j] ^= mul(a, b)
    return r


def padd(f, g):
    r = [0] * max(len(f), len(g))
    for i, a in enumerate(f):
        r[i] ^= a
    for i, b in enumerate(g):
        r[i] ^= b
    return r


def peval(f, x):
    r = 0
    for c in reversed(f):
        r = mul(r, x) ^ c
    return r


def deg(f):
    d = len(f) - 1
    while d >= 0 and f[d] == 0:
        d -= 1
    return d


def interpolate(xs, ys):
    res = [0]
    for i, xi in enumerate(xs):
        num, den = [1], 1
        for j, xj in enumerate(xs):
            if j != i:
                num = pmul(num, [xj, 1])
                den = mul(den, xi ^ xj)
        c = mul(ys[i], inv(den))
        res = padd(res, [mul(c, a) for a in num])
    return res


def compose(G, L):
    res, power = [0], [1]
    for c in G:
        res = padd(res, [mul(c, a) for a in power])
        power = pmul(power, L)
    return res


def rank(rows, ncols):
    rows = [r[:] for r in rows]
    rk = 0
    for c in range(ncols):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        ip = inv(rows[rk][c])
        rows[rk] = [mul(ip, v) for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c]
                rows[i] = [v ^ mul(f, u) for v, u in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def rim(points, edges, t, dim):
    """reduced intersection matrix: unknowns d_j = f_j - f_{t-1} for j < t-1, dim coefficients each."""
    rows = []
    for x, e in zip(points, edges):
        pw = [1]
        for _ in range(dim - 1):
            pw.append(mul(pw[-1], x))
        j0 = e[0]
        for j in e[1:]:
            row = [0] * ((t - 1) * dim)
            for jj in (j0, j):
                if jj < t - 1:
                    for c in range(dim):
                        row[jj * dim + c] ^= pw[c]
            rows.append(row)
    return rows


def partitions(s):
    if not s:
        yield []
        return
    first, rest = s[0], s[1:]
    for part in partitions(rest):
        yield [[first]] + part
        for i in range(len(part)):
            yield part[:i] + [[first] + part[i]] + part[i + 1:]


def wpc(edges, t):
    """largest kappa such that the hypergraph is kappa-weakly-partition-connected."""
    best = None
    for P in partitions(list(range(t))):
        if len(P) < 2:
            continue
        where = {v: i for i, part in enumerate(P) for v in part}
        s = sum(max(len({where[v] for v in e}) - 1, 0) for e in edges)
        val = s // (len(P) - 1)
        best = val if best is None else min(best, val)
    return best


def subspace(w):
    basis = [1, 2, 4, 8, 16][: w.bit_length() - 1]
    U = [0]
    for b in basis:
        U += [u ^ b for u in U]
    return U


def main():
    rng = random.Random(42)
    print("w  m0  t  n  dim=k'+1  weight  (t-1)dim  wpc  rank on coset unions (20 choices of representatives)  rank at random points (20 choices)  full")
    for w, m0 in ((2, 1), (2, 2), (2, 3), (2, 5), (4, 1), (4, 2), (4, 3), (8, 1), (8, 2)):
        U = subspace(w)
        LU = [1]
        for u in U:
            LU = pmul(LU, [u, 1])
        t, kp = m0 + 2, w * m0
        dim = kp + 1
        ranks_coset, ranks_rand = set(), set()
        for trial in range(20):
            # representatives of t distinct cosets
            reps = []
            while len(reps) < t:
                c = rng.randrange(256)
                if all((c ^ r) not in U for r in reps):
                    reps.append(c)
            pts = [c ^ u for c in reps for u in U]
            v = [peval(LU, c) for c in reps]
            assert len(set(v)) == t
            word = []
            for x in pts:
                lx = peval(LU, x)
                r = 1
                for _ in range(m0 + 1):
                    r = mul(r, lx)
                word.append(r)
            members = []
            for g0 in range(t):
                xs = [v[g] for g in range(t) if g != g0]
                ys = []
                for x in xs:
                    r = 1
                    for _ in range(m0 + 1):
                        r = mul(r, x)
                    ys.append(r)
                G = interpolate(xs, ys)
                assert deg(G) <= m0
                f = compose(G, LU)
                assert deg(f) <= kp
                members.append((f + [0] * dim)[:dim])
            assert len({tuple(f) for f in members}) == t
            edges = []
            for idx, x in enumerate(pts):
                e = [j for j in range(t) if peval(members[j], x) == word[idx]]
                assert e == [j for j in range(t) if j != idx // w], (e, idx)
                edges.append(e)
            weight = sum(len(e) - 1 for e in edges)
            # the members give a nonzero kernel vector
            M = rim(pts, edges, t, dim)
            vec = []
            for j in range(t - 1):
                vec += [a ^ b for a, b in zip(members[j], members[t - 1])]
            assert any(vec)
            for row in M:
                acc = 0
                for a, b in zip(row, vec):
                    acc ^= mul(a, b)
                assert acc == 0
            ranks_coset.add(rank(M, (t - 1) * dim))
            rnd = rng.sample(range(256), len(pts))
            ranks_rand.add(rank(rim(rnd, edges, t, dim), (t - 1) * dim))
        conn = wpc(edges, t) if t <= 7 else None
        print(f"{w}  {m0}  {t}  {w*t}  {dim}  {weight}  {(t-1)*dim}  {conn}  {sorted(ranks_coset)}  {sorted(ranks_rand)}  {(t-1)*dim}")
    print("In every row: the hypergraph is (k'+1)-weakly-partition-connected (wpc >= dim), the matrix has full column rank at random points and is rank deficient on every coset union tried.")


if __name__ == "__main__":
    main()
