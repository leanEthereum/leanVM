# 59_keylemma.py: explicit subspaces V of K[X]_{<k} with Delta(V) >= L (k - L), so that
# E_V[q^Delta(V)] >= q^(Delta(V) - L (k - L)) >= 1 already from one V: the Key Lemma of note 57 fails for them.
# Exact arithmetic; Delta_x(V) = dim V - rank(V restricted to the Hamming-ball window of x).
import random
import sys

sys.path.insert(0, __file__.rsplit("/", 1)[0])
lib = __import__("59_lib")


def report(name, N, k, vals, F, degs):
    L = len(vals)
    d = lib.deficiency(F, vals, N)
    n = 1 << N
    assert max(degs) < k, (max(degs), k)
    print(f"{name}: N={N} n={n} k={k} L={L} max degree={max(degs)} Delta={sum(d)} "
          f"(min,max Delta_x)=({min(d)},{max(d)}) L(k-L)={L * (k - L)} "
          f"exponent Delta-L(k-L)={sum(d) - L * (k - L)}")


def grid_space(N, m, parts, k, mults=None):
    """V = polynomials of multidegree < A_i in M_i = L_{U'_i}, U'_i = span(b_l : l not in I_i)."""
    F = lib.GF(m)
    n = 1 << N
    pts = list(range(n))
    Ms, degM = [], []
    for I in parts:
        U = lib.span([1 << l for l in range(N) if l not in I])
        Ms.append(lib.subspace_poly_values(F, U, pts))
        degM.append(len(U))
    A = mults or [2] * len(parts)
    exps = [[]]
    for a in A:
        exps = [e + [i] for e in exps for i in range(a)]
    vals, degs = [], []
    for e in exps:
        row = [1] * n
        for Mi, ei in zip(Ms, e):
            row = [F.mul(r, F.pw(x, ei)) for r, x in zip(row, Mi)]
        vals.append(row)
        degs.append(sum(ei * d for ei, d in zip(e, degM)))
    return F, vals, degs


def main():
    # (i) rate 1/4, L = 4: V = span(1, M1, M2, M1 M2)
    N, m = 7, 8
    F, vals, degs = grid_space(N, m, [{0, 1, 2}, {3, 4, 5, 6}], 32)
    report("grid 2x2, rate 1/4", N, 32, vals, F, degs)
    # (ii) rate 1/2, L = 8: multilinear polynomials in M1, M2, M3
    N, m = 9, 10
    F, vals, degs = grid_space(N, m, [{0, 1}, {2, 3, 4}, {5, 6, 7, 8}], 256)
    report("grid 2x2x2, rate 1/2", N, 256, vals, F, degs)
    # (ii') rate 1/2, L = 8 again, with direction sets of sizes (3, 3, 3)
    F, vals, degs = grid_space(N, m, [{0, 1, 2}, {3, 4, 5}, {6, 7, 8}], 256, [2, 2, 2])
    report("grid 2x2x2 with parts (3,3,3), rate 1/2", N, 256, vals, F, degs)
    # (ii'') rate 1/8, L = 4, same as (i) with smaller degrees: N = 9, parts of sizes 4 and 5, k = 64
    F, vals, degs = grid_space(N, m, [{0, 1, 2, 3}, {4, 5, 6, 7, 8}], 64)
    report("grid 2x2, rate 1/8", N, 64, vals, F, degs)
    # (iii) rate 1/2, L = 9: V = Lambda_B(l) * K[l]_{<9}, l = L_U, U group-sum subspace of codimension 6
    N, m, c, u, b = 11, 12, 6, 9, 23
    F = lib.GF(m)
    n, k = 1 << N, 1 << (N - 1)
    groups = [[0, 1], [2, 3], [4, 5], [6, 7], [8, 9], [10]]
    gens = []
    for g in groups:
        gens += [(1 << g[0]) ^ (1 << j) for j in g[1:]]
    U = lib.span(gens)
    assert len(U) == n >> c
    ell = lib.subspace_poly_values(F, U, list(range(n)))
    values = sorted(set(ell))
    assert len(values) == 1 << c
    rng = random.Random(59)
    B = rng.sample(values, b)
    lam = []
    for y in ell:
        v = 1
        for t in B:
            v = F.mul(v, y ^ t)
        lam.append(v)
    vals = [[F.mul(lam[x], F.pw(ell[x], j)) for x in range(n)] for j in range(u)]
    degs = [(b + j) * len(U) for j in range(u)]
    report("MDS type c=6 u=9 b=23, rate 1/2", N, k, vals, F, degs)
    # (iv) control: random V of the same dimensions (deficiency 0 expected)
    N, m, k, L = 7, 8, 32, 4
    F = lib.GF(m)
    n = 1 << N
    rng = random.Random(1)
    vals = []
    for _ in range(L):
        co = [rng.randrange(F.q) for _ in range(k)]
        row = []
        for x in range(n):
            v = 0
            for a in reversed(co):
                v = F.mul(v, x) ^ a
            row.append(v)
        vals.append(row)
    report("control: random V, rate 1/4", N, k, vals, F, [k - 1])


main()
