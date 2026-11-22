"""Note 64, Section 4b check: four polynomials of degree n/2 (k = n/2 + 1) built from the four cosets of a subspace U of
codimension 2, P_0 = 0, P_i = e_i * prod over j != i, j >= 1 of (L_U + c_j), with pointwise sum of (c_x - 1) equal to 2n > 3k,
and no free agreement for the cube window. GF(2^8), N = 4 and 6."""
import importlib.util, os
spec = importlib.util.spec_from_file_location("lib64", os.path.join(os.path.dirname(__file__), "64_lib.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)
F = L.GF(8)
def peval(p, x):
    s = 0
    for c in reversed(p): s = F.mul(s, x) ^ c
    return s
for N in (4, 6):
    n, k = 1 << N, (1 << N) // 2 + 1
    U = list(range(n // 4))                       # span(b_0 .. b_{N-3})
    LU = L.vanishing(F, U)
    c = [peval(LU, r * (n // 4)) for r in range(4)]   # the value of L_U on each coset
    shift = lambda j: [LU[0] ^ c[j]] + LU[1:]
    prod = {i: L.poly_mul(F, *[shift(j) for j in (1, 2, 3) if j != i]) for i in (1, 2, 3)}
    y0 = 0                                        # a point of coset 0; scale so that P_1 = P_2 = P_3 = 1 there
    P = [[0]] + [[F.mul(F.inv(peval(prod[i], y0)), a) for a in prod[i]] for i in (1, 2, 3)]
    assert all(len(p) <= k for p in P)
    ev = [[peval(p, x) for x in range(n)] for p in P]
    score = sum(max(sum(1 for j in range(4) if ev[j][x] == ev[i][x]) for i in range(4)) - 1 for x in range(n))
    free = 0
    for x in range(n):
        w = [x] + [x ^ (1 << i) for i in range(N)]
        free += max(sum(1 for j in range(4) if all(ev[j][y] == ev[i][y] for y in w)) for i in range(4)) - 1
    zmax = max(sum(1 for x in range(n) if ev[i][x] == ev[j][x]) for i in range(4) for j in range(i))
    print(f"N={N} n={n} k={k}: pointwise sum of (c_x - 1) = {score} against 3k = {3*k}; largest pairwise agreement {zmax} (< k);"
          f" free sum for the cube window = {free}")
