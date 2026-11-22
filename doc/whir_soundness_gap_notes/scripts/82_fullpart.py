"""Note 82, 3.3 (a): the full-part tuple is not exact in general. One triple leaf and five pair-class leaves at six
different vectors of W = K^2 (a pattern at (4,16): leaves in six different bottom pairs). Arithmetic mod a prime
(the statement does not depend on the characteristic). Checks: rank 7 = w, the solution restricted to the block of the
triple leaf has rank one, its left kernel nu moves with the twiddle t_j of the triple leaf, and nu (x) g (x) F^2 is in R."""
import random
P = (1 << 61) - 1
def rank_and_kernel(rows, ncols):
    M = [r[:] for r in rows]; piv = []; rk = 0
    for c in range(ncols):
        p = next((i for i in range(rk, len(M)) if M[i][c] % P), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]; inv = pow(M[rk][c], P - 2, P); M[rk] = [a * inv % P for a in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][c] % P: f = M[i][c]; M[i] = [(a - f * b) % P for a, b in zip(M[i], M[rk])]
        piv.append(c); rk += 1
    ker = []
    for c in range(ncols):
        if c in piv: continue
        v = [0] * ncols; v[c] = 1
        for i, pc in enumerate(piv): v[pc] = (-M[i][c]) % P
        ker.append(v)
    return rk, ker
def tens(a, h, z): return [x * y % P * w % P for x in a for y in h for w in z]  # K^2 (x) W (x) F^2, index 4a + 2h + z
def run(seed, tj=None):
    rnd = random.Random(seed)
    g = [rnd.randrange(P), rnd.randrange(P)]; hs = [[rnd.randrange(P), rnd.randrange(P)] for _ in range(5)]
    lines = [[1, 0], [1, 0], [0, 1], [0, 1], [1, 1]]; ts = [rnd.randrange(P) for _ in range(5)]
    if tj is None: tj = rnd.randrange(P)
    rows = [tens(l, h, [1, t]) for l, h, t in zip(lines, hs, ts)] + [tens([1, 0], g, [1, tj]), tens([0, 1], g, [1, tj])]
    rk, ker = rank_and_kernel(rows, 8); psi = ker[0]
    D = [[sum(psi[4 * a + 2 * i + b] * g[i] for i in range(2)) % P for b in range(2)] for a in range(2)]  # Delta(a, y)
    det = (D[0][0] * D[1][1] - D[0][1] * D[1][0]) % P
    nu = (D[1][0], (-D[0][0]) % P) if D[0][0] or D[1][0] else (D[1][1], (-D[0][1]) % P)  # left kernel
    ratio = nu[0] * pow(nu[1], P - 2, P) % P
    rk2, _ = rank_and_kernel(rows + [tens(list(nu), g, [1, 0]), tens(list(nu), g, [0, 1])], 8)
    return rk, len(ker), det, ratio, rk2
a = run(1, tj=12345); b = run(1, tj=67890)
print("rank, kernel dim, det of the block form, slope of nu, rank after adding nu (x) g (x) F^2:")
print(" t_j = 12345:", a); print(" t_j = 67890:", b)
print("rank 7 = w:", a[0] == 7, "| block form of rank one:", a[2] == 0, "| nu (x) g (x) F^2 inside R:", a[4] == 7, "| nu moves with t_j:", a[3] != b[3])
