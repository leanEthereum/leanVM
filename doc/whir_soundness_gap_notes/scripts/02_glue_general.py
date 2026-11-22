"""Sampled check of the general hyperplane-gluing family (report 02, Theorem 5, general form).

Rate rho = 2^-R, U a subspace of D with |U| = n/M' (M' = 2^mp), g = rho M' + 1, word w = L_U^g.
For a hyperplane W of U and a 2g-subset Y of the 2M' labels L_W(D) with sum(Y) = g eta_W, the set
S = L_W^{-1}(Y) has g n / M' = (rho + 1/M') n points and deg(w - Z_S) <= rho n.

usage: python3 02_glue_general.py N R mp samples [seed]
"""
import sys, os, random, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
N, R, mp, samples = (int(a) for a in sys.argv[1:5])
rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
F = gf.GF(64)
n = 1 << N
k = n >> R
Mp = 1 << mp
g = (Mp >> R) + 1
D = gf.span(gf.power_basis(F, N))
while True:
    Ub = [rng.choice(D) for _ in range(N - mp)]
    if gf.rank_f2(Ub)[0] == N - mp:
        break
LU = gf.subspace_poly(F, Ub)
LUf = [0] * ((1 << (N - mp)) + 1)
for i, c in enumerate(LU):
    LUf[1 << i] = c
w = [1]
for _ in range(g):
    w = F.poly_mul(w, LUf)
T = g * n // Mp
done = 0
maxdeg = 0
while done < samples:
    phi = rng.randrange(1, 1 << (N - mp)) if N - mp > 0 else 0
    if N - mp == 0:
        Wb, eta_src = [], None
    piv = phi.bit_length() - 1
    Wb = [Ub[j] ^ (Ub[piv] if phi >> j & 1 else 0) for j in range(N - mp) if j != piv]
    LW = gf.subspace_poly(F, Wb)
    eta = gf.lin_eval(F, LW, Ub[piv])
    fib = {}
    for x in D:
        fib.setdefault(gf.lin_eval(F, LW, x), []).append(x)
    labels = sorted(fib)
    assert len(labels) == 2 * Mp
    Y = rng.sample(labels, 2 * g - 1)
    s = eta if g & 1 else 0
    for y in Y:
        s ^= y
    if s in Y or s not in fib:
        continue
    Y.append(s)
    S = sorted(x for y in Y for x in fib[y])
    assert len(S) == T
    Z = F.locator(S)
    P = [a ^ b for a, b in zip(w, Z)]
    deg = max((i for i, c in enumerate(P) if c), default=-1)
    assert deg <= k, (deg, k)
    maxdeg = max(maxdeg, deg)
    done += 1
print(f"N={N} rate 2^-{R} M'={Mp} g={g}: {samples} random members, agreement T={T} = ({g}/{Mp}) n, "
      f"deg(w - Z_S) <= k = {k} in every case (max seen {maxdeg})")
