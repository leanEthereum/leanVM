"""The dual space D* of leanVM's real domain and the subfield test for label spaces (report 02, section 7).

For a hyperplane H = ker(phi) of D put u_phi = prod_{x in D \\ H} x = L_H(a) (any a with phi(a) = 1) and
w_phi = 1/u_phi. Then phi -> w_phi is F_2-linear (checked here by brute force for N <= 6), so
D* = {w_phi} + {0} is an N-dimensional subspace of K. For a subspace W of D, the label space L_W(D) has
(L_W(D))* = {w_phi : phi vanishes on W}, a subspace of D*. If L_W(D) lay in c F for a subfield F of K, with
dimension >= 2, two elements of D* would have a ratio in F \\ F_2, i.e. D* and lambda D* would meet for some
lambda in F \\ F_2. The script computes dim(D* cap lambda D*) for every lambda in F_256 \\ F_2 (and F_65536).

usage: python3 02_dual_space.py [N] [check16]
"""
import sys, os, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
F = gf.GF(64)


def dual_basis(basis):
    ws = []
    for i, b in enumerate(basis):
        c = gf.subspace_poly(F, basis[:i] + basis[i + 1:])
        ws.append(F.inv(gf.lin_eval(F, c, b)))
    return ws


# brute-force check of linearity for small N
for N in (3, 4, 5, 6):
    basis = gf.power_basis(F, N)
    D = gf.span(basis)
    ws = dual_basis(basis)
    for phi in range(1, 1 << N):
        prod = 1
        for i, x in enumerate(D):
            if bin(i & phi).count("1") & 1:
                prod = F.mul(prod, x)
        lin = 0
        for j in range(N):
            if phi >> j & 1:
                lin ^= ws[j]
        assert F.mul(prod, lin) == 1, (N, phi)
print("phi -> 1/prod_{x in D, phi(x)=1} x is linear: checked for N = 3..6 (power basis, all functionals)")

N = int(sys.argv[1]) if len(sys.argv) > 1 else 25
basis = gf.power_basis(F, N)
ws = dual_basis(basis)
rk, piv = gf.rank_f2(ws)
print(f"N={N}: dim D* = {rk}")

# subfield F_256 = {z : z^256 = z}
def subfield_elems(e):
    # generator of the subgroup of order 2^e - 1
    q1 = (1 << 64) - 1
    for h in range(2, 200):
        g = F.pow(h, q1 // ((1 << e) - 1))
        # order exactly 2^e - 1?
        ok = all(F.pow(g, ((1 << e) - 1) // p) != 1 for p in (3, 5, 17, 257) if ((1 << e) - 1) % p == 0)
        if ok:
            break
    out, x = [], 1
    for _ in range((1 << e) - 1):
        out.append(x)
        x = F.mul(x, g)
    assert x == 1
    return out


def meet_dim(lam):
    r2, _ = gf.rank_f2(ws + [F.mul(lam, w) for w in ws])
    return 2 * N - r2


for e in (8,) + ((16,) if len(sys.argv) > 2 else ()):
    hits = {}
    for lam in subfield_elems(e):
        if lam == 1:
            continue
        d = meet_dim(lam)
        if d:
            hits[d] = hits.get(d, 0) + 1
    print(f"N={N}: lambda in F_2^{e} \\ F_2 with D* cap lambda D* != 0: {hits if hits else 'none'}"
          f" (expected number for a random {N}-dimensional space: about {((1 << e) - 2) * 2.0 ** (2 * N - 64):.3g})")
