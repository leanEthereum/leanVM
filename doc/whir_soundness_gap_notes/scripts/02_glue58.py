"""Check the hyperplane-gluing family at rate 1/2, agreement 5n/8, degree <= n/2 (report 02, Theorem 5).

D = span(1, x, ..., x^(N-1)) in K = GF(2^64) (leanVM's field), U a subspace of D with |U| = n/8, word w = L_U^5.
For every hyperplane W of U and every 10-subset Y of the 16 labels L_W(D) with sum(Y) = eta_W (the nonzero element
of L_W(U)), the set S = L_W^{-1}(Y) has 5n/8 points and w - Z_S has degree <= n/2.

The script enumerates all members, checks deg(w - Z_S) <= n/2 by computing the locator (all members for n <= 64,
a random sample otherwise), checks agreement of P = w - Z_S with w on S and nowhere else, and counts distinct sets:
expected 56 + 448 (n/8 - 1).

usage: python3 02_glue58.py N [seed] [sample]
"""
import sys, os, random, itertools, importlib.util
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
sample = int(sys.argv[3]) if len(sys.argv) > 3 else (10**9 if N <= 6 else 40)
rng = random.Random(seed)
F = gf.GF(64)
n = 1 << N
Dbasis = gf.power_basis(F, N)
D = gf.span(Dbasis)

# a random subspace U of D of dimension N - 3
while True:
    Ubasis = [rng.choice(D) for _ in range(N - 3)]
    if gf.rank_f2(Ubasis)[0] == N - 3:
        break
U = gf.span(Ubasis)
LU = gf.subspace_poly(F, Ubasis)
# word w = L_U^5 as a polynomial (low first)
LU_full = [0] * (len(U) + 1)
for i, c in enumerate(LU):
    LU_full[1 << i] = c
w = [1]
for _ in range(5):
    w = F.poly_mul(w, LU_full)
assert len(w) - 1 == 5 * n // 8
wvals = {x: F.poly_eval(w, x) for x in D}

# hyperplanes of U: kernels of nonzero functionals on the coordinates of Ubasis
members = set()
checked = 0
maxdeg = 0
nonper = 0
for phi in range(1, 1 << (N - 3)):
    # W = {u in U : <phi, coords(u)> = 0}; build a basis
    Wb, out = [], None
    piv = phi.bit_length() - 1
    for j in range(N - 3):
        if j == piv:
            continue
        Wb.append(Ubasis[j] ^ (Ubasis[piv] if phi >> j & 1 else 0))
    LW = gf.subspace_poly(F, Wb)
    eta = gf.lin_eval(F, LW, Ubasis[piv])
    assert eta != 0
    fib = {}
    for x in D:
        fib.setdefault(gf.lin_eval(F, LW, x), []).append(x)
    labels = sorted(fib)
    assert len(labels) == 16 and all(len(v) == n // 16 for v in fib.values())
    fam = []
    for Y in itertools.combinations(labels, 10):
        s = 0
        for y in Y:
            s ^= y
        if s == eta:
            fam.append(Y)
    assert len(fam) == 504
    for Y in fam:
        S = frozenset(x for y in Y for x in fib[y])
        if S in members:
            continue
        members.add(S)
        if rng.random() * len(fam) < sample or sample >= 10**9:
            Z = F.locator(sorted(S))
            P = [a ^ b for a, b in zip(w, Z)]
            deg = max((i for i, c in enumerate(P) if c), default=-1)
            assert deg <= n // 2, deg
            maxdeg = max(maxdeg, deg)
            agree = sum(1 for x in D if F.poly_eval(P[: n // 2 + 1], x) == wvals[x])
            assert agree == 5 * n // 8, agree
            checked += 1
# genuine variant: members through a fixed point p, divided by (X - p)
p = D[1]
c = wvals[p]
# w' = (w - c)/(X - p) by synthetic division
def div_linear(poly, root):
    q = [0] * (len(poly) - 1)
    carry = 0
    for d in range(len(poly) - 1, 0, -1):
        carry = poly[d] ^ F.mul(carry, root)
        q[d - 1] = carry
    assert poly[0] ^ F.mul(carry, root) == 0, "not divisible"
    return q
wc = list(w); wc[0] ^= c
w1 = div_linear(wc, p)
w1vals = {x: F.poly_eval(w1, x) for x in D}
through = [S for S in members if p in S]
gchecked = 0
for S in through:
    if rng.random() * len(through) < sample or sample >= 10**9:
        Z1 = F.locator(sorted(S - {p}))
        P1 = [a ^ b for a, b in zip(w1, Z1)]
        deg = max((i for i, cc in enumerate(P1) if cc), default=-1)
        assert deg <= n // 2 - 1, deg
        agree = sum(1 for x in D if F.poly_eval(P1[: n // 2], x) == w1vals[x])
        assert agree >= 5 * n // 8 - 1
        gchecked += 1
gexp = 35 + 280 * (n // 8 - 1)
print(f"N={N}: genuine variant, word (L_U^5 - c)/(X - p): {len(through)} members through p (expected {gexp}); "
      f"{gchecked} checked: degree <= n/2 - 1, agreement >= {5*n//8 - 1}")
assert len(through) == gexp
expected = 56 + 448 * (n // 8 - 1)
print(f"N={N} n={n}: {len(members)} distinct sets (expected {expected}); {checked} members checked in full: "
      f"deg(w - Z_S) <= n/2 = {n//2} (max seen {maxdeg}), agreement exactly {5*n//8}")
assert len(members) == expected
