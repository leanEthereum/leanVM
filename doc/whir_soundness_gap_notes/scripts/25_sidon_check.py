"""Researcher 25. Additive quadruples in lists (note 25, Theorem 1.1).

Theorem 1.1: four distinct list members with c1 + c2 + c3 + c4 = 0 force T <= (n + 3d)/4 (d the degree bound).
Check of tightness: the family of note 02 Theorem 5 on a 16-point domain (word (y^2 + eta y)^5, degree <= 8,
agreement 10 = (16 + 24)/4, 504 members) contains additive quadruples, so the bound is attained.

Check of the statement above the threshold: note 18 found a list of 16 at (n, degree, T) = (16, <= 8, 11),
with agreement sets the 16 translates of one set. The word and the codewords are recovered by linear algebra
on this script's domain and tested: no coincidence c_i + c_j = c_k + c_l, as 11 > (16 + 24)/4 requires.

usage: python3 25_sidon_check.py [seed]
"""
import sys, os, random, itertools, importlib.util
from collections import defaultdict
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
rng = random.Random(seed)
F = gf.GF(64)
basis = gf.random_basis(F, 4, rng)
D = gf.span(basis)
eta = basis[0]
n, d, T = 16, 8, 10
assert 4 * T == n + 3 * d

# members: 10-subsets Y of D with sum eta; the codeword is (y^2 + eta y)^5 - Z_Y(y), of degree <= 8
betas = [F.rand(rng) for _ in range(3)]  # codewords are compared through their values at three random points
def fingerprint(Y):
    out = []
    for b in betas:
        z = 1
        for y in Y:
            z = F.mul(z, b ^ y)
        q = F.mul(b, b) ^ F.mul(eta, b)
        out.append(F.pow(q, 5) ^ z)
    return tuple(out)

members = []
for Y in itertools.combinations(D, 10):
    s = 0
    for y in Y:
        s ^= y
    if s == eta:
        members.append((Y, fingerprint(Y)))
print(f"n = {n}, degree <= {d}, agreement {T} = (n + 3d)/4: {len(members)} members of the word (y^2 + eta y)^5")

# additive quadruples: pairs {i, j} with equal sums of fingerprints
sums = defaultdict(list)
for i in range(len(members)):
    fi = members[i][1]
    for j in range(i + 1, len(members)):
        fj = members[j][1]
        sums[(fi[0] ^ fj[0], fi[1] ^ fj[1], fi[2] ^ fj[2])].append((i, j))
quads = sum(len(v) * (len(v) - 1) // 2 for v in sums.values())
print(f"coincidences c_i + c_j = c_k + c_l among them: {quads}, that is {quads // 3} additive quadruples (each gives three)")
# in a quadruple every point lies in 0, 1, 2 or 4 of the four agreement sets, and the count is tight
checked = 0
for v in sums.values():
    if len(v) >= 2:
        (i, j), (k, l) = v[0], v[1]
        sets = [set(members[t][0]) for t in (i, j, k, l)]
        mult = [sum(x in s for s in sets) for x in D]
        assert all(m in (0, 1, 2, 4) for m in mult), mult
        assert sum(mult) == 4 * T
        checked += 1
        if checked == 200:
            break
print(f"multiplicity pattern in {{0,1,2,4}} and sum 4T verified on {checked} quadruples")

# Above the threshold. Note 18 found, at (n, degree, T) = (16, <= 8, 11), a list of 16: the agreement sets are
# the 16 translates of the set with mask 0x177f (bit i = point with coordinates i). The word and the 16 codewords
# are recovered here by linear algebra on this script's random domain (unknowns: w off S_0 and c_1..c_15, with
# c_0 = 0), then the 16 codewords are tested for coincidences c_i + c_j = c_k + c_l. 11 > (16 + 24)/4 = 10.
def solve_null(rows, ncols):
    """one nonzero null vector of the matrix (list of rows), or None"""
    rows = [r[:] for r in rows]
    piv = []
    rk = 0
    for c in range(ncols):
        p = next((i for i in range(rk, len(rows)) if rows[i][c]), None)
        if p is None:
            continue
        rows[rk], rows[p] = rows[p], rows[rk]
        iv = F.inv(rows[rk][c])
        rows[rk] = [F.mul(iv, v) if v else 0 for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c]:
                f = rows[i][c]
                rows[i] = [a ^ F.mul(f, b) if b else a for a, b in zip(rows[i], rows[rk])]
        piv.append(c)
        rk += 1
    free = [c for c in range(ncols) if c not in piv]
    if not free:
        return None, 0
    v = [0] * ncols
    v[free[0]] = 1
    for i, c in enumerate(piv):
        v[c] = rows[i][free[0]]
    return v, len(free)

base = 0x177f
masks16 = [sum(1 << (x ^ t) for x in range(16) if base >> x & 1) for t in range(16)]
assert len(set(masks16)) == 16
K1 = 9  # degree <= 8
off = [x for x in range(16) if not base >> x & 1]           # the 5 points where w is unknown (w = c_0 = 0 on S_0)
ncols = 15 * K1 + len(off)
rows = []
pw = [[F.pow(D[x], e) for e in range(K1)] for x in range(16)]
for t in range(1, 16):
    for x in range(16):
        if masks16[t] >> x & 1:
            r = [0] * ncols
            for e in range(K1):
                r[(t - 1) * K1 + e] = pw[x][e]
            if x in off:
                r[15 * K1 + off.index(x)] = 1
            rows.append(r)
v, nfree = solve_null(rows, ncols)
print(f"translation orbit of 0x177f on this domain: solution space of dimension {nfree}")
if v is not None:
    polys = [tuple([0] * K1)] + [tuple(v[(t - 1) * K1:(t - 1) * K1 + K1]) for t in range(1, 16)]
    distinct = len(set(polys))
    sums2 = defaultdict(int)
    for i in range(16):
        for j in range(i + 1, 16):
            sums2[tuple(a ^ b for a, b in zip(polys[i], polys[j]))] += 1
    q2 = sum(c * (c - 1) // 2 for c in sums2.values())
    print(f"16 codewords of degree <= 8 at agreement 11 > (n + 3d)/4 = 10: {distinct} distinct, coincidences c_i + c_j = c_k + c_l: {q2} (Theorem 1.1 says 0)")
    assert distinct == 16 and q2 == 0
