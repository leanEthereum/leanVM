# Researcher 21 (referee). The 105n - 965 genuine codewords at agreement exactly 9n/16 (note 12, Theorem 5.2).
# Input: dumps of 21_walsh rm2 (class of seven cosets of a codimension-4 subspace Y, bottom bits) for n = 32, 64, 128.
# Checks: the count, the structure (every member is invariant under a hyperplane of Y), and, with field arithmetic in
# K = GF(2^64) on the leanVM shape and on a random basis, that the complements (9n/16 points) share e_1..e_(n/8-1).
# Usage: python3 21_nine16_checks.py dump32 dump64 dump128
import importlib
import random
import sys

sys.dont_write_bytecode = True
gf = importlib.import_module("21_gf")
F = gf.K64
rng = random.Random(916)

for path in sys.argv[1:]:
    members = [int(l, 16) for l in open(path)]
    szs = {bin(m).count("1") for m in members}
    assert len(szs) == 1
    s = szs.pop()
    n = s * 16 // 7
    N = n.bit_length() - 1
    assert len(members) == len(set(members)) == 105 * n - 965, (len(members), n)
    ydim = N - 4

    def invariant(m, h):
        t = 0
        for x in range(n):
            if m >> x & 1:
                t |= 1 << (x ^ h)
        return t == m

    # stabilizer inside Y = points 0..2^ydim - 1
    hist = {}
    for m in members:
        st = [h for h in range(1 << ydim) if invariant(m, h)]
        hist[len(st)] = hist.get(len(st), 0) + 1
    full = hist.get(1 << ydim, 0)
    half = hist.get(1 << (ydim - 1), 0)
    assert full == 715 and half == 1680 * ((1 << ydim) - 1) and full + half == len(members)
    print(f"n={n}: {len(members)} = 105n-965 members; {full} invariant under Y, {half} = 1680(n/16-1) invariant under exactly a hyperplane of Y")
    full_mask = (1 << n) - 1
    t = n // 8 - 1
    for name, basis in (("leanVM shape", gf.power_basis(N)), ("random basis", gf.random_basis(F, N, rng))):
        D = gf.span(basis)
        sample = members if n <= 64 else rng.sample(members, 1500)
        tops = set()
        nxt = set()
        for m in sample:
            comp = full_mask ^ m
            pts = [D[x] for x in range(n) if comp >> x & 1]
            assert len(pts) == 9 * n // 16
            e = gf.top_coeffs(F, pts, t + 1)
            tops.add(tuple(e[1:t + 1]))
            nxt.add(e[t + 1])
        assert len(tops) == 1
        print(f"   {name}: {len(sample)} complements (9n/16 = {9 * n // 16} points) share e_1..e_{t}: pairwise locator differences of degree <= 7n/16 = {7 * n // 16} < n/2;"
              f" e_(n/8) takes {len(nxt)} values")
