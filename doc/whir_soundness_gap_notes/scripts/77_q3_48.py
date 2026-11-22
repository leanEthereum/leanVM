"""Note 77: Q_3 fails for today's code at (k, n) = (4, 8), D = <1, x, x^2> in GF(2^64).
Three codewords 0, f, g of degree 3 that coincide pairwise at all 8 points (Q_3 allows 7).
Also: the same test for random subspaces (kind G) and the count of all such partitions."""
import random, itertools, importlib.util, os, sys
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "74_gfpy.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
mul, inv = gf.mul, gf.inv

def span(basis):
    pts = [0]
    for b in basis: pts += [p ^ b for p in pts]
    return pts
def polymul(p, q):
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q): r[i + j] ^= mul(a, b)
    return r
def lam(S):
    p = [1]
    for s in S: p = polymul(p, [s, 1])
    return p
def ev(p, y):
    r = 0
    for c in reversed(p): r = mul(r, y) ^ c
    return r

x = 2
D = span([1, x, mul(x, x)])
A = [1, mul(x, x), mul(x, x) ^ 1]; B = [x, x ^ 1, mul(x, x) ^ x]; c = mul(x, x) ^ x ^ 1; C = [0, c]
f, g = lam(A), lam(B)
h = [a ^ b for a, b in zip(f, g)]
print("f + g coefficients (low to high):", [hex(t) for t in h], " expected c*y*(y+c) with c =", hex(c))
print("zeros of f:", sorted(y for y in D if ev(f, y) == 0), " of g:", sorted(y for y in D if ev(g, y) == 0), " of f+g:", sorted(y for y in D if ev(h, y) == 0))
cnt = sum(1 for y in D if ev(f, y) == 0 or ev(g, y) == 0 or ev(h, y) == 0)
print("coincidence points:", cnt, "of 8; Q_3 allows 2k-1 = 7")

def count_violations(D, k):
    """all unordered partitions of D into (A,B,C) (sizes <= k-1) carrying 3 distinct codewords with a coincidence at every point"""
    n = len(D); found = []
    for lab in itertools.product(range(3), repeat=n):
        if lab[0] != 0: continue  # symmetry: the point 0 is in A
        sz = [lab.count(i) for i in range(3)]
        if max(sz) > k - 1: continue
        # unknowns f (k coeffs), g (k coeffs); equations f(a)=0, g(b)=0, (f+g)(c)=0
        rows = []
        for y, l in zip(D, lab):
            pw = [1]
            for _ in range(k - 1): pw.append(mul(pw[-1], y))
            z = [0] * k
            rows.append(pw + z if l == 0 else z + pw if l == 1 else pw + pw)
        if gf.rank(rows) < 2 * k: found.append(lab)
    return found
v = count_violations(D, 4)
print("D = <1,x,x^2>: partitions (0 in A) with a list:", len(v))
for lab in v: print("   ", "".join("ABC"[l] for l in lab), " (points in order 0,1,x,x+1,x^2,x^2+1,x^2+x,x^2+x+1)")
rnd = random.Random(7)
tot = 0
for trial in range(20):
    while True:
        b = [rnd.getrandbits(64) for _ in range(3)]
        Dr = span(b)
        if len(set(Dr)) == 8: break
    tot += len(count_violations(Dr, 4))
print("20 random subspaces of GF(2^64) of dimension 3: partitions with a list in total:", tot)
