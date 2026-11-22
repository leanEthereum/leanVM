"""Note 64, item 2 diagnostic: on the quotient D' (16 points, GF(2^8)), how often do two random disjoint 4-point root
sets A, B give f_A + lam f_B with 4 further roots in D', and are these triples of fibres all flats (cosets of planes)?"""
import importlib.util, random, os
spec = importlib.util.spec_from_file_location("lib64", os.path.join(os.path.dirname(__file__), "64_lib.py"))
L = importlib.util.module_from_spec(spec); spec.loader.exec_module(L)
F = L.GF(8); rng = random.Random(1)
def peval(p, x):
    s = 0
    for c in reversed(p): s = F.mul(s, x) ^ c
    return s
LW = L.vanishing(F, [0, 1, 2, 3])
Dq = sorted({peval(LW, v) for v in range(64)})
def isflat(A):
    S = {x ^ A[0] for x in A}
    return all((x ^ y) in S for x in S for y in S)
trials = 200000; hits = flat = 0
for _ in range(trials):
    pts = Dq[:]; rng.shuffle(pts)
    A, B, rest = pts[3:7], pts[7:11], pts[11:]
    f1, f2 = L.vanishing(F, A), L.vanishing(F, B)
    lam = {}
    for x in rest: lam.setdefault(F.mul(peval(f1, x), F.inv(peval(f2, x))), []).append(x)
    b = max(lam.values(), key=len)
    if len(b) >= 4:
        hits += 1; flat += isflat(A) and isflat(B) and isflat(b)
print(f"trials {trials}: three full fibres {hits}, of which all three fibres are flats {flat}; generic prediction {trials*5/2**24:.3f}")
