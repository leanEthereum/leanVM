"""Describe a word found by 02_lists climb: degree of its interpolant on D, and the agreement sets of its list.

usage: python3 02_climb_analyze.py <lists-binary> <climb-output-file> k T [power|rnd]
(rnd is the domain of 02_climb_run.sh: random basis with seed 21.)
"""
import sys, os, subprocess, random, importlib.util
from collections import Counter
spec = importlib.util.spec_from_file_location("gf", os.path.join(os.path.dirname(os.path.abspath(__file__)), "02_gf.py"))
gf = importlib.util.module_from_spec(spec); spec.loader.exec_module(gf)
F = gf.GF(64)
binary, path, k, T = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
dom = sys.argv[5] if len(sys.argv) > 5 else "power"
if dom == "power":
    D = list(range(16))
else:
    r = random.Random(21)
    D = gf.span([r.getrandbits(64) for _ in range(4)])
n = len(D)
w = [int(x, 16) for x in open(path).read().split(":")[1].split()]
poly = F.interpolate(D, w)
deg = max(i for i, c in enumerate(poly) if c)
inp = " ".join(f"{x:x}" for x in D) + "\n" + " ".join(f"{v:x}" for v in w) + "\n"
out = subprocess.run([binary, "members", "64", "1b", str(n), str(k), str(T)], input=inp, capture_output=True, text=True).stdout.split()
masks = [int(x, 16) for x in out]
def rank(vs):
    piv = {}
    for v in vs:
        while v:
            h = v.bit_length() - 1
            if h in piv: v ^= piv[h]
            else: piv[h] = v; break
    return len(piv)
sizes = Counter(bin(m).count("1") for m in masks)
inter = Counter(bin(a & b).count("1") for i, a in enumerate(masks) for b in masks[:i])
cover = Counter(sum(1 for m in masks if m >> p & 1) for p in range(n))
aff = Counter()
for m in masks:
    P = [i for i in range(n) if m >> i & 1]
    aff[rank([p ^ P[0] for p in P[1:]])] += 1
print(f"{os.path.basename(path)}: k={k} T={T} list={len(masks)} deg(w)={deg} nonzero coefficients={sum(1 for c in poly if c)}")
print(f"  agreement sizes {dict(sizes)}; pairwise intersections {dict(sorted(inter.items()))};")
print(f"  points by number of list members through them {dict(sorted(cover.items()))}; affine-span dims {dict(aff)}")
print("  sets:", " ".join(f"{m:04x}" for m in sorted(masks)))
