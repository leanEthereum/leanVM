"""Note 83, Section 4: for the lists at n = 16 that are not products at level 1, all maximal sub-lists whose differences
are products A (x) B at level 1 and at level 2 (flattening rank 1), and the pairwise agreements of the members.
Usage: 83_products.py n file"""
import sys, os, random, itertools, importlib.util
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(here, name + ".py")); m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m
L83 = load("83_lib"); P = load("83_profile")
n = int(sys.argv[1]); rnd = random.Random(4242); agg = {}
for line in open(sys.argv[2]):
    if "classes per leaf:" not in line: continue
    cls = P.parse(line); v = (n // 2).bit_length() - 1; k = n // 2; t = max(c.bit_length() for c in cls); Lk = (t - 1) * k
    tw = L83.make_tw(v, rnd); G = L83.gen(tw, v)
    ker = L83.kernel(np.array(L83.rows_of(G, k, t, cls)), Lk); pt = L83.random_point(ker, rnd); cw = L83.codewords(G, k, t, pt)
    if P.flat_rank(pt, range(t), 0, k, 1) == 1: continue
    out = []
    for lev in (1, 2):
        mx = []
        for size in range(t, 1, -1):
            for sub in itertools.combinations(range(t), size):
                if any(set(sub) <= set(m) for m in mx): continue
                if P.flat_rank(pt, sub, sub[0], k, lev) == 1: mx.append(sub)
        out.append(mx)
    pair = {(a, b): int(np.sum(cw[a] == cw[b])) for a in range(t) for b in range(a + 1, t)}
    pairfull = {(a, b): sum(1 for p in range(n // 2) if cw[a][2 * p] == cw[b][2 * p] and cw[a][2 * p + 1] == cw[b][2 * p + 1]) for a in range(t) for b in range(a + 1, t)}
    key = (tuple(sorted(len(m) for m in out[0])), tuple(sorted(len(m) for m in out[1])), tuple(sorted(pair.values())), tuple(sorted(pairfull.values())))
    agg.setdefault(key, []).append((line.split("classes per leaf:")[1].strip(), out, pair))
print("# key: sizes of the maximal product sub-lists at level 1, at level 2, sorted pairwise agreements (leaves), sorted pairwise full pairs")
for key, ex in sorted(agg.items(), key=lambda kv: -len(kv[1])):
    print(len(ex), "patterns:", key); print("    e.g.", ex[0][0]); print("    product sub-lists level 1:", ex[0][1][0], "level 2:", ex[0][1][1]); print("    pair agreements:", ex[0][2])
