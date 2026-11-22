"""Note 83, Section 4: the pair structure of exact lists. For every pattern (classes per leaf, as printed by 76_n8 or
76_orbits.py) on the generic tree code [n, n/2]: kernel dimension s of the word pattern, a generic kernel point, its full
coincidence partitions pi_x, the pair partitions pi_p, the top kernel s' = dim S'(pi), the number E of essential leaves
(Lemma 2.2: s(pi) <= 2 s' - E), for every member its full pairs f, half leaves h and the votes lost (Lemma 2.3), and
the product structure (flattening rank of the differences at each level, for the list and its sub-lists).
Usage: 83_profile.py n file [max]   (lines containing 'classes per leaf:' followed by classes, '|' ignored)."""
import sys, os, random, itertools, importlib.util
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("lib83", os.path.join(here, "83_lib.py")); L83 = importlib.util.module_from_spec(spec); spec.loader.exec_module(L83)

def parse(line):
    s = line.split("classes per leaf:")[1].split("sizes:")[0]
    out = []
    for tok in s.split():
        if tok == "|": continue
        out.append(0 if tok == "." else sum(1 << int(ch, 36) for ch in tok))
    return out
def flat_rank(pt, members, base, k, lev):
    """rank of the differences d_l - d_base, l in members, flattened as (member, upper index) x (lower index of 2^lev)"""
    low = 1 << lev; rows = []
    def d(l): return pt[(l - 1) * k:l * k] if l >= 1 else np.zeros(k, dtype=np.uint64)
    for l in members:
        if l == base: continue
        v = d(l) ^ d(base)
        rows += [v[u * low:(u + 1) * low] for u in range(k // low)]
    return L83.rank(np.array(rows))
def analyse(cls, n, rnd, verbose=True):
    v = (n // 2).bit_length() - 1; k = n // 2; t = max(c.bit_length() for c in cls); Lk = (t - 1) * k
    tw = L83.make_tw(v, rnd); G = L83.gen(tw, v)
    ker = L83.kernel(np.array(L83.rows_of(G, k, t, cls)), Lk); s = len(ker)
    pt = L83.random_point(ker, rnd); cw = L83.codewords(G, k, t, pt)
    assert len(set(map(tuple, cw.tolist()))) == t, "members not distinct"
    parts = [L83.partition_at(cw[:, x]) for x in range(n)]
    for x in range(n): assert cls[x] == 0 or bin(cls[x]).count("1") == 1 or any(c & cls[x] == cls[x] for c in parts[x]), "class not realized"
    pparts = [L83.partition_at([(int(cw[l, 2 * p]), int(cw[l, 2 * p + 1])) .__hash__() if False else (int(cw[l, 2 * p]) << 64) | int(cw[l, 2 * p + 1]) for l in range(t)]) for p in range(n // 2)]
    s_pi = len(L83.kernel(np.array(L83.rows_of_partition(G, k, t, parts)), Lk))
    Gtop = G[0::2, 0::2]   # rows g_p of the top code (even indices: bottom bit 0)
    rows_top = L83.rows_of_partition(Gtop, k // 2, t, pparts)
    s_top = len(L83.kernel(np.array(rows_top), (t - 1) * (k // 2))) if rows_top else (t - 1) * (k // 2)
    E = sum(1 for x in range(n) if parts[x] != pparts[x // 2])
    prof = []
    for l in range(t):
        f = sum(1 for p in range(n // 2) if (cls[2 * p] >> l) & 1 and (cls[2 * p + 1] >> l) & 1)
        h = sum(1 for x in range(n) if (cls[x] >> l) & 1) - 2 * f
        lost = 0
        for x in range(n):
            if not (cls[x] >> l) & 1: continue
            # classes of pi_p inside C_x (singletons included)
            sub = {}
            for m in L83.bits(cls[x]): sub.setdefault((int(cw[m, 2 * (x // 2)]), int(cw[m, 2 * (x // 2) + 1])), []).append(m)
            if len(sub) >= 2:
                big = max(sub.values(), key=lambda c: (len(c), -min(c)))
                if l not in big: lost += 1
        prof.append((f, h, lost))
    # product structure: largest sub-lists whose differences have flattening rank 1 at level lev
    prod = {}
    for lev in range(1, v + 1):
        best = []
        for size in range(t, 1, -1):
            for sub in itertools.combinations(range(t), size):
                if flat_rank(pt, sub, sub[0], k, lev) == 1: best.append(sub)
            if best: break
        prod[lev] = best
    fr = [flat_rank(pt, range(t), 0, k, lev) for lev in range(1, v + 1)]
    return dict(t=t, s=s, s_pi=s_pi, s_top=s_top, E=E, prof=prof, prod=prod, flat=fr, parts=parts, pparts=pparts)
if __name__ == "__main__":
    n = int(sys.argv[1]); fn = sys.argv[2]; mx = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
    rnd = random.Random(8383); cnt = 0; agg = {}
    for line in open(fn):
        if "classes per leaf:" not in line: continue
        cls = parse(line); assert len(cls) == n
        r = analyse(cls, n, rnd); cnt += 1
        prof = sorted(r["prof"], reverse=True)
        key = (r["s"], r["s_pi"], r["s_top"], r["E"], tuple(r["flat"]), tuple(prof), tuple(len(r["prod"][lev][0]) if r["prod"][lev] else 1 for lev in sorted(r["prod"])))
        agg.setdefault(key, []).append(line.split("classes per leaf:")[1].strip())
        if cnt >= mx: break
    print(f"# n={n}: {cnt} patterns analysed. key = (s, s(pi), s_top, E, flattening ranks by level, sorted member profiles (full pairs, half leaves, votes lost), largest product sub-list by level)")
    for key, ex in sorted(agg.items(), key=lambda kv: -len(kv[1])):
        print(len(ex), "patterns:", "s=%d s(pi)=%d s_top=%d E=%d flat=%s" % key[:5], "profiles", list(key[5]), "largest product sub-list by level", list(key[6]), " e.g.", ex[0])
