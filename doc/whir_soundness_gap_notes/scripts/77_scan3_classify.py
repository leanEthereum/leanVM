"""Note 77: classify the singular labelings printed by 77_scan3 (three members, one functional per point).
A labeling is a LIFT if the true zero sets A, B, C of the kernel are, after completing them by common zeros T, all invariant under one
translation y -> y + b, b in D nonzero (then they are unions of cosets of {0, b} and Theorem 5.2 applies). Otherwise it is NOT a lift.
Points are indexed by the bits of their coordinates in the basis, so a translation is an XOR of indices.
usage: 77_scan3_classify.py file [file ...]"""
import sys
from collections import Counter
def classify(tr):
    """lift: for some b, every point of A (of B, of C) has its partner x + b in the same set or among the common zeros T.
    Then the kernel is B(y) * (aligned triple), B vanishing on T, and a point of T whose partner lies in A completes A's pair."""
    n = len(tr)
    for b in range(1, n):
        if all(tr[i ^ b] in (tr[i], "T") for i in range(n) if tr[i] in "ABC"): return True
    return False
def canon(tr):
    """smallest image under translations and renamings of A, B, C (first occurrence order)"""
    n = len(tr); best = None
    for t in range(n):
        s = [tr[i ^ t] for i in range(n)]
        m = {}; out = []
        for ch in s:
            if ch in "ABC":
                if ch not in m: m[ch] = "ABC"[len(m)]
                out.append(m[ch])
            else: out.append(ch)
        o = "".join(out)
        if best is None or o < best: best = o
    return best
for fn in sys.argv[1:]:
    rows = [l.split() for l in open(fn) if l.strip()]
    def rename(t):
        m = {}; out = []
        for ch in t:
            if ch in "ABC":
                if ch not in m: m[ch] = "ABC"[len(m)]
                out.append(m[ch])
            else: out.append(ch)
        return "".join(out)
    trues = sorted({rename(r[2]) for r in rows})
    lift = [t for t in trues if classify(t)]; non = [t for t in trues if not classify(t)]
    def sizes(t): return (tuple(sorted((t.count("A"), t.count("B"), t.count("C")), reverse=True)), t.count("T"))
    print(f"{fn}: singular labelings {len(rows)}, distinct kernels (true patterns up to renaming) {len(trues)}: lifts {len(lift)}, not lifts {len(non)}")
    print("   lifts by (sizes, common zeros):", dict(sorted(Counter(sizes(t) for t in lift).items())))
    print("   not lifts by (sizes, common zeros):", dict(sorted(Counter(sizes(t) for t in non).items())))
    orb = sorted({canon(t) for t in non})
    print(f"   not lifts: {len(orb)} orbits under translations and renaming; first: {orb[:3]}")
