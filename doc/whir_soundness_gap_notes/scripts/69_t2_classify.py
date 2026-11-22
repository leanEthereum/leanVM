#!/usr/bin/env python3
"""Task 2: classify the deficient patterns written by 69_t2_exh.c.
usage: 69_t2_classify.py deffile code [maxprint [feasible]]
With "feasible", only patterns that carry a list of pairwise distinct members for the code and none for the uniform matrix.
Orbits under member permutations and tree automorphisms; an orbit is called minimal when no pattern obtained by
removing one member from one class (or deleting a class of two) is deficient for the same code."""
import sys, itertools

def parse(line):
    head, pat = line.strip().split(" | ")
    f = head.split()
    fi = f.index("feas") if "feas" in f else len(f)
    ranks = {t.split("=")[0]: int(t.split("=")[1]) for t in f[3:fi]}
    feas = {t.split("=")[0]: int(t.split("=")[1]) for t in f[fi + 1:]}
    if FEASIBLE_ONLY and not (feas.get(CODE, 1) and not feas.get("U", 0)):
        ranks = dict(ranks); ranks[CODE] = ranks["U"]
    cls = tuple(frozenset() if c == "." else frozenset(int(ch) for ch in c) for c in pat.split())
    return int(f[0][2:]), ranks, cls

def tree_canon(seq):
    if len(seq) == 1:
        return (seq[0],)
    h = len(seq) // 2
    a, b = tree_canon(seq[:h]), tree_canon(seq[h:])
    return a + b if a <= b else b + a

def key(cls, perm=None):
    s = tuple(tuple(sorted(perm[m] for m in c)) if perm else tuple(sorted(c)) for c in cls)
    return tree_canon(s)

def full_canon(cls, members):
    return min(key(cls, p) for p in itertools.permutations(range(members)))

def show(k):
    return " ".join("".join(map(str, c)) if c else "." for c in k)

FEASIBLE_ONLY = len(sys.argv) > 4 and sys.argv[4] == "feasible"
CODE = sys.argv[2]

def main():
    path, code = sys.argv[1], sys.argv[2]
    maxprint = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    pats = {}
    members = 0
    for line in open(path):
        w, ranks, cls = parse(line)
        members = max(members, max((max(c) for c in cls if c), default=0) + 1)
        if ranks[code] < ranks["U"]:
            pats[key(cls)] = (w, ranks, cls)
    print(f"{path}: code {code}: {len(pats)} deficient patterns up to tree automorphisms, members {members}")
    orbits = {}
    for kk, (w, ranks, cls) in pats.items():
        orbits.setdefault(full_canon(cls, members), []).append((w, ranks, cls))
    def minimal(cls):
        for x, c in enumerate(cls):
            if not c:
                continue
            subs = [frozenset()] if len(c) == 2 else [c - {m} for m in c]
            for s in subs:
                q = cls[:x] + (s,) + cls[x + 1:]
                if key(q) in pats:
                    return False
        return True
    rows = []
    for ok, lst in orbits.items():
        w, ranks, cls = lst[0]
        rows.append((w, ok, len(lst), ranks, minimal(cls)))
    rows.sort(key=lambda t: (not t[4], t[0], t[1]))
    nmin = sum(1 for t in rows if t[4])
    print(f"orbits under members x tree: {len(rows)}, of which minimal: {nmin}")
    for w, ok, cnt, ranks, mn in rows[:maxprint]:
        others = " ".join(f"{c}={v}" for c, v in ranks.items())
        print(f"  {'MIN' if mn else '   '} weight {w:2d} [{others}] x{cnt:3d}: {show(ok)}")

main()
