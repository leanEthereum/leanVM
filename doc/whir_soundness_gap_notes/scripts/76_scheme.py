"""Note 76, Theorem 4.1: the best recursive split/merge scheme r_v for patterns at (4,8), against the exact rank.
A graphic space is a set partition of the members (its dimension: members minus blocks); a sum of spaces is the join."""
import sys, os, re, itertools, functools
def join(P, Q):
    """P, Q: tuples of frozensets (blocks of size >= 2 only)"""
    blocks = [set(b) for b in P] + [set(b) for b in Q]
    out = []
    for b in blocks:
        merged = set(b); rest = []
        for c in out:
            if c & merged: merged |= c
            else: rest.append(c)
        out = rest + [merged]
    return tuple(sorted((frozenset(b) for b in out), key=sorted))
def dim(P): return sum(len(b) - 1 for b in P)
E = ()
@functools.lru_cache(maxsize=None)
def r(state):
    """state: tuple of partitions on the nodes of the two trees (first half tree 0), length 2 * 2^v"""
    n = len(state)
    if n == 2: return dim(join(state[0], state[1]))
    best = 0
    for opt in itertools.product(range(4), repeat=n // 2):
        s0 = []; s1 = []
        for p, o in enumerate(opt):
            a, b = state[2 * p], state[2 * p + 1]
            if o == 0: s0.append(a); s1.append(b)
            elif o == 1: s0.append(b); s1.append(a)
            elif o == 2: s0.append(join(a, b)); s1.append(E)
            else: s0.append(E); s1.append(join(a, b))
        val = r(tuple(s0)) + r(tuple(s1))
        if val > best: best = val
    return best
here = os.path.dirname(os.path.abspath(__file__))
for fn in ["69_t2_def_4_8_3_full.txt", "74_def_4_8_4.txt"]:
    tot = eq = low = 0
    for line in open(os.path.join(here, fn)):
        head, pat = line.split("|"); rk = int(re.search(r" 2=(\d+)", head).group(1))
        state = tuple(E if c == "." or len(c) < 2 else (frozenset(int(ch) for ch in c),) for c in pat.split())
        val = r(state); tot += 1; eq += val == rk; low += val > rk
    print(f"{fn}: patterns {tot}, best scheme equals the rank: {eq}, best scheme above the rank (would contradict Theorem 4.1): {low}")
