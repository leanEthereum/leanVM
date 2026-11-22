#!/usr/bin/env python3
"""Note 60, Section 1 and 2: window shapes in abelian groups of order 16, by exhaustion.

For each (group, offset set C): kappa(C) from the subgroup formula of Lemma 1.1,
and over all 2^16 - 1 nonempty sets J: the closure J + C, the boundary, and the checks
  (a) J + C = J  iff  J is a union of blocks (cosets of <C>),
  (b) boundary < kappa  =>  the closure is a union of blocks,
  (c) min boundary over sets whose closure is not a union of blocks  ==  kappa == |C| - 1,
  (d) the number of sets by boundary size (small boundaries),
  (e) the minimal two-sided boundary of a set that is not a union of blocks.
"""
import itertools


class Grp:
    def __init__(self, mods):
        self.mods = mods
        self.elts = list(itertools.product(*[range(m) for m in mods]))
        self.idx = {e: i for i, e in enumerate(self.elts)}
        self.n = len(self.elts)

    def add(self, i, j):
        a, b = self.elts[i], self.elts[j]
        return self.idx[tuple((x + y) % m for x, y, m in zip(a, b, self.mods))]

    def neg(self, i):
        a = self.elts[i]
        return self.idx[tuple((-x) % m for x, m in zip(a, self.mods))]

    def subgroups(self):
        subs = set()
        for k in range(0, 5):
            for gens in itertools.combinations(range(self.n), k):
                H = {0}
                frontier = [0]
                while frontier:
                    x = frontier.pop()
                    for g in gens:
                        y = self.add(x, g)
                        if y not in H:
                            H.add(y)
                            frontier.append(y)
                subs.add(frozenset(H))
        return subs


def translate_table(G, c):
    n = G.n
    tab = [0] * (1 << n)
    for m in range(1, 1 << n):
        low = (m & -m).bit_length() - 1
        tab[m] = tab[m & (m - 1)] | (1 << G.add(low, c))
    return tab


def analyse(name, G, C):
    n = G.n
    r = len(C)
    subs = G.subgroups()
    Cset = set(C)
    kappa = None
    for H in subs:
        if Cset <= H:
            continue
        cosets = {frozenset(G.add(c, h) for h in H) for c in C}
        v = (len(cosets) - 1) * len(H)
        kappa = v if kappa is None else min(kappa, v)
    # blocks = cosets of <C>
    gen = min((H for H in subs if Cset <= H), key=len)
    blockmask = []
    seen = set()
    for x in range(n):
        if x in seen:
            continue
        co = [G.add(x, h) for h in gen]
        seen.update(co)
        blockmask.append(sum(1 << y for y in co))
    tabs = [translate_table(G, c) for c in C]
    negtabs = [translate_table(G, G.neg(c)) for c in C]
    full = (1 << n) - 1

    def is_block_union(m):
        return all((m & b) in (0, b) for b in blockmask)

    okA = okB = True
    min_generic = None
    hist = {}
    two_sided = None
    for J in range(1, 1 << n):
        cl = 0
        for t in tabs:
            cl |= t[J]
        b = bin(cl).count("1") - bin(J).count("1")
        bu = is_block_union(cl)
        if (cl == J) != is_block_union(J):
            okA = False
        if kappa is not None and b < kappa and not bu:
            okB = False
        if not bu:
            min_generic = b if min_generic is None else min(min_generic, b)
        if b <= r:
            key = (b, bu)
            hist[key] = hist.get(key, 0) + 1
        if not is_block_union(J):
            # two-sided boundary: points of J with a window point outside J, plus the boundary
            comp = full & ~J
            out = 0
            for t in negtabs:
                out |= t[comp]
            inner = bin(J & out).count("1")
            ts = inner + b
            two_sided = ts if two_sided is None else min(two_sided, ts)
    print(f"{name}: r={r} blocks={len(blockmask)}x{len(gen)} kappa={kappa} (r-1={r - 1})  closed-iff-block-union: {okA}  small-boundary-implies-periodic: {okB}  min generic boundary: {min_generic}  min two-sided boundary (non block unions): {two_sided}")
    print("    sets by (boundary, closure is a union of blocks):", dict(sorted(hist.items())))


def main():
    Z16 = Grp((16,))
    for C in ([0, 1], [0, 1, 2], [0, 1, 2, 3], [0, 1, 2, 3, 4], [0, 1, 4], [0, 1, 2, 4, 8], [0, 1, 8], [0, 2, 8], [0, 4, 8], [0, 1, 3], [0, 1, 5]):
        analyse(f"Z/16 C={C}", Z16, [Z16.idx[(c,)] for c in C])
    F4 = Grp((2, 2, 2, 2))
    e = lambda *bits: F4.idx[tuple(1 if i in bits else 0 for i in range(4))]
    analyse("F_2^4 cube t'=4", F4, [e(), e(0), e(1), e(2), e(3)])
    analyse("F_2^4 block cube t'=3 (2 blocks)", F4, [e(), e(0), e(1), e(2)])
    analyse("F_2^4 block cube t'=2 (4 blocks)", F4, [e(), e(0), e(1)])
    M = Grp((2, 2, 4))
    analyse("F_2^2 x Z/4: block cube t'=2 plus stride 'next block'", M, [M.idx[(0, 0, 0)], M.idx[(1, 0, 0)], M.idx[(0, 1, 0)], M.idx[(0, 0, 1)]])
    M2 = Grp((2, 8))
    analyse("F_2 x Z/8: block cube t'=1 plus stride 'next block'", M2, [M2.idx[(0, 0)], M2.idx[(1, 0)], M2.idx[(0, 1)]])


if __name__ == "__main__":
    main()
