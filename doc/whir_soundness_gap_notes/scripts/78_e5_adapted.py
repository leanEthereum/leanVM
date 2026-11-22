#!/usr/bin/env python3
"""Note 78, experiment 5(b) for V1: product messages on unions of blocks ADAPTED to the partner maps.
By (P1) of the note, a lifted list A_l (x) B encoded by V1 has, at leaf x, the class C'(x) & C'(pi_1 x) & .. & C'(pi_d x),
where C'(x) is the class of the block of x in the top list, or all members if x is a zero of B. So the best V1 weight of a
lift at a scale of N blocks is a purely combinatorial maximum over top patterns (a class per block; two members share at most
k_up - 1 blocks, which every list of an MDS top code satisfies, and the top weight is at most L k_up - 1 + (L-1)(k_up/2 - 1),
the largest weight conjectured for a list of a tree code) and zero sets (2^i - 1 leaves anywhere):
    W = sum_x ( |C'(x) & C'(pi_1 x) & ...| - 1 )_+ .
This script computes that maximum (N = 4: every top pattern; N = 8: hill climbing; zeros on the best partner path, then
improved leaf by leaf) for random partner maps and compares it with the gS bound Lk - 1. It is an upper bound for lifts: the
top pattern is not required to carry a list of the top code. The plain tree code (no partner) gives the reference value.
usage: 78_e5_adapted.py v r d ptype nseeds   ptype = a (any) or x (cross tree)"""
import sys, random, itertools

def partner(n, k, r, ptype, rng):
    if ptype == 'a':
        p = list(range(n)); rng.shuffle(p); return p
    s = rng.randrange(1, 1 << r); p = [0] * n
    for t in range(1 << r):
        q = list(range(k)); rng.shuffle(q)
        for i in range(k): p[t * k + i] = (t ^ s) * k + q[i]
    return p
def weight(n, pis, cls, full):
    w = 0
    for x in range(n):
        c = cls[x]
        for p in pis: c &= cls[p[x]]
        b = bin(c).count('1')
        if b >= 2: w += b - 1
    return w
def with_zeros(n, lo, pis, blk, full, rng, tries=30):
    """block classes blk (per block) -> leaf classes; then 2^lo - 1 zeros: best path of the first partner map, then swaps"""
    bs = 1 << lo; cls = [blk[x >> lo] for x in range(n)]
    nz = bs - 1
    if nz == 0: return weight(n, pis, cls, full), cls
    best = None
    for _ in range(tries):
        x = rng.randrange(n); Z = []
        for _ in range(nz): Z.append(x); x = pis[0][x]
        c2 = list(cls)
        for z in Z: c2[z] = full
        w = weight(n, pis, c2, full)
        if best is None or w > best[0]: best = (w, c2, list(Z))
    w, c2, Z = best
    for _ in range(4 * nz):  # move one zero to a random leaf if the weight improves
        i = rng.randrange(len(Z)); y = rng.randrange(n)
        if c2[y] == full: continue
        old = Z[i]; c3 = list(c2); c3[old] = blk[old >> lo]; c3[y] = full
        w3 = weight(n, pis, c3, full)
        if w3 > w: w, c2 = w3, c3; Z[i] = y
    return w, c2
def ok_pairs(blk, members, kup):
    L = members - 1  # top weight at most the largest weight conjectured for a tree-code list (note 74, Conjecture 4.7)
    if sum(bin(c).count('1') - 1 for c in blk if c) > L * kup - 1 + (L - 1) * (kup // 2 - 1): return False
    for a in range(members):
        for b in range(a + 1, members):
            m = (1 << a) | (1 << b)
            if sum(1 for c in blk if c & m == m) > kup - 1: return False
    return True
def main():
    v, r, d, ptype, nseeds = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
    n, k = 1 << (v + r), 1 << v
    print(f"(k,n)=({k},{n}) V1 d={d} {ptype}: best V1 weight of an adapted lift, as 'weight (excess over the gS bound Lk-1)'; reference = plain tree code with the same top pattern search")
    for members in (3, 4, 5):
        L = members - 1; full = (1 << members) - 1
        classes = [0] + [c for c in range(1, 1 << members) if bin(c).count('1') >= 2]
        for N in (4, 8, 16):
            lo = v + r - (N.bit_length() - 1); kup = k >> lo
            if kup < 2: continue
            res = []
            for seed in range(nseeds):
                rng = random.Random(1000 * seed + 7 * members + N)
                pis = [partner(n, k, r, ptype, rng) for _ in range(d)]
                # T-tensor: counts of (block of x, blocks of partners)
                T = {}
                for x in range(n):
                    key = (x >> lo,) + tuple(p[x] >> lo for p in pis); T[key] = T.get(key, 0) + 1
                def tw(blk):
                    w = 0
                    for key, cnt in T.items():
                        c = full
                        for q in key: c &= blk[q]
                        b = bin(c).count('1')
                        if b >= 2: w += cnt * (b - 1)
                    return w
                cands = []
                if N == 4 and members <= 4:
                    for blk in itertools.product(classes, repeat=N):
                        if not ok_pairs(blk, members, kup): continue
                        cands.append((tw(blk), blk))
                else:
                    for rs in range(60):
                        blk = [rng.choice(classes) for _ in range(N)]
                        while not ok_pairs(blk, members, kup): blk[rng.randrange(N)] = 0
                        w = tw(blk)
                        for st in range(400):
                            b2 = list(blk); b2[rng.randrange(N)] = rng.choice(classes)
                            if not ok_pairs(b2, members, kup): continue
                            w2 = tw(b2)
                            if w2 >= w: blk, w = b2, w2
                        cands.append((w, tuple(blk)))
                cands.sort(reverse=True)
                best = (-1, None)
                for w0, blk in cands[:12]:
                    w, cls = with_zeros(n, lo, pis, blk, full, rng)
                    if w > best[0]: best = (w, blk)
                # reference: the same top pattern class, no partner: 2^lo * top weight + zeros in the emptiest block
                ref = max((1 << lo) * sum(bin(c).count('1') - 1 for c in blk if c) + ((1 << lo) - 1) * (members - min(max(bin(c).count('1'), 1) for c in blk)) for _, blk in cands[:200]) if d else 0
                res.append((best[0], best[1]))
            wbest, blkbest = max(res)
            gs = L * k - 1
            # reference for the plain tree code: maximize 2^lo w_up + zero gains over the same constraint class
            print(f"  members {members}, N={N} (blocks of {1 << lo}, k_up={kup}): V1 best over {nseeds} partner draws: {wbest} ({wbest - gs:+d}), per draw {[w for w, _ in res]}; gS bound {gs}; pattern {' '.join(''.join(str(i) for i in range(members) if (c >> i) & 1) or '.' for c in blkbest)}")
main()
