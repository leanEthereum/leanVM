"""Note 64, item 4b: the purely combinatorial relaxation of the free t-wise sum in the N-cube, block-symmetric sets.

Relaxation: every point y carries a partition pi_y of {0..t-1} (which of the t polynomials coincide at y); the only
constraint kept from Reed-Solomon is that each pair coincides on at most k - 1 points. Score = sum over x of
(largest class of the meet of pi_y over the window of x) - 1, to compare with (t - 1) k. Any proof of the free part of
(H_t) that uses only pairwise zero-set sizes and isoperimetry must beat this relaxation.

Sets are unions of cells: the coordinates are split into blocks and a cell is the vector of block weights.
Usage: python3 64_item4b_relax.py N blocks t rate_log iters seed     e.g. 25 12,13 4 1 300000 1
"""
import sys, random, math
from math import comb
from itertools import product

N, blocks, t, rlog, iters, seed = int(sys.argv[1]), [int(b) for b in sys.argv[2].split(",")], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
assert sum(blocks) == N
rng = random.Random(seed)
n = 1 << N
cap = (n >> rlog) - 1
cells = list(product(*[range(b + 1) for b in blocks]))
idx = {c: i for i, c in enumerate(cells)}
w = [math.prod(comb(b, a) for b, a in zip(blocks, c)) for c in cells]
nbr = []
for c in cells:
    l = []
    for j in range(len(blocks)):
        for d in (-1, 1):
            e = list(c); e[j] += d
            if 0 <= e[j] <= blocks[j]:
                l.append(idx[tuple(e)])
    nbr.append(l)
pairs = [(i, j) for i in range(t) for j in range(i + 1, t)]
pbit = {p: 1 << b for b, p in enumerate(pairs)}


def partitions(m):
    if m == 0:
        yield []
        return
    for p in partitions(m - 1):
        for cl in range(max(p, default=-1) + 2):
            yield p + [cl]


masks = sorted({sum(pbit[(i, j)] for i, j in pairs if p[i] == p[j]) for p in partitions(t)})
largest = {}
for mk in range(1 << len(pairs)):
    largest[mk] = max(1 + sum(1 for (a, b) in pairs if (a == i or b == i) and mk & pbit[(a, b)]) for i in range(t))
ALL = (1 << len(pairs)) - 1


def cell_score(lab, c):
    mk = lab[c]
    for d in nbr[c]:
        mk &= lab[d]
    return w[c] * (largest[mk] - 1)


def total(lab):
    return sum(cell_score(lab, c) for c in range(len(cells)))


def masses(lab):
    M = [0] * len(pairs)
    for c, mk in enumerate(lab):
        for b in range(len(pairs)):
            if mk >> b & 1:
                M[b] += w[c]
    return M


def repair(lab):
    M = masses(lab)
    for c in sorted(range(len(cells)), key=lambda c: w[c]):
        if all(m <= cap for m in M):
            break
        if any(lab[c] >> b & 1 and M[b] > cap for b in range(len(pairs))):
            for b in range(len(pairs)):
                if lab[c] >> b & 1:
                    M[b] -= w[c]
            lab[c] = 0
    return lab


def anneal(lab, T0, T1):
    M, cur = masses(lab), total(lab)
    best, bestlab = cur, lab[:]
    for it in range(iters):
        T = T0 * (T1 / T0) ** (it / iters) * n
        c = rng.randrange(len(cells))
        new = lab[rng.choice(nbr[c])] if rng.random() < 0.6 else rng.choice(masks)
        old = lab[c]
        if new == old:
            continue
        ok = True
        for b in range(len(pairs)):
            if new >> b & 1 and not old >> b & 1 and M[b] + w[c] > cap:
                ok = False
                break
        if not ok:
            continue
        aff = [c] + nbr[c]
        before = sum(cell_score(lab, a) for a in aff)
        lab[c] = new
        delta = sum(cell_score(lab, a) for a in aff) - before
        if delta >= 0 or rng.random() < math.exp(delta / T):
            cur += delta
            for b in range(len(pairs)):
                M[b] += w[c] * ((new >> b & 1) - (old >> b & 1))
            if cur > best:
                best, bestlab = cur, lab[:]
        else:
            lab[c] = old
    return best, bestlab


def seed_ball():       # all t coincide on the ball of radius r (largest fitting), nothing elsewhere
    r = max(r for r in range(N + 1) if sum(comb(N, i) for i in range(r + 1)) <= cap + 1)
    return repair([ALL if sum(c) <= r else 0 for c in cells])


def seed_quadrants():  # region e (given by two half-cubes) : all but polynomial e coincide; needs 2 blocks, t >= 4
    lab = []
    for c in cells:
        e = 2 * (sum(c) <= N // 2) + (c[1] <= c[0] + (blocks[1] - blocks[0]) // 2)
        lab.append(sum(pbit[(i, j)] for i, j in pairs if i != e and j != e and i < 4 and j < 4))
    return repair(lab)


seeds = {"empty": [0] * len(cells), "common ball": seed_ball()}
if t >= 4 and len(blocks) == 2:
    seeds["quadrants"] = seed_quadrants()
target = (t - 1) * (n >> rlog)
print(f"N={N} blocks={blocks} t={t} rate=2^-{rlog}: cells {len(cells)}, partitions {len(masks)}, (t-1)k/n = {target/n:.4f}")
for name, lab in seeds.items():
    s0 = total(lab)
    best, bl = anneal(lab[:], 0.004, 0.00005)
    M = masses(bl)
    print(f"   seed {name}: seed score/(t-1)k = {s0/target:.4f}; after annealing {best/target:.4f}"
          f" (score/n = {best/n:.4f}); max pair mass/k = {max(M)/(cap+1):.4f}; labels used {len(set(bl))}")
