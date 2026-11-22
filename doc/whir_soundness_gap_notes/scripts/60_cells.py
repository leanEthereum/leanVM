#!/usr/bin/env python3
"""Note 60, Section 3.5 to 3.7: explicit configurations in the N-cube, counted exactly.

Vertices are grouped by their vector of block weights (the coordinates are split into blocks),
so a set that depends only on block weights is counted with products of binomials.

 cells  : fibres = Voronoi cells of p codewords of the [7,3] simplex code (blocks = columns
          repeated), p = 2..8.  Reports m = largest fibre, I = total interior, (I - m)/n.
 keyhole: three sets Z_i = B + F_i, B = Hamming ball {weight <= r}, F_i = the part of the rest
          where block i is the heaviest of three blocks.  Reports sum |int Z_i| - |int B|.
 packing: radius-1 balls around a shortened Hamming code (analytic).

 python3 60_cells.py [N ...]
"""
import itertools, sys
from math import comb


def blocks(N, B):
    q, r = divmod(N, B)
    return [q + 1] * r + [q] * (B - r)


def count(sizes, label):
    """label: function weight-vector -> hashable label (None = unassigned).
    Returns (size by label, interior by label)."""
    ranges = [range(s + 1) for s in sizes]
    lab = {w: label(w) for w in itertools.product(*ranges)}
    size, inner = {}, {}
    for w, l in lab.items():
        mult = 1
        for s, x in zip(sizes, w):
            mult *= comb(s, x)
        if l is None:
            continue
        size[l] = size.get(l, 0) + mult
        ok = True
        for i, s in enumerate(sizes):
            if w[i] < s and lab[w[:i] + (w[i] + 1,) + w[i + 1:]] != l:
                ok = False
                break
            if w[i] > 0 and lab[w[:i] + (w[i] - 1,) + w[i + 1:]] != l:
                ok = False
                break
        if ok:
            inner[l] = inner.get(l, 0) + mult
    return size, inner


def simplex_cells(N, p, dim=3, R=None):
    """Voronoi cells of the first p words of the [2^dim - 1, dim] simplex code (one block per
    column); with R: only the points at distance <= R of their nearest word are assigned."""
    nb = 2 ** dim - 1
    sizes = blocks(N, nb)
    cols = list(range(1, nb + 1))
    words = [[bin(u & a).count("1") & 1 for a in cols] for u in range(nb + 1)][:p]

    def label(w):
        best, arg = None, None
        for t, c in enumerate(words):
            d = sum((s - x) if bit else x for s, x, bit in zip(sizes, w, c))
            if best is None or d < best:
                best, arg = d, t
        return arg if (R is None or best <= R) else None

    return count(sizes, label)


def keyhole(N, r):
    sizes = blocks(N, 3)

    def sector(w):
        return max(range(3), key=lambda i: (w[i] / sizes[i], -i))

    res = []
    inB = lambda w: sum(w) <= r
    sB, iB = count(sizes, lambda w: 0 if inB(w) else None)
    total = -iB.get(0, 0)
    zmax = 0
    for i in range(3):
        s, inn = count(sizes, lambda w: 0 if (inB(w) or sector(w) == i) else None)
        total += inn.get(0, 0)
        zmax = max(zmax, s[0])
    return sB[0], iB.get(0, 0), zmax, total


def main():
    Ns = [int(a) for a in sys.argv[1:]] or [16, 20, 25, 28]
    for N in Ns:
        n = 2 ** N
        print(f"N={N}")
        for p in range(2, 9):
            size, inner = simplex_cells(N, p)
            m = max(size.values())
            I = sum(inner.values())
            print(f"  simplex cells p={p}: m/n={m / n:.4f}  I/n={I / n:.4f}  (I-m)/n={(I - m) / n:+.4f}   (m+|B'|)/n={(m + n - I) / n:.4f}")
        for p in (3, 4):
            size, inner = simplex_cells(N, p, dim=2)
            m = max(size.values()); I = sum(inner.values())
            print(f"  3-block cells p={p}: m/n={m / n:.4f}  I/n={I / n:.4f}  (I-m)/n={(I - m) / n:+.4f}")
        for rate in (4, 8, 16):
            for R in range(N // 2, 0, -1):
                size, inner = simplex_cells(N, 8, R=R)
                m = max(size.values())
                if m < n // rate:
                    I = sum(inner.values())
                    print(f"  8 simplex cells truncated at radius {R} (largest with m < n/{rate}): m/n={m / n:.4f}  I/n={I / n:.4f}  (I-m)/n={(I - m) / n:+.4f}  against k/n={1 / rate:.4f}: margin {1 / rate - (I - m) / n:+.4f}")
                    break
        # two antipodal balls of radius r: fibres B(0,r), B(1,r), 2r+1 <= N
        best = None
        for r in range(1, (N - 1) // 2 + 1):
            m = sum(comb(N, i) for i in range(r + 1))
            I = 2 * sum(comb(N, i) for i in range(r))
            if m < n // 2:
                v = (I - m) / n
                if best is None or v > best[0]:
                    best = (v, r, m / n, I / n)
        print(f"  two antipodal balls, best radius {best[1]}: m/n={best[2]:.4f} I/n={best[3]:.4f} (I-m)/n={best[0]:+.4f}")
        ham = 2 ** (N - (N + 1).bit_length() + (0 if (N + 1) & N else -1) + 0)
        # shortened Hamming code of length N: 2^(N - ceil(log2(N+1))) codewords
        import math
        ham = 2 ** (N - math.ceil(math.log2(N + 1)))
        print(f"  radius-1 balls around a shortened Hamming code: m={N + 1}, I/n={ham / n:.5f} (= 2^-{math.ceil(math.log2(N + 1))}); exceeds k+m at rates below {ham / n:.5f}")
        bestk = None
        for r in range(N // 2 - 5, N // 2 + 1):
            b, ib, zmax, tot = keyhole(N, r)
            if zmax < n // 2:
                if bestk is None or tot > bestk[0]:
                    bestk = (tot, r, b, ib, zmax)
        if bestk:
            tot, r, b, ib, zmax = bestk
            print(f"  keyhole (rate 1/2, common zero set B = ball of radius {r}): |B|/n={b / n:.4f} |int B|/n={ib / n:.4f} max|Z_i|/n={zmax / n:.4f}  (sum|int Z_i| - |int B|)/n={tot / n:.4f}  against 2k/n = 1")


if __name__ == "__main__":
    main()
