#!/usr/bin/env python3
"""Note 60, Section 2: index-stride windows x -> x + 2^s (integer addition mod 2^N).

 (1) check (enumeration, N = 12) of the formula for the fraction of positions whose whole
     window stays in the coset of a coordinate subspace U (coordinates outside E):
        stay(S, E) = prod over excluded e in E that are the first excluded coordinate
                     at or above some stride of (1 - 2^-(e - s)), s the largest such stride.
 (2) N = 10: the best hyperplane (all 2^N - 1 of them) against the best coordinate hyperplane.
 (3) N = 25..28: I*(c) = max over coordinate subspaces of codimension c of stay, for evenly
     spread strides, with the mean verifier cost sum_j (s_j + 2) (cube window: N(N+1)/2).
 (4) interior loss of the aligned periodic half sets {x mod 2^(s'+1) < 2^s'}: an upper bound
     on the vertex-isoperimetric constant beta(1/2) of the circulant.
"""
import itertools, random
from math import comb


def stay_formula(N, S, E):
    E = sorted(E)
    first = {}
    for s in S:
        e = next((e for e in E if e >= s), None)
        if e is not None:
            first[e] = max(first.get(e, -1), s)
    p = 1.0
    for e, s in first.items():
        p *= 1 - 2.0 ** (-(e - s))
    return p


def stay_enum(N, S, E):
    n = 1 << N
    mask = sum(1 << e for e in E)
    cnt = 0
    for x in range(n):
        if all(((x + (1 << s)) % n ^ x) & mask == 0 for s in S):
            cnt += 1
    return cnt / n


def spread(N, d):
    return sorted({(j * N) // d for j in range(d)})


def best_coordinate(N, S, c):
    best = (0.0, None)
    for E in itertools.combinations(range(N), c):
        v = stay_formula(N, S, E)
        if v > best[0]:
            best = (v, E)
    return best


def main():
    random.seed(60)
    N = 12
    ok = True
    for _ in range(40):
        S = sorted(random.sample(range(N), random.randint(1, 5)))
        E = sorted(random.sample(range(N), random.randint(1, 4)))
        a, b = stay_formula(N, S, E), stay_enum(N, S, E)
        if abs(a - b) > 1e-12:
            ok = False
            print("MISMATCH", S, E, a, b)
    print(f"(1) formula against enumeration, N=12, 40 random (strides, excluded sets): {ok}")

    N = 10
    n = 1 << N
    for S in ([0, 3, 6], [0, 2, 4, 6, 8], [0, 5]):
        deltas = [[((x + (1 << s)) % n) ^ x for s in S] for x in range(n)]
        best = (0, 0)
        for a in range(1, n):
            cnt = sum(1 for dl in deltas if all(bin(a & d).count("1") % 2 == 0 for d in dl))
            if cnt > best[0]:
                best = (cnt, a)
        bc = best_coordinate(N, S, 1)
        print(f"(2) N=10 strides {S}: best hyperplane a={best[1]:010b} stays {best[0] / n:.4f}; best coordinate hyperplane {bc[0]:.4f} (excluded {bc[1]})")

    for N in (25, 28):
        print(f"(3) N={N}: I*(c), c = 1..6, for d evenly spread strides; mean verifier cost sum (s_j + 2), cube window {N * (N + 1) // 2}")
        for d in (3, 5, 8, 12, N):
            S = spread(N, d)
            row = []
            for c in range(1, 7):
                row.append(f"{best_coordinate(N, S, c)[0]:.3f}")
            cost = sum(s + 2 for s in S)
            gaps = [b - a for a, b in zip(S, S[1:])] + [N - S[-1]]
            # (4) aligned periodic half sets: period 2^(s'+1) with s' just below a stride or the top
            loss = min(2.0 ** (1 - g) for g in gaps)
            print(f"    d={d:2d} strides {S if d <= 12 else 'all'}: I* = {' '.join(row)}; cost {cost}; (4) a half set with interior loss {loss:.4f}")


if __name__ == "__main__":
    main()
