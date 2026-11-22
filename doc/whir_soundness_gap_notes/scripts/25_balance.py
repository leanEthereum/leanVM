"""Researcher 25. The balance condition for hyperplane families (note 25, Proposition 2.6 and Corollary 2.7).

A hyperplane family of type (A, B, chi) on M labels (rate 1/2, degree bound d on the 2M-point label domain,
d = M with slack one, d = M - 1 genuine) needs, with p = |A|, s = |B|, |S| = 2p + s:
  (i)  p + s <= M,
  (ii) 2p + |B cap H| <= d for every affine hyperplane H of F_2^r that does not contain B.
(ii) gives 4p + s <= 2d. If B lies in a hyperplane then |S| <= d + M/4 (at most 5/8). Otherwise
|hat b(phi)| <= beta = 2d - 4p - s for phi != 0, and Parseval gives beta^2 >= s (M - s) / (M - 1).

Part 1: the largest |S| allowed by (i) and the Parseval form of (ii), for M = 8 .. 1024.
Part 2: exhaustive check of (ii) itself for M = 8, 16 over all (A, B): no pair passes above 5/8.
Part 3: for M = 32, the (p, s) allowed by Parseval.

usage: python3 25_balance.py
"""
import itertools


def parseval_ok(M, d, p, s):
    beta = 2 * d - 4 * p - s
    if p + s > M or p < 0 or s < 0 or beta < 0 or 2 * p > d:
        return False
    if 4 * (2 * p + s) <= 4 * d + M:   # |S| <= d + M/4: B may be a flat inside a hyperplane, no further condition
        return True
    return beta * beta * (M - 1) >= s * (M - s)


print("Part 1: largest |S| on 2M labels allowed by (i) and Parseval, slack one (d = M) / genuine (d = M - 1)")
print("  M    max|S| slack  fraction   max|S| genuine  fraction   (5/8 is |S| = 1.25 M)")
for r in range(3, 11):
    M = 1 << r
    out = []
    for d in (M, M - 1):
        best = None
        for S in range(2 * M, M, -1):
            if any(parseval_ok(M, d, p, S - 2 * p) for p in range(0, M // 2 + 1) if S - 2 * p >= 0):
                best = S
                break
        out.append(best)
    print(f"  {M:4d}  {out[0]:6d}       {out[0] / (2 * M):.4f}     {out[1]:6d}        {out[1] / (2 * M):.4f}")

print()
print("Part 2: exhaustive check of (ii) for M = 8 and M = 16, slack one, |S| above 5/8")
for r in (3, 4):
    M = 1 << r
    d = M
    hyper = []
    for phi in range(1, M):
        H = sum(1 << x for x in range(M) if bin(x & phi).count("1") & 1)
        hyper.append(H)
        hyper.append(((1 << M) - 1) ^ H)
    for S in range(5 * M // 4 + 1, 2 * M):
        total = passing = 0
        for p in range(0, M // 2):
            s = S - 2 * p
            if s < 1 or p + s > M:
                continue
            # quick exit through Parseval when it already excludes the pair (p, s)
            for Aset in itertools.combinations(range(M), p):
                A = sum(1 << x for x in Aset)
                rest = [x for x in range(M) if not A >> x & 1]
                for Bset in itertools.combinations(rest, s):
                    B = sum(1 << x for x in Bset)
                    total += 1
                    inside = any(B & H == B for H in hyper)
                    if inside and 4 * S > 4 * d + M:
                        continue    # B in a hyperplane forces |S| <= d + M/4
                    if all(2 * p + bin(B & H).count("1") <= d for H in hyper if B & H != B):
                        passing += 1
        if total:
            print(f"  M = {M}, |S| = {S} ({S / (2 * M):.4f}): {total} pairs (A, B), {passing} pass the balance condition")

print()
print("Part 3: M = 32, pairs (p, s) allowed by (i) and Parseval, slack one")
M = 32
for S in range(41, 48):
    ok = [(p, S - 2 * p) for p in range(0, 16) if S - 2 * p >= 1 and parseval_ok(M, M, p, S - 2 * p)]
    print(f"  |S| = {S} ({S / 64:.4f}): {ok}")
