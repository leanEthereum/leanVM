# Referee 75: the Kraft sum of note 73's prefix code, by enumeration of the labels themselves (sets and sides, not sizes) on tiny trees,
# for the note's multipliers and for arbitrary positive multipliers lambda_i (the equality should not depend on the recursion).
import itertools, math, random

def kraft(r, J, v, j, lam_top, lams):
    """sum over prefix labels pi_j = (Z_J; (D_i, c_i), i = J..j) of 2^-w(pi_j); lams[i] = lambda_i, c_i = log2(1 + 2^(1 - lambda_i))"""
    nJ = 2 ** (J + r); total = 0.0
    def rec(i, Zsize, npos, acc):
        nonlocal total
        if i > j: total += 2.0 ** -acc; return
        m = npos - Zsize; ci = math.log2(1 + 2 ** (1 - lams[i]))
        # enumerate D as a subset of the m available nodes with sides: every (D, c) explicitly
        for D in range(1 << m):
            d = bin(D).count("1")
            for sides in range(1 << d):
                rec(i + 1, 2 * Zsize + d, 2 * npos, acc + lams[i] * d + m * ci)
    for Z in range(1 << nJ):
        z = bin(Z).count("1")
        rec(J, z, nJ, lam_top * z + nJ * math.log2(1 + 2 ** -lam_top))
    return total

random.seed(7)
for (r, J, v) in ((1, 0, 2), (1, 1, 3), (2, 0, 2), (1, 0, 3)):
    lam = 1.3
    C = {v: 0.0}
    for i in range(v - 1, J - 1, -1): C[i] = C[i + 1] + math.log2(1 + 2 ** (1 - lam - C[i + 1] / 2))
    note = {i: lam + C[i + 1] / 2 for i in range(J, v)}
    arb = {i: random.uniform(0.3, 3.0) for i in range(J, v)}
    for j in range(J, v):
        if (2 ** (j + r)) > 8: continue   # keep the enumeration small
        print(f"r={r} J={J} v={v} truncation j={j}: Kraft sum with the note's multipliers {kraft(r, J, v, j, 2 * lam + C[J], note):.12f}, with arbitrary multipliers {kraft(r, J, v, j, random.uniform(0.5, 4), arb):.12f}")
