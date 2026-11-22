"""Note 82, Section 6: the two kinds of six-member atoms at k = 2, in odd characteristic (the C programs are characteristic 2).
Unknowns: m_1..m_5 in K^2 (m_0 = 0). A leaf with direction z and a group {a, b}: (m_a - m_b) . z = 0. Rank mod a prime."""
import random
P = (1 << 61) - 1
def rank(rows):
    M = [r[:] for r in rows]; rk = 0; nc = len(M[0])
    for c in range(nc):
        p = next((i for i in range(rk, len(M)) if M[i][c] % P), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]; inv = pow(M[rk][c], P - 2, P)
        for i in range(rk + 1, len(M)):
            if M[i][c] % P:
                f = M[i][c] * inv % P; M[i] = [(x - f * y) % P for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk
def system(leaves, seed):
    rnd = random.Random(seed); rows = []
    for groups in leaves:
        z = (1, rnd.randrange(P))
        for g in groups:
            for b in g[1:]:
                row = [0] * 10; a = g[0]
                if a: row[2 * (a - 1)] = z[0]; row[2 * (a - 1) + 1] = z[1]
                if b: row[2 * (b - 1)] = (row[2 * (b - 1)] - z[0]) % P; row[2 * (b - 1) + 1] = (row[2 * (b - 1) + 1] - z[1]) % P
                rows.append(row)
    return rows
pappus = [[(0, 1, 2)], [(0, 3), (1, 4)], [(2, 3), (1, 5)], [(0, 5), (2, 4)], [(3, 4, 5)]]
pentagon = [[(0, 1), (2, 3)], [(0, 2), (1, 4)], [(0, 3), (1, 5)], [(0, 4), (2, 5)], [(0, 5), (3, 4)]]
for name, pat in (("Pappus (two triangles, three double pairs)", pappus), ("five double pairs (point and pentagon)", pentagon)):
    print(name, ": ranks mod 2^61 - 1 at three draws:", [rank(system(pat, s)) for s in range(3)], "(characteristic 2: 9)")
