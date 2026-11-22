#!/usr/bin/env python3
"""55_gap.py: referee tests of note 53, Proposition 6.3 (words of Gamma_inf(g) in the weight gap of RM(2, N) on
small fields). Own code (55_lib.py); every word produced is verified from the definition: all power sums
p_0, .., p_g are recomputed over the field, and the weight and the Boolean degree are computed from the truth table.

Toy size N = 10, n = 1024, g in [3n/16 - 1, 7n/32 - 2] = [191, 222], fields GF(2^12), GF(2^16).
A. The odd k <= g of binary weight >= N - 3 are exactly 2^(N-3) - 1 and 2^(N-2) - 1 - 2^(N-4) (brute force), for the
   toy g and for the real sizes (closed form); the range of g for which this holds.
B. The space X of quadratic forms Q on x_1..x_{N-1} with p_k(x_0 Q) = 0 for the two k: dimension against
   C(N-1, 2) - 2m.
C. Two-half words f = x_0 Q + (quadratic), Q in X of rank 2h': for a quadratic q_A of rank 4 with rank(q_A + Q) = 2b
   the halves are made of weights n/4 - n/16 and n/4 - n/2^(b+2); b = 3 gives 13n/32, b = 4 gives 27n/64.
   (Note 53 takes q_A in the radical of Q, which gives b = h' + 2; any q_A with the two ranks works.)
D. Four-quarter words f = x_0 Q_0 + x_1 Q_1 + x_0 x_1 l + (quadratic) with quarter ranks (4, 4, 6, 8): weight
   53n/128 = 424, inside the interval [2(A - Delta), 2A(n - A)/n) scaled to n = 1024.
E. The linear-algebra facts used at N = 25, m = 64: the counts, and a brute-force check (v = 4, 5) that a linear
   space of alternating forms of rank <= 2 on F_2^v has dimension at most max(v - 1, 3).
Run: python3 55_gap.py
"""
import importlib
import random
import sys
from math import comb

sys.path.insert(0, sys.path[0] or ".")
L = importlib.import_module("55_lib")


def fwht(w):
    w = list(w)
    h = 1
    n = len(w)
    while h < n:
        for i in range(0, n, 2 * h):
            for j in range(i, i + h):
                a, b = w[j], w[j + h]
                w[j], w[j + h] = a + b, a - b
        h *= 2
    return w


def best_affine(f):
    """f: list of 0/1 on F_2^r. Returns (weight, g) with g = f + (best affine function), of smallest weight."""
    n = len(f)
    W = fwht([1 - 2 * v for v in f])
    best = max(range(n), key=lambda u: abs(W[u]))
    c = 1 if W[best] < 0 else 0
    g = [f[x] ^ (bin(x & best).count("1") & 1) ^ c for x in range(n)]
    return sum(g), g


def quad_eval(r, rows):
    """truth table on F_2^r of sum_{i<j} B_ij x_i x_j, rows[i] = bitmask of the j > i with B_ij = 1."""
    out = []
    for x in range(1 << r):
        v = 0
        for i in range(r):
            if (x >> i) & 1:
                v ^= bin(rows[i] & x).count("1") & 1
        out.append(v)
    return out


def alt_rank(r, rows):
    """rank of the alternating form with upper triangle rows."""
    full = [0] * r
    for i in range(r):
        for j in range(i + 1, r):
            if (rows[i] >> j) & 1:
                full[i] |= 1 << j
                full[j] |= 1 << i
    return L.f2_rank(full)


def rand_alt_of_rank(rnd, r, rank):
    """upper triangle of a random alternating form of the given rank: sum of rank/2 products u ^ v."""
    while True:
        up = [0] * r
        for _ in range(rank // 2):
            u, v = rnd.randrange(1, 1 << r), rnd.randrange(1, 1 << r)
            for i in range(r):
                for j in range(i + 1, r):
                    if (((u >> i) & (v >> j)) ^ ((u >> j) & (v >> i))) & 1:
                        up[i] ^= 1 << j
        if alt_rank(r, up) == rank:
            return up


def xor_rows(a, b):
    return [x ^ y for x, y in zip(a, b)]


def verify_word(F, alpha, f, g, N):
    """f: truth table (list) on F_2^N. Returns (weight, degree, first k with p_k != 0)."""
    pts = [alpha[a] for a in range(1 << N) if f[a]]
    first = None
    pw = [1] * len(pts)
    for k in range(0, 2 * g + 4):
        s = 0
        if k == 0:
            s = len(pts) & 1
        else:
            pw = [F.mul(v, a) for v, a in zip(pw, pts)]
            for v in pw:
                s ^= v
        if s:
            first = k
            break
    mask = 0
    for a, v in enumerate(f):
        if v:
            mask |= 1 << a
    return len(pts), L.boolean_degree(N, mask), first


def part_A():
    print("A. odd k <= g with binary weight >= N - 3")
    N = 10
    n = 1 << N
    k1, k2, k3 = (1 << (N - 3)) - 1, (1 << (N - 2)) - 1 - (1 << (N - 4)), (1 << (N - 2)) - 1 - (1 << (N - 5))
    lo = hi = None
    for g in range(1, n // 4):
        ks = [k for k in range(1, g + 1, 2) if bin(k).count("1") >= N - 3]
        if ks == [k1, k2]:
            lo = g if lo is None else lo
            hi = g
    print(f"   N = 10: exactly [{k1}, {k2}] for g in [{lo}, {hi}] = [3n/16 - 1, 7n/32 - 2] "
          f"({lo == 3 * n // 16 - 1 and hi == 7 * n // 32 - 2}); the third one is {k3} = 7n/32 - 1")
    for N in (25, 28):
        n = 1 << N
        glo = -(-1875 * n // 10000)
        ghi = (2187 * n - 1) // 10000
        print(f"   N = {N}: the note's range g/n in [0.1875, 0.2187) is g in [{glo}, {ghi}]; "
              f"3n/16 - 1 = {3 * n // 16 - 1} <= {glo}: {3 * n // 16 - 1 <= glo}; {ghi} <= 7n/32 - 2 = "
              f"{7 * n // 32 - 2}: {ghi <= 7 * n // 32 - 2}")


def setup(F, N, basis):
    alpha = F.span(basis)                      # alpha[a], bit i of a <-> basis[i]
    return alpha


def functional_rows(F, alpha, N, monos, ks):
    """for each monomial (a bitmask I), the packed values sum_{a >= I} alpha(a)^k, k in ks."""
    m = F.m
    pws = [[F.pow(alpha[a], k) for a in range(1 << N)] for k in ks]
    rows = []
    for I in monos:
        v = 0
        for pk in pws:
            s = 0
            for a in range(1 << N):
                if a & I == I:
                    s ^= pk[a]
            v = (v << m) | s
        rows.append(v)
    return rows


def part_BCD(F, N, basis, name, rnd):
    n = 1 << N
    m = F.m
    alpha = setup(F, N, basis)
    k1, k2 = (1 << (N - 3)) - 1, (1 << (N - 2)) - 1 - (1 << (N - 4))
    g = 211
    r = N - 1
    # B. X: quadratic forms in x_1..x_{N-1}; monomial x_0 x_i x_j
    pairs = [(i, j) for i in range(1, N) for j in range(i + 1, N)]
    monos = [1 | (1 << i) | (1 << j) for (i, j) in pairs]
    rows = functional_rows(F, alpha, N, monos, (k1, k2))
    piv, ker = L.f2_echelon(rows)
    print(f"B. {name}: dim X = {len(ker)}; C(N-1,2) - 2m = {comb(N - 1, 2) - 2 * m}")
    if not ker:
        return True
    ok = True

    def form_of(comb_mask):
        up = [0] * r
        for t, (i, j) in enumerate(pairs):
            if (comb_mask >> t) & 1:
                up[i - 1] |= 1 << (j - 1)
        return up
    # C. two-half words
    done = {}
    ranks_seen = {}
    for trial in range(400):
        cm = 0
        while cm == 0:
            cm = 0
            for kv in ker:
                if rnd.random() < 0.5:
                    cm ^= kv
        Q = form_of(cm)
        hq = alt_rank(r, Q)
        ranks_seen[hq] = ranks_seen.get(hq, 0) + 1
        qA = rand_alt_of_rank(rnd, r, 4)
        rb = alt_rank(r, xor_rows(Q, qA))
        if rb not in (6, 8) or rb in done:
            continue
        fA = quad_eval(r, qA)
        fB = quad_eval(r, xor_rows(Q, qA))
        wA, gA = best_affine(fA)
        wB, gB = best_affine(fB)
        f = [0] * n
        for a in range(n):
            f[a] = gB[a >> 1] if a & 1 else gA[a >> 1]
        wt, deg, first = verify_word(F, alpha, f, g, N)
        b = rb // 2
        target = n // 2 - n // 16 - (n >> (b + 2))
        good = wt == target and deg == 3 and first is not None and first > g
        ok &= good
        done[rb] = (hq, wt, deg, first, good)
        if len(done) == 2:
            break
    print(f"C. {name}: ranks of random elements of X: {dict(sorted(ranks_seen.items()))}")
    for rb, (hq, wt, deg, first, good) in sorted(done.items()):
        print(f"   rank Q = {hq}, rank q_A = 4, rank(q_A + Q) = {rb}: weight {wt} = {wt * 128 // n}n/128, Boolean degree {deg}, "
              f"p_k = 0 for all k < {first} (g = {g}; needs > {g}): {good}; in (3n/8, 7n/16) = ({3 * n // 8}, {7 * n // 16}): "
              f"{3 * n // 8 < wt < 7 * n // 16}")
    ok &= len(done) == 2
    # D. four-quarter words: monomials x_0 x_i x_j, x_1 x_i x_j (2 <= i < j), x_0 x_1 x_j
    r2 = N - 2
    pr2 = [(i, j) for i in range(2, N) for j in range(i + 1, N)]
    monos = [1 | (1 << i) | (1 << j) for (i, j) in pr2] + [2 | (1 << i) | (1 << j) for (i, j) in pr2] + \
            [3 | (1 << j) for j in range(2, N)]
    rows = functional_rows(F, alpha, N, monos, (k1, k2))
    piv, ker2 = L.f2_echelon(rows)
    np2 = len(pr2)
    found = None
    tries = 0
    while found is None and tries < 60000:
        tries += 1
        if tries % 200 == 1:
            cm = 0
            for kv in ker2:
                if rnd.random() < 0.5:
                    cm ^= kv
            Q0, Q1 = [0] * r2, [0] * r2
            for t, (i, j) in enumerate(pr2):
                if (cm >> t) & 1:
                    Q0[i - 2] |= 1 << (j - 2)
                if (cm >> (np2 + t)) & 1:
                    Q1[i - 2] |= 1 << (j - 2)
            lin = (cm >> (2 * np2))                    # bit (j - 2): coefficient of x_0 x_1 x_j
            if alt_rank(r2, xor_rows(Q0, Q1)) < 6:
                continue
        q = rand_alt_of_rank(rnd, r2, 4)
        ra, rb_, rc = alt_rank(r2, xor_rows(q, Q0)), alt_rank(r2, xor_rows(q, Q1)), \
            alt_rank(r2, xor_rows(q, xor_rows(Q0, Q1)))
        if rc == 8 and sorted((ra, rb_)) == [4, 6]:
            found = (q, Q0, Q1, lin)
    if found is None:
        print(f"D. {name}: no quarter pattern (4, 4, 6, 8) found in {tries} tries")
        return False
    q, Q0, Q1, lin = found
    nq = 1 << r2
    t00 = quad_eval(r2, q)
    t10 = quad_eval(r2, xor_rows(q, Q0))
    t01 = quad_eval(r2, xor_rows(q, Q1))
    t11 = quad_eval(r2, xor_rows(q, xor_rows(Q0, Q1)))
    # affine corrections: free on quarters 00, 10, 01; on 11 the linear part is forced (A00 + A10 + A01 + lin), the
    # constant is free. The quarter 11 has rank 8 (bent on F_2^8), so every linear part gives 128 +- 8.
    W = {}
    lins = {}
    for key, t in (("00", t00), ("10", t10), ("01", t01)):
        Wt = fwht([1 - 2 * v for v in t])
        u = max(range(nq), key=lambda z: abs(Wt[z]))
        lins[key] = (u, 1 if Wt[u] < 0 else 0)
    u11 = lins["00"][0] ^ lins["10"][0] ^ lins["01"][0] ^ lin
    Wt = fwht([1 - 2 * v for v in t11])
    c11 = 1 if Wt[u11] < 0 else 0
    lins["11"] = (u11, c11)
    f = [0] * n
    tabs = {"00": t00, "10": t10, "01": t01, "11": t11}
    for a in range(n):
        key = f"{a & 1}{(a >> 1) & 1}"
        x = a >> 2
        u, c = lins[key]
        f[a] = tabs[key][x] ^ (bin(x & u).count("1") & 1) ^ c
    wt, deg, first = verify_word(F, alpha, f, g, N)
    A = -(-7065 * n // 10000)
    lo_w, hi_w = 2 * (A - n // 2), 2 * A * (n - A) / n
    good = deg == 3 and first is not None and first > g
    print(f"D. {name}: quarter ranks (4, 4, 6, 8) found after {tries} tries: weight {wt} (53n/128 = {53 * n // 128}), "
          f"Boolean degree {deg}, p_k = 0 for all k < {first} (needs > {g}): {good}; the interval "
          f"[2(A - n/2), 2A(n - A)/n) at n = 1024 is [{lo_w}, {hi_w:.1f}): inside: {lo_w <= wt < hi_w}")
    return ok and good and wt == 53 * n // 128


def max_rank2_space(v):
    """largest dimension of a linear space of alternating forms on F_2^v all of rank <= 2 (exhaustive)."""
    idx = [(i, j) for i in range(v) for j in range(i + 1, v)]

    def rank_of(code):
        rows = [0] * v
        for t, (i, j) in enumerate(idx):
            if (code >> t) & 1:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        return L.f2_rank(rows)
    low = [c for c in range(1, 1 << len(idx)) if rank_of(c) == 2]
    lowset = set(low)
    best = 0

    def grow(space, basis_max, dim):
        nonlocal best
        best = max(best, dim)
        for c in low:
            if c <= basis_max or c in space:
                continue
            if all((c ^ s) in lowset for s in space if s):
                grow(space | {c ^ s for s in space}, c, dim + 1)
    grow({0}, 0, 0)
    return best, len(low)


def part_E():
    print("E. counts at real sizes (m = 64) and the rank lemma")
    for v in (4, 5):
        b, cnt = max_rank2_space(v)
        print(f"   v = {v}: {cnt} forms of rank 2; largest linear space of forms of rank <= 2 has dimension {b} "
              f"(max(v - 1, 3) = {max(v - 1, 3)})")
    for N in (25, 26, 27, 28):
        tot = comb(N - 1, 2)
        m = 64
        note = tot - 2 * m - (4 * (N - 1) - 10)
        mmax = (tot - (4 * (N - 1) - 10) - (N - 6) - 1) // 2
        iso = max(c for c in range(0, N) if tot - comb(N - 1 - c, 2) <= 2 * m)   # largest codim not enough
        print(f"   N = {N}: C(N-1,2) = {tot}; dim X >= {tot - 2 * m}; note's count {note} > N - 6 = {N - 6}: "
              f"{note > N - 6} (holds for m <= {mmax}); X != 0 as soon as m <= {(tot - 1) // 2}; forms vanishing on a "
              f"subspace of codimension c have dimension > 128 from c = {iso + 1} on, so X contains a nonzero form "
              f"of rank <= {2 * (iso + 1)}")


def main():
    rnd = random.Random(5506)
    part_A()
    ok = True
    F12 = L.GFs(12)
    ok &= part_BCD(F12, 10, F12.rand_basis(rnd, 10), "GF(2^12), random 10-dimensional subspace", rnd)
    F16 = L.GFs(16)
    ok &= part_BCD(F16, 10, [1 << i for i in range(10)], "GF(2^16), span(1, x, .., x^9)", rnd)
    part_E()
    print("ALL OK" if ok else "FAILURE")


if __name__ == "__main__":
    main()
