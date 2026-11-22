#!/usr/bin/env python3
"""Brute-force checks for note 07 (the DEEP fold lemma and the pole collapse of polynomial combiners).

Pure python, 4 processes, about 35 seconds. Toy setting: E = GF(2^5), D = span(1, x, x^2, x^3) (n = 16),
degree bound d = 3, agreement threshold A = 6. Since A^2 = 36 < n d = 48 this is beyond the Johnson radius, and a
random word has about 8 codewords in its list.

For a pair of words (f0, f1) the script computes, for all q^2 = 1024 challenges c = (alpha, beta), the full list
L(c) of polynomials of degree <= d agreeing with f1 + (alpha + beta x) f0 on at least A points. Then:

  T0  identities of Lemma 1 on random data (sum L_j = 0, sum L_j a_j = 0, a dependent triple lies on one rational pair);
  T1  dependency classes: maximal sets of triples (c, P) with P = G + (alpha + beta X) F for one rational pair
      (F, G). Checks Lemma 2: a class with a pole lies on one line of challenges; a polynomial class with more than
      max(q, C(n, 2)) members has deg F <= d - 1 and (F, G) agrees with (f0, f1) on at least A - 1 common points;
  T2  DEEP points: for s = 2 points the exact maximum over prover answers m of the number of challenges with an
      m-consistent list member, and for s = 3, 4 the refinement of the best cells;
  T3  the pole collapse for a combiner of degree r.

Usage: python3 07_deep_fold_check.py [word ...]   (words: random planted pole flats; default all)
"""
import itertools, random, sys, time
from collections import Counter, defaultdict
from multiprocessing import Pool

M, MOD = 5, 0b100101  # GF(32) = F_2[x]/(x^5 + x^2 + 1)
Q = 1 << M
N_DOM, DEG, AGREE = 16, 3, 6
DOM = list(range(N_DOM))


def _mul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a >> M:
            a ^= MOD
        b >>= 1
    return r


MUL = [[_mul(a, b) for b in range(Q)] for a in range(Q)]
INV = [0] * Q
for _a in range(1, Q):
    for _b in range(1, Q):
        if MUL[_a][_b] == 1:
            INV[_a] = _b


def poly_eval(coeffs, x):
    r = 0
    for c in reversed(coeffs):
        r = MUL[r][x] ^ c
    return r


def table(coeffs):
    return tuple(poly_eval(coeffs, x) for x in range(Q))


SUBSETS = list(itertools.combinations(DOM, DEG + 1))
# LAG[S][x][j] = row of MUL for the Lagrange coefficient of the j-th point of S at x, for every x in the field.
LAG = []
for S in SUBSETS:
    per_x = []
    for x in range(Q):
        rows = []
        for j, sj in enumerate(S):
            num, den = 1, 1
            for k, sk in enumerate(S):
                if k != j:
                    num = MUL[num][x ^ sk]
                    den = MUL[den][sj ^ sk]
            rows.append(MUL[MUL[num][INV[den]]])
        per_x.append(rows)
    LAG.append(per_x)


def word_list(w, agree=AGREE):
    """All polynomials of degree <= DEG agreeing with w (on DOM) on at least `agree` points, as value tables on E."""
    out = []
    for si, S in enumerate(SUBSETS):
        lag = LAG[si]
        w0, w1, w2, w3 = w[S[0]], w[S[1]], w[S[2]], w[S[3]]
        hits = []
        for x in DOM:
            r = lag[x]
            if r[0][w0] ^ r[1][w1] ^ r[2][w2] ^ r[3][w3] == w[x]:
                hits.append(x)
        if len(hits) >= agree and tuple(hits[: DEG + 1]) == S:
            out.append(tuple(r[0][w0] ^ r[1][w1] ^ r[2][w2] ^ r[3][w3] for r in lag))
    return out


def fold(f0, f1, a, b):
    return [f1[x] ^ MUL[a ^ MUL[b][x]][f0[x]] for x in DOM]


_WORDS = None


def _init(words):
    global _WORDS
    _WORDS = words


def _lists_for_alpha(a):
    f0, f1 = _WORDS
    return [(a, b, word_list(fold(f0, f1, a, b))) for b in range(Q)]


def all_lists(f0, f1):
    with Pool(4, initializer=_init, initargs=((f0, f1),)) as pool:
        rows = pool.map(_lists_for_alpha, range(Q))
    triples = []
    for row in rows:
        for a, b, lst in row:
            for P in lst:
                triples.append((a, b, P))
    return triples


# ---------------------------------------------------------------------------------------------------------------
# T0: the identities of Lemma 1


def t0(rng):
    for _ in range(2000):
        cs = [(rng.randrange(Q), rng.randrange(Q)) for _ in range(3)]
        if len(set(cs)) < 3:
            continue
        x = rng.randrange(Q)
        a = [c[0] ^ MUL[c[1]][x] for c in cs]
        L = [a[1] ^ a[2], a[0] ^ a[2], a[0] ^ a[1]]
        assert L[0] ^ L[1] ^ L[2] == 0
        assert MUL[L[0]][a[0]] ^ MUL[L[1]][a[1]] ^ MUL[L[2]][a[2]] == 0
        # a triple on one pair (F, G) is dependent, at every point
        F, G = rng.randrange(Q), rng.randrange(Q)
        P = [G ^ MUL[a[j]][F] for j in range(3)]
        assert MUL[L[0]][P[0]] ^ MUL[L[1]][P[1]] ^ MUL[L[2]][P[2]] == 0
    print("T0 ok: sum L_j = 0, sum L_j a_j = 0, triples on one pair have Q = 0")


# ---------------------------------------------------------------------------------------------------------------
# T1: dependency classes


def interp_value(points, x):
    """Value at x of the polynomial of degree < len(points) through the given (xi, yi)."""
    r = 0
    for j, (xj, yj) in enumerate(points):
        num, den = 1, 1
        for k, (xk, _) in enumerate(points):
            if k != j:
                num = MUL[num][x ^ xk]
                den = MUL[den][xj ^ xk]
        r ^= MUL[yj][MUL[num][INV[den]]]
    return r


def pair_from(t1, t2):
    """The rational F with P2 = P1 + (a2 - a1) F, as a value table on E ('inf' at a pole), or None if c1 = c2."""
    a1, b1, P1 = t1
    a2, b2, P2 = t2
    da, db = a1 ^ a2, b1 ^ b2
    if da == 0 and db == 0:
        return None
    root = MUL[da][INV[db]] if db else None  # zero of da + db X
    vals, hole = [], None
    for x in range(Q):
        l = da ^ MUL[db][x]
        num = P1[x] ^ P2[x]
        if l == 0:
            if num:
                vals.append("inf")
            else:
                vals.append(None)
                hole = x
        else:
            vals.append(MUL[num][INV[l]])
    if hole is not None:  # removable: F is a polynomial of degree <= DEG - 1, fill the hole
        pts = [(x, vals[x]) for x in range(Q) if x != hole][:DEG]
        vals[hole] = interp_value(pts, hole)
    return tuple(vals)


def fits(tbl, k):
    """Whether the value table on E is a polynomial of degree < k."""
    pts = [(x, tbl[x]) for x in range(k)]
    return all(interp_value(pts, x) == tbl[x] for x in range(Q))


def t1(name, f0, f1, triples, rng, anchors=500):
    n_tr = len(triples)
    idx = list(range(n_tr))
    rng.shuffle(idx)
    best_unexplained, best_explained, pole_ok, big_ok = 0, 0, True, True
    seen_classes = set()
    big = max(Q, N_DOM * (N_DOM - 1) // 2)
    for ai in idx[:anchors]:
        t_anchor = triples[ai]
        groups = defaultdict(list)
        for ti, t in enumerate(triples):
            if ti == ai:
                continue
            F = pair_from(t_anchor, t)
            if F is not None:
                groups[F].append(ti)
        for F, members in groups.items():
            size = len(members) + 1
            if size < 3:
                continue
            chal = {(triples[ti][0], triples[ti][1]) for ti in members} | {(t_anchor[0], t_anchor[1])}
            if "inf" in F:
                x0 = F.index("inf")
                lines = {a ^ MUL[b][x0] for a, b in chal}
                if len(lines) != 1 or len(chal) > Q:
                    pole_ok = False
                best_unexplained = max(best_unexplained, len(chal))
                continue
            a1, b1, P1 = t_anchor
            G = tuple(P1[x] ^ MUL[a1 ^ MUL[b1][x]][F[x]] for x in range(Q))
            Z = [x for x in DOM if F[x] == f0[x] and G[x] == f1[x]]
            key = (F, G)
            explained = len(Z) >= AGREE - 1 and fits(F, DEG) and fits(G, DEG + 1)
            if explained:
                best_explained = max(best_explained, len(chal))
            else:
                best_unexplained = max(best_unexplained, len(chal))
                if len(chal) > big:
                    big_ok = False
            seen_classes.add(key)
    print(
        f"T1 {name}: {n_tr} triples, {min(anchors, n_tr)} anchors; largest class explained by a pair of "
        f"List(f; A-1, d): {best_explained} challenges; largest other class: {best_unexplained} "
        f"(lemma: <= max(q, C(n,2)) = {big}); pole classes on one line: {pole_ok}; Lemma 2 holds: {big_ok and pole_ok}"
    )
    return best_explained, best_unexplained


# ---------------------------------------------------------------------------------------------------------------
# T2: DEEP points


def t2(name, triples, rng, trials=3):
    """Exact max over the answers at two DEEP points, then refinement of the best cells at a third and fourth."""
    for trial in range(trials):
        zs = rng.sample(range(N_DOM, Q), 4)  # outside D: in the real setting a point of D has probability n/q
        # per triple and point: a = alpha + beta zeta, p = P(zeta); m-consistent iff yG = p + a yF
        ap = [[(a ^ MUL[b][z], P[z]) for z in zs] for a, b, P in triples]
        count = [0] * (Q**4)
        for (a1, p1), (a2, p2), _, _ in ap:
            r1, r2 = MUL[a1], MUL[a2]
            base = [((y2 << M) | (p2 ^ r2[y2])) for y2 in range(Q)]
            for y1 in range(Q):
                hi = ((y1 << M) | (p1 ^ r1[y1])) << (2 * M)
                for lo in base:
                    count[hi | lo] += 1
        # count[] counts triples; convert the best cells to distinct challenges
        order = sorted(range(Q**4), key=count.__getitem__, reverse=True)[:40]
        top = set(order)
        members = defaultdict(list)
        for ti, ((a1, p1), (a2, p2), _, _) in enumerate(ap):
            r1, r2 = MUL[a1], MUL[a2]
            for y1 in range(Q):
                hi = ((y1 << M) | (p1 ^ r1[y1])) << (2 * M)
                for y2 in range(Q):
                    key = hi | (y2 << M) | (p2 ^ r2[y2])
                    if key in top:
                        members[key].append(ti)
        k2 = max(len({(triples[ti][0], triples[ti][1]) for ti in tis}) for tis in members.values())
        k3 = k4 = 0
        for tis in members.values():
            cells3 = defaultdict(set)
            for ti in tis:
                a3, p3 = ap[ti][2]
                for y in range(Q):
                    cells3[(y, p3 ^ MUL[a3][y])].add(ti)
            for sub in cells3.values():
                k3 = max(k3, len({(triples[ti][0], triples[ti][1]) for ti in sub}))
                if len(sub) < 3:
                    continue
                cells4 = defaultdict(set)
                for ti in sub:
                    a4, p4 = ap[ti][3]
                    for y in range(Q):
                        cells4[(y, p4 ^ MUL[a4][y])].add((triples[ti][0], triples[ti][1]))
                k4 = max(k4, max(len(v) for v in cells4.values()))
        print(
            f"T2 {name} trial {trial}: most challenges won by one answer vector: s=2: {k2} (exact), "
            f"s=3: {k3}, s=4: {k4} (within the 40 best 2-point cells); q = {Q}, q^2 = {Q * Q}"
        )


# ---------------------------------------------------------------------------------------------------------------
# T3: pole collapse for a combiner of degree r


def t3(rng):
    for r in (1, 2, 3):
        for _ in range(200):
            x0 = rng.randrange(N_DOM, Q)  # pole outside the domain
            alphas = [rng.randrange(Q) for _ in range(r + 1)]
            c_at = lambda x: poly_eval(alphas, x)
            gamma = c_at(x0)
            # (C(x) - C(x0)) / (x - x0) is a polynomial of degree r - 1: check its r-th finite difference vanishes
            vals = [MUL[c_at(x) ^ gamma][INV[x ^ x0]] for x in DOM]
            pts = [(x, vals[x]) for x in DOM[:r]]
            assert all(interp_value(pts, x) == vals[x] for x in DOM), "quotient is not of degree < r"
    print("T3 ok: C(x)/(x - x0) = (polynomial of degree r - 1) + C(x0)/(x - x0) for r = 1, 2, 3")


# ---------------------------------------------------------------------------------------------------------------


def make_words(kind, rng):
    if kind == "random":
        return [rng.randrange(Q) for _ in DOM], [rng.randrange(Q) for _ in DOM]
    if kind == "planted":  # a pair (F, G) on A - 1 common points, random elsewhere
        F = [rng.randrange(Q) for _ in range(DEG)]
        G = [rng.randrange(Q) for _ in range(DEG + 1)]
        Z = set(rng.sample(DOM, AGREE - 1))
        f0 = [poly_eval(F, x) if x in Z else rng.randrange(Q) for x in DOM]
        f1 = [poly_eval(G, x) if x in Z else rng.randrange(Q) for x in DOM]
        return f0, f1
    if kind in ("pole", "flats"):  # f0 = 1/(x - x0), f1 = w/(x - x0)
        x0 = 21
        w = [rng.randrange(Q) for _ in DOM] if kind == "pole" else [poly_eval([0] * 8 + [1], x) for x in DOM]
        f0 = [INV[x ^ x0] for x in DOM]
        f1 = [MUL[w[x]][INV[x ^ x0]] for x in DOM]
        return f0, f1
    raise SystemExit(f"unknown word {kind}")


def main():
    rng = random.Random(7)
    t0(rng)
    t3(rng)
    kinds = sys.argv[1:] or ["random", "planted", "pole", "flats"]
    for kind in kinds:
        f0, f1 = make_words(kind, rng)
        start = time.time()
        triples = all_lists(f0, f1)
        bad = len({(a, b) for a, b, _ in triples})
        sizes = Counter((a, b) for a, b, _ in triples)
        print(
            f"\n{kind}: {len(triples)} triples in {time.time() - start:.0f}s; challenges with a nonempty list: "
            f"{bad} of {Q * Q}; largest list {max(sizes.values()) if sizes else 0}"
        )
        if not triples:
            continue
        t1(kind, f0, f1, triples, rng)
        t2(kind, triples, rng)


if __name__ == "__main__":
    main()
