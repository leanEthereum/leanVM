"""`CoreMode.subRS` (`CoreMode/CoreResS.lean`): a run of symbolic bounds inside a run of constant bounds, its exponent
bounds from the facts `e(v) < n` the same certificate states (each of a family itself).

Residuals as `heapc.py` writes them: `('lt', a, b)`, `('subR', q, r)`, `('under', g, r)`; a run `(cell, S, lo, hi)`, a
cell `(bases, off)`, an index `('num', n)`, `('val', v)` or `('mono', cell)`."""

CAPE = 2 ** 62


def fact_of(g, v, r):
    """`CoreMode.factOf`: `e(v) < n`, `n < 2^62`, unconditional or under conditions among `g`: `n`."""
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num':
        return r[2][1] if r[1][1] == v and r[2][1] < CAPE else None
    if r[0] == 'under' and r[2][0] == 'lt' and r[2][1][0] == 'val' and r[2][2][0] == 'num':
        x, n = r[2][1][1], r[2][2][1]
        return n if x == v and n < CAPE and all(tuple(c) in {tuple(d) for d in g} for c in r[1]) else None
    return None


def fact_b(L, g, v):
    """`CoreMode.factB`: the least fact's bound on `v`."""
    ns = [n for n in (fact_of(g, v, r) for r in L) if n is not None]
    return min(ns) if ns else None


def prod_max(L, g, bs):
    """`CoreMode.prodMax`: `Σ a·(n - 1)`."""
    t = 0
    for v, a in bs:
        n = fact_b(L, g, v)
        if n is None:
            return None
        t += a * max(n - 1, 0)
    return t


def idx_max(L, g, i):
    """`CoreMode.idxMax`: an index's exponent at most."""
    if i[0] == 'num':
        return i[1]
    if i[0] == 'val':
        n = fact_b(L, g, i[1])
        return None if n is None else max(n - 1, 0)
    M = prod_max(L, g, i[1][0])
    return None if M is None else M + i[1][1]


def sub_rs_g(L, g, q, r):
    """`CoreMode.subRSg`: `r = ⟨⟨rb, o'⟩, 1, l, N⟩`, `q`'s bases `rb` then the rest, `o' ≤ o`, `l ≤ o - o'`,
    `o - o' + prodMax rest + S·(idxMax hi - 1) < N < 2^62`."""
    (qb, qo), S, _, hi = q
    (rb, ro), S2, rl, rh = r
    if rl[0] != 'num' or rh[0] != 'num':
        return False
    l, N = rl[1], rh[1]
    qb, rb = [tuple(x) for x in qb], [tuple(x) for x in rb]
    if qb[:len(rb)] != rb or S2 != 1 or ro > qo or l > qo - ro or not N < CAPE:
        return False
    H, M = idx_max(L, g, hi), prod_max(L, g, qb[len(rb):])
    return H is not None and M is not None and qo - ro + M + S * max(H - 1, 0) < N


def sub_rs(L, r):
    """`CoreMode.subRS`: `subRSg` over the certificate's residuals `L`, unconditional or under conditions."""
    if r[0] == 'subR':
        return sub_rs_g(L, (), r[1], r[2])
    if r[0] == 'under' and r[2][0] == 'subR':
        return sub_rs_g(L, r[1], r[2][1], r[2][2])
    return False
