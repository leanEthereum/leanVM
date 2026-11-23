"""Residual rules of the core inference (`infer.py`), on core names. Each hook returns a witness whose residuals (`P.addres`) are closed statements on core names, or `None`.

* `tabIdx`: a read `P·x^S·g^o` of a table over the parameters at a word `x` of known bound `e(x) < N` (a hint's range,
  a range check, a selector): the run `P·g^o`, stride `S`, `[0, N)` a precondition, the read inside it.
"""
from infer import mk, shift, num, base, ORD

APPLIED = {}


def split_index(P, c):
    """`c = Q·x^S·g^o`, `Q` over the parameters, `x` one other base: `(Q, x, S, o)`, or `None`."""
    q = tuple((b, e) for b, e in c[0] if b < P.m)
    xs = [(b, e) for b, e in c[0] if b >= P.m]
    if len(xs) != 1 or not q or c[1] >= 2 ** 20:
        return None
    if P.loop and any(b == P.sig.ctr for b, _ in q):
        return None
    return mk(q, 0), xs[0][0], xs[0][1], c[1]


def bound_of(P, st, x):
    """A bound `B` with `e(x) < e(B)` known, a constant (the least) or else a monomial over the parameters (a range
    check against an argument), and the residuals that give it."""
    best = None
    for a, b in st.lts:
        if a != base(x):
            continue
        if not b[0] and b[1] < 2 ** 20:
            if best is None or best[0] or b[1] < best[1]:
                best = b
        elif b[0] and P.iface(b) and best is None and not (P.loop and any(v == P.sig.ctr for v, _ in b[0])):
            best = b
    if best is None:
        return None
    used = []
    P.lt(st, base(x), best, used)
    return best, used


def tab_idx(P, st, c, site):
    s = split_index(P, c)
    if s is None:
        return None
    Q, x, S, o = s
    b = bound_of(P, st, x)
    if b is None:
        return None
    N, used = b
    r = (shift(Q, o), S, num(0), N)
    from infer import NARROW, F
    nw = NARROW.get((P.key, r)) if 'narrow' in F else None
    if nw is not None:
        # the callers write the table only at a stride: the read one of those cells, a residual (`objs.narrow_site`)
        a, S2 = nw
        r2 = (shift(Q, o + a), S2, num(0), num((N[1] - a + S2 - 1) // S2))
        if r2 not in P.sig.preR:
            P.sig.preR.append(r2)
        k = P.addres(('sub', c, r2, 'narrow'))
        APPLIED['narrow'] = APPLIED.get('narrow', 0) + 1
        return ('run', ('preR', P.sig.preR.index(r2)), used + [k])
    if r not in P.sig.preR:
        P.sig.preR.append(r)
    APPLIED['tabIdx'] = APPLIED.get('tabIdx', 0) + 1
    return ('run', ('preR', P.sig.preR.index(r)), used)


def read(P, st, c, site):
    for rule in (tab_idx,):
        w = rule(P, st, c, site)
        if w is not None:
            P.stats['rule-' + rule.__name__] += 1
            return w
    return None


def lin_sub(P, st, r, site, conds):
    """`linSub`: a run `Q·[lo, e(h))` of stride `S`, `h` not over the parameters, a parameter `p` with
    `p = h^K·m` (an `assert ==`), `K >= S`: inside `Q·[lo, e(p))` of stride 1 (`Res.sub`), that run known or a
    precondition."""
    Q, S, lo, hi = r
    if not P.iface(Q) or not P.iface(lo) or P.iface(hi) or not Q[0] or hi[1] != 0:
        return None
    for a, b in P.eqs:
        for pm, M in ((a, b), (b, a)):
            if len(pm[0]) != 1 or pm[0][0][1] != 1 or pm[0][0][0] >= P.m or pm[1] != 0:
                continue
            dm = dict(M[0])
            if not all(dm.get(x, 0) >= S * e for x, e in hi[0]):
                continue
            # the cells `Q·g^(k + S·j)`, `k < S`, lie in the stride-1 run from `Q·g^0` (`k + S·j < S·e(h) <= e(p)`);
            # one from `Q·g^k` would reach `k` cells past `e(p)`
            R = ((Q[0], 0), 1, lo, pm) if lo == num(0) and Q[1] < S else (Q, 1, lo, pm)
            w = P.cover_run(st, R, site, conds)
            if w is None or w[0] == 'run' and w[2]:
                continue
            k = P.addres(('sub', r, (R,)))
            APPLIED['linSub'] = APPLIED.get('linSub', 0) + 1
            return ('sub', w, [k])
    return None


def derive(P, st):
    """Runs implied by runs in scope, each a `Res.sub` of index arithmetic (true of all words): `merge`, the `S`
    residues `T·g^d`, `d < S`, of stride `S` over `[lo, hi)` are `T` over `[S·lo, S·hi)`; `concat`, `T` over `[0, A)`
    then `T·A` over `[0, B)` are `T` over `[0, A·B)`; `rename`, a bound `M^k` with `M = p` (an `assert ==`) is `p^k`."""
    from infer import mmul, mpow
    have = {r for r, _ in st.runs}
    new = []
    by = {}
    for r in have:
        Q, S, lo, hi = r
        if S > 1 and Q[1] < S:
            by.setdefault(((Q[0], 0), S, lo, hi), set()).add(Q[1])
    for (T, S, lo, hi), ds in by.items():
        if len(ds) == S:
            R = (T, 1, mpow(lo, S), mpow(hi, S))
            if R not in have:
                new.append((R, [((T[0], d), S, lo, hi) for d in range(S)], 'merge'))
    ones = [r for r in have if r[1] == 1 and r[2] == num(0)] + [x[0] for x in new if x[0][1] == 1 and x[0][2] == num(0)]
    # a function whose continuation is in each branch (`dup`): concatenations of concatenations, to its guarantee
    for _ in range(3 if getattr(P, 'dups', None) else 1):
        seen = {x[0] for x in new}
        more = []
        for a in ones:
            for b in ones:
                if b[0] == mmul(a[0], a[3]) and a[3][0]:
                    R = (a[0], 1, num(0), mmul(a[3], b[3]))
                    if R not in have and R not in seen:
                        seen.add(R)
                        more.append((R, [a, b], 'concat'))
        if not more:
            break
        new += more
        ones += [x[0] for x in more]
    out = []
    for R, parts, why in new:
        for x, y in P.eqs:
            for M, pm in ((x, y), (y, x)):
                # `pm` a parameter, or a constant (`M = g^c` by a quotient's equation: the bound a constant)
                if (len(pm[0]) == 1 and pm[0][0][1] == 1 and pm[0][0][0] < P.m and pm[1] == 0 or not pm[0] and
                        pm[1] < 2 ** 20) and M[0] and M[1] == 0:
                    k = None
                    dm, dh = dict(M[0]), dict(R[3][0])
                    if set(dm) == set(dh) and R[3][1] == 0:
                        ks = {dh[v] // dm[v] for v in dm if dh[v] % dm[v] == 0}
                        if len(ks) == 1 and all(dh[v] == dm[v] * list(ks)[0] for v in dm):
                            k = ks.pop()
                    if k:
                        R2 = (R[0], 1, R[2], mpow(pm, k))
                        out.append((R2, [R], 'rename'))
        out.append((R, parts, why))
    for R, parts, why in out:
        if R in have:
            continue
        have.add(R)
        i = P.addres(('sub', R, tuple(parts), why))
        st.runs.append((R, ('derived', i)))
        P.stats['derive-' + why] += 1


def run(P, st, r, site, conds):
    for rule in (lin_sub,):
        w = rule(P, st, r, site, conds)
        if w is not None:
            P.stats['rule-' + rule.__name__] += 1
            return w
    return None
