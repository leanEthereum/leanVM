"""Residual rules of the core inference (`infer.py`): the bytecode walk's `rules_fix.py` and `rules_da.py` on core
names. Each hook returns a witness whose residuals (`P.addres`) are closed statements on core names, or `None`.

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
    """A constant `N` with `e(x) < N` known, and the residuals that give it."""
    best = None
    for a, b in st.lts:
        if a == base(x) and not b[0] and b[1] < 2 ** 20:
            if best is None or b[1] < best:
                best = b[1]
    if best is None:
        return None
    used = []
    P.lt(st, base(x), num(best), used)
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
    r = (shift(Q, o), S, num(0), num(N))
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
            R = (Q, 1, lo, pm)
            w = P.cover_run(st, R, site, conds)
            if w is None or w[0] == 'run' and w[2]:
                continue
            k = P.addres(('sub', r, (R,)))
            APPLIED['linSub'] = APPLIED.get('linSub', 0) + 1
            return ('sub', w, [k])
    return None


def run(P, st, r, site, conds):
    for rule in (lin_sub,):
        w = rule(P, st, r, site, conds)
        if w is not None:
            P.stats['rule-' + rule.__name__] += 1
            return w
    return None


def term(P, st, a, b, cond):
    return None
