"""Pointer runs for the core inference (`infer.py`, feature `pfr`): pointer tables filled in loops.

`ptr`'s pointer facts (`preP`/`postP`: the word at a cell is a pointer whose given cells past it are written) as runs:
`(⟨Q, S, lo, hi⟩, offs)`, every cell `Q·g^(S·j)`, `lo ≤ j < hi`, holds a pointer `p_j` with `p_j·g^o` written for
`o ∈ offs`. A loop's pointer facts over its counter become runs over `[e(i), e(n))` (`prePR` when it reads them, `postPR`
when its calls guarantee them), a read through a word loaded from a run's cell is covered by it (bounds as for a read
in a run), a callee's `prePR` is met by a run in scope (the run rule), by its points (constant bounds), or becomes the
caller's own.
"""
import infer as I
from infer import mk, shift, num, base, F


def scope(st, conds):
    return st.pfr + [x for cd in (conds or ()) for x in cd[2].get(I.PFR, [])]


def read(P, st, s, offs, conds):
    """The word at cell `s` is a pointer with the cells `offs` past it written: a pointer run in scope holding `s`."""
    for r, o, w in reversed(scope(st, conds)):
        if not set(offs) <= o:
            continue
        used = []
        best = P.find_run(st, s, [(r, w)], used)
        if best is None:
            continue
        _, _, j, okl, okh = best
        if okl and okh:
            P.stats['w-pfr'] += 1
            return ('pfr', w, used)
        if 'idx' in F:
            res = []
            if not okl:
                res.append(P.addres(('lt', r[2], shift(j, 1), 'idx')))
            if not okh:
                res.append(P.addres(('lt', j, r[3], 'idx')))
            P.stats['w-pfr-res'] += 1
            return ('pfr', w, res)
    return None


def cover(P, st, t, offs, conds):
    """A callee's pointer run at `t` = `(Q, S, lo, hi)`: a run in scope (run rule), its points, or a precondition."""
    Q, S, lo, hi = t
    n = I.ioff(lo, hi)
    if n is not None and n <= 0:
        return ('empty',)
    for r, o, w in reversed(scope(st, conds)):
        if r[0] != Q or r[1] != S or not set(offs) <= o:
            continue
        u = []
        if P.lean_lower(st, lo, r, u) and P.lean_upper(st, hi, r, u):
            P.stats['wpr-run'] += 1
            return ('pfr', w, u)
    if n is not None and n <= 64 and not lo[0]:
        ws = []
        pf = dict(st.pf)
        for cd in conds or ():
            pf.update({c: f for c, f in cd[2].get(I.PF, {}).items() if c not in pf})
        for i in range(n):
            c = shift(Q, S * (lo[1] + i))
            f = pf.get(c)
            if f is not None and set(offs) <= f[0]:
                ws.append(('pf', f[1]))
                continue
            w = read(P, st, c, offs, conds)
            if w is None:
                break
            ws.append(w)
        else:
            P.stats['wpr-pts'] += 1
            return ('pts', ws)
    if not P.at_tail and P.iface(Q) and P.iface(lo) and P.iface(hi) and Q[0] and not (
            P.loop and any(b == P.sig.ctr for b, _ in Q[0])):
        e = (t, tuple(sorted(offs)))
        if e not in P.sig.prePR:
            P.sig.prePR.append(e)
        P.stats['wpr-pre'] += 1
        return ('pfr', ('prePR', P.sig.prePR.index(e)), [])
    # runs of other strides and points over the same table that hold every cell of `t`: with constant bounds a
    # decidable inclusion (`ptrsub`), else an instance residual (`ptrsubv`)
    haves = [(r, w) for r, o, w in scope(st, conds) if r[0][0] == Q[0] and set(offs) <= o]
    pf = dict(st.pf)
    for cd in conds or ():
        pf.update({c: f for c, f in cd[2].get(I.PF, {}).items() if c not in pf})
    pts = [(c, f[1]) for c, f in pf.items() if c[0] == Q[0] and set(offs) <= f[0]]
    if not haves and not pts:
        return None
    const = not lo[0] and not hi[0] and all(not r[2][0] and not r[3][0] for r, _ in haves)
    if const:
        offs_have = {c[1] for c, _ in pts}
        for r, _ in haves:
            offs_have |= {r[0][1] + r[1] * j for j in range(r[2][1], r[3][1])}
        if not all(Q[1] + S * j in offs_have for j in range(lo[1], hi[1])):
            return None
        k = P.addres(('subPR', t, tuple(r for r, _ in haves) + tuple(c for c, _ in pts), 'ptrsub'))
    else:
        k = P.addres(('subPR', t, tuple(r for r, _ in haves), 'ptrsubv'))
    P.stats['wpr-sub'] += 1
    return ('pfr', haves[0][1] if haves else pts[0][1], [k])


def loop_finish(P, G, tails, end):
    """A loop's pointer facts over its counter: its `preP` cells over the counter become `prePR` runs (unless each
    iteration gives the next one's, chained); the pointer
    facts its iteration gains over the counter (callees' `postP`) its `postPR` runs."""
    i = G.ctr
    keep = []
    for c, offs in G.preP:
        S = dict(c[0]).get(i)
        if not S:
            keep.append((c, offs))
            continue
        nxt = shift(c, S)
        if tails and all(nxt in st.pf and set(offs) <= st.pf[nxt][0] for st in tails):
            # chained: this iteration gives the next one's pointer fact
            keep.append((c, offs))
            P.stats['chained-ptr'] += 1
            continue
        if tails and all(nxt in st.pts for st in tails):
            # the iteration stores the next record's word: no caller wrote the table past the counter's record, so no
            # pointer run over it; the reads through it go to their object (`obj`)
            G.noptr.add(c)
            P.stats['noptr'] += 1
            continue
        Q = mk(tuple((b, e) for b, e in c[0] if b != i), c[1])
        r = (Q, S, base(i), end)
        for k, (r2, o2) in enumerate(G.prePR):
            if r2 == r:
                G.prePR[k] = (r, tuple(sorted(set(o2) | set(offs))))
                break
        else:
            G.prePR.append((r, tuple(offs)))
    G.preP = keep
    cand = None
    for st in tails:
        got = {}
        for c, (offs, _) in st.pf.items():
            if not c[0] or not all(b < P.m for b, _ in c[0]):
                continue
            S = dict(c[0]).get(i)
            if S:
                Q = mk(tuple((b, e) for b, e in c[0] if b != i), c[1])
                if Q[0]:
                    got[(Q, S, base(i), end)] = frozenset(offs)
        cand = got if cand is None else {r: o & got[r] for r, o in cand.items() if r in got and o & got[r]}
    # the words the iteration stores at a cell over the counter: pointers whose cells it knows written (in its scope
    # without a residual), accumulated over the iterations (`fillP`)
    acc = None
    for st in tails:
        got = {}
        for c, w in st.hv.items():
            if not c[0] or not all(b < P.m for b, _ in c[0]) or not w[0]:
                continue
            if len(w[0]) == 1 and w[0][0][1] == 1 and P.defkind.get(w[0][0][0]) == 'load' and \
                    (st.src.get(w[0][0][0]) or (None,))[0] == c:
                continue  # a word loaded from the cell, not stored there
            S = dict(c[0]).get(i)
            Q = mk(tuple((b, e) for b, e in c[0] if b != i), c[1]) if S else None
            if not S or not Q[0] or any(c == shift(x, S) for x in G.noptr):
                # (the next record's field of a walk: no table, `noptr`)
                continue
            offs = set()
            for o in range(64):
                x = shift(w, o)
                if x in st.pts:
                    offs.add(o)
                    continue
                u = []
                b = P.find_run(st, x, st.runs, u)
                if b is not None and b[3] and b[4] and not u:
                    offs.add(o)
            if offs:
                got[(Q, S, base(i), end)] = frozenset(offs)
        acc = got if acc is None else {r: o & got[r] for r, o in acc.items() if r in got and o & got[r]}
    for r, o in (acc or {}).items():
        cand = dict(cand or {})
        cand[r] = (cand.get(r, frozenset()) | o)
    pre = {r for r, _ in G.prePR}
    G.postPR = sorted((r, tuple(sorted(o))) for r, o in (cand or {}).items() if r not in pre)


def retsig(P, G, rename):
    """Guarantees at return: the pointer runs in scope on every path, over the parameters and returned words."""
    acc = None
    for st, vs in P.rets:
        got = {}
        for r, o, _ in st.pfr:
            t = tuple(rename(x) if x[0] else x for x in (r[0], r[2], r[3]))
            if None not in t and t[0][0]:
                got[(t[0], r[1], t[1], t[2])] = o
        acc = got if acc is None else {r: o & got[r] for r, o in acc.items() if r in got and o & got[r]}
    pre = {r for r, _ in G.prePR}
    G.postPR = sorted((r, tuple(sorted(o))) for r, o in (acc or {}).items() if r not in pre)
