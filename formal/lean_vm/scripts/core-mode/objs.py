"""Objects for the core inference (`infer.py`, features `obj` and `narrow`): its object families on core names.

A read `c` the other rules leave uncovered is usually through a pointer: a stream cursor, a word loaded from a record,
a callee's returned word. Its **object** is what that pointer points into: an allocation or a callee's returned buffer
of this function (`('val', v)`), the object a parameter points into (`('param', i)`), the object the word at a cell over
the parameters points into (`('cell', s)`), a ghost slot (`('ghost', j)`). The read is then the residual
`subR ⟨c's run⟩ R`: its cells are among those of the run `R` the object is written as in scope (`CRes.subR`), a closed
statement on core names, true of every honest instance by the object's family lemma.

**Ghost slots** name a caller's object in a function that has no parameter for it (a loop reading a cursor from its
record): ghost `j` is the value `GB + j`, its run `⟨G_j, 1, 0, G_h⟩` (base and bound ghosts) a precondition; each call
instantiates the ghosts by monomials of the caller (`calls`' ghost arguments), here by resolving the ghost's anchor
(the callee's parameter or record cell) to the caller's object and taking its run. Anchors, `postIn` (the words a
callee stores point into an anchor's object) and `retIn` (a returned word points into one) are inference devices only:
the Lean check sees ghost runs, ghost arguments and `subR` residuals, and the residual carries the meaning.

`narrow`: a table run a function reads at a hinted index (`tabIdx`'s `⟨P·g^o, 1, 0, N⟩`) that every caller writes only
at a stride `S` (`selector_tables`' levels) becomes `⟨P·g^o, S, 0, N/S⟩`, the read the residual `sub c R` (the index a
multiple of `S`).
"""
import infer as I
from infer import mk, shift, num, base, F, GB

OBJ_KINDS = ('load', 'ret', 'alloc')


def is_obj(P, b):
    if b >= GB:
        return True
    if b < P.m:
        return not (P.loop and b == P.sig.ctr)
    return P.defkind.get(b) in OBJ_KINDS


def anchorable(P, c):
    return bool(c[0]) and all(b < P.m for b, _ in c[0])


def ptrlike(P, b):
    """A parameter the signature already reads as a pointer (a cell or run over it alone)."""
    G = P.sig
    return any(c[0] == ((b, 1),) for c in G.pre) or any(r[0][0] == ((b, 1),) for r in G.preR)


def idxlike(P, b):
    """A value used as an index: in an exponent fact (a range check, a selector, a hint's range) or raised to a power
    in some monomial; then not an object when another base can be."""
    st = P.cur
    key = (id(st), len(st.env), len(st.lts))
    if getattr(P, 'idxkey', None) != key:
        s = set()
        for a, c in st.lts:
            s.update(x for x, _ in a[0])
            s.update(x for x, _ in c[0])
        for m in st.env.values():
            s.update(x for x, e in m[0] if e > 1)
        P.idxkey, P.idxset = key, s
    return b in P.idxset


def order(P, bs):
    # an allocation is always a pointer, so the other bases of a monomial over it are indices
    rank = {'ghost': 0, 'alloc': 1, 'ptr': 2, 'load': 3, 'ret': 4, 'param': 5}
    return sorted(bs, key=lambda b: (b < GB and getattr(P, 'cur', None) is not None and idxlike(P, b),
                                     rank['ghost' if b >= GB else ('ptr' if ptrlike(P, b) else 'param') if b < P.m
                                          else P.defkind.get(b)]))


def gcd_rest(c, rb):
    import math
    g = 0
    for b, e in c[0]:
        if b != rb:
            g = math.gcd(g, e)
    return g


def cell_root(P, c):
    rs = [b for b, e in c[0] if e == 1 and is_obj(P, b)]
    return order(P, rs)[0] if rs else None


def on_store(P, st, c, d):
    P.cur = st
    """A store: the object of the word, by the cell's object and its offset modulo the record stride."""
    rb = cell_root(P, c)
    if rb is None:
        return
    o = obj_of_mono(P, st, P.mono(st, d))
    P.stores.append((rb, c[1], gcd_rest(c, rb), o))


def stored_obj(P, t):
    rb = cell_root(P, t)
    if rb is None:
        return None
    g = gcd_rest(t, rb)
    os_ = set()
    for rb2, off, g2, o in P.stores:
        if rb2 != rb:
            continue
        m = g or g2
        if (off - t[1]) % m == 0 if m else off == t[1]:
            os_.add(o)
    return os_.pop() if len(os_) == 1 else None


def obj_of_base(P, st, b, depth=0):
    if depth > 40:
        return None
    if b >= GB:
        return ('ghost', b - GB)
    if b < P.m:
        return ('param', b)
    k = P.defkind.get(b)
    if k == 'ret':
        rs = P.retsite.get(b)
        if rs is not None:
            f, args, j, ginst = rs
            G = I.SIGS.get(f)
            anc = G.retIn.get(j) if G is not None else None
            if anc is not None:
                o = resolve(P, st, anc, args, ginst, depth + 1)
                if o is not None:
                    return o
        return ('val', b)
    if k == 'load':
        src = st.src.get(b)
        if src is not None:
            o = content_obj(P, st, src[0], depth + 1)
            if o is not None:
                return o
        return ('val', b)
    if k == 'alloc':
        return ('val', b)
    return None


def obj_of_mono(P, st, m, depth=0):
    for b in order(P, [b for b, e in m[0] if e == 1 and is_obj(P, b)]):
        o = obj_of_base(P, st, b, depth)
        if o is not None:
            return o
    return None


def objs_of_mono(P, st, m):
    out = []
    for b in order(P, [b for b, e in m[0] if e == 1 and is_obj(P, b)]):
        o = obj_of_base(P, st, b)
        if o is not None and o not in out:
            out.append(o)
    return out


def content_obj(P, st, t, depth=0, conds=None):
    """The object the word at cell `t` points into."""
    w = st.hv.get(t)
    for cd in conds or ():
        w = w or cd[2].get(t)
    if w is not None and w != base(t) and t not in [((b, 1),) for b, _ in w[0]]:
        o = obj_of_mono(P, st, w, depth + 1)
        if o is not None:
            return o
    for (Q, S), o in reversed(P.contents):
        if matches(P, t, Q, S):
            return o
    o = stored_obj(P, t)
    if o is not None:
        return o
    if anchorable(P, t):
        return ('cell', t)
    return None


def matches(P, t, Q, S):
    """`t` one of the cells `Q·g^(S·j)` (`j` an index, possibly one below the pattern's base: a loop's pattern is
    over its next counter, `i·g`)."""
    if S == 0:
        return t == Q
    return any(P.idx_in(t, (shift(Q, -S * k), S, num(0), num(0))) is not None for k in range(3) if Q[1] >= S * k)


def resolve(P, st, anc, args, ginst, depth=0, conds=None):
    """A callee's anchor at a call with `args`: the caller's object."""
    if anc[0] == 'param':
        return obj_of_mono(P, st, P.mono(st, args[anc[1]]), depth + 1) if anc[1] < len(args) else None
    if anc[0] == 'cell':
        old = P.ginst
        P.ginst = ginst
        t = P.tr(st, anc[1], args, None)
        P.ginst = old
        return content_obj(P, st, t, depth + 1, conds) if t is not None else None
    return None


def ghost(P, anc):
    G = P.sig
    if anc not in G.ghosts:
        G.ghosts.append(anc)
        G.ghosts.append(('hi', len(G.ghosts) - 1))
    j = G.ghosts.index(anc)
    return j, G.ghosts.index(('hi', j))


def ghost_run(j, jh):
    return ((((GB + j, 1),), 0), 1, num(0), (((GB + jh, 1),), 0))


def run_for(P, st, obj, conds=None, create=True):
    """The run `(R, witness)` the object is written as in scope, a ghost run for a caller's object."""
    runs = st.runs + [x for cd in (conds or ()) for x in cd[1]]
    if obj[0] in ('val', 'param'):
        v = obj[1]
        best = None
        if create and not P.at_tail and 'rules' in F and not any(
                R[0] == (((v, 1),), 0) and R[1] == 1 and R[2] == num(0) and not R[3][0] for R, _ in runs):
            # runs implied by those in scope (`merge`, `concat`, `rename`), as at a `ret`
            import rules
            n = len(st.runs)
            rules.derive(P, st)
            runs = runs + st.runs[n:]
        for R, rw in reversed(runs):
            if R[0] == (((v, 1),), 0) and R[1] == 1 and R[2] == num(0):
                if best is None or not R[3][0] and best[0][3][0]:
                    best = (R, rw)
        if create and not P.at_tail:
            ch = chain(P, st, v, runs, conds)
            if ch is not None and (best is None or best[0][3][0] or best[0][3][1] < ch[0][3][1]):
                best = ch
        if best is None and create and not P.at_tail:
            best = derive_for(P, st, v, runs, conds)
        if best is not None and create and not P.at_tail:
            best = extend(P, st, best, runs, conds)
        if best is not None:
            return best
        if obj[0] == 'val':
            return None
        anc = obj
    elif obj[0] == 'cell':
        anc = obj
    else:
        j = obj[1]
        if j >= len(P.sig.ghosts) or P.sig.ghosts[j][0] == 'hi':
            return None
        anc = P.sig.ghosts[j]
    if anc not in P.sig.ghosts and (not create or P.at_tail):
        return None
    j, jh = ghost(P, anc)
    R = ghost_run(j, jh)
    if R not in P.sig.preR:
        if not create or P.at_tail:
            return None
        P.sig.preR.append(R)
    for R2, rw in runs:
        if R2 == R:
            return R, rw
    rw = ('preR', P.sig.preR.index(R))
    st.runs.append((R, rw))
    return R, rw


def chain(P, st, v, runs, conds=None):
    """The object `v`'s longest prefix written as adjacent constant runs and points from its base: one run
    `⟨v, 1, 0, n⟩` (`concat`, generic) when it takes more than one part."""
    pts = set(st.pts).union(*[cd[0] for cd in conds or ()])
    by = {}
    for R, rw in runs:
        Q, S, lo, hi = R
        if Q[0] == ((v, 1),) and S == 1 and lo == num(0) and not hi[0] and Q[1] < 2 ** 40 and hi[1] < 2 ** 40:
            if hi[1] > by.get(Q[1], (0,))[0]:
                by[Q[1]] = (hi[1], R)
    pos, parts = 0, []
    while True:
        if pos in by:
            n, R = by[pos]
            parts.append(R)
            pos += n
        elif shift((((v, 1),), 0), pos) in pts:
            parts.append(shift((((v, 1),), 0), pos))
            pos += 1
        else:
            break
    if len(parts) < 2 or not any(len(x) == 4 for x in parts) and P.allocsz.get(v) != pos:
        # points alone are what was read or written so far: the object only when they fill its allocation
        return None
    R = ((((v, 1),), 0), 1, num(0), num(pos))
    for R2, rw in runs:
        if R2 == R:
            return R, rw
    k = P.addres(('sub', R, tuple(parts), 'concat'))
    st.runs.append((R, ('derived', k)))
    P.stats['derive-chain'] += 1
    return R, ('derived', k)


def extend(P, st, best, runs, conds=None):
    """The object's run `⟨v, 1, 0, A⟩` continued by the points `v·A·g^k`, `k < K`, written after it (a buffer filled
    by a loop, then a few cells): `⟨v, 1, 0, A·g^K⟩` (`concat`, generic)."""
    R, rw = best
    Q, S, lo, hi = R
    if S != 1 or lo != num(0) or not hi[0]:
        return best
    pts = set(st.pts).union(*[cd[0] for cd in conds or ()])
    top = I.mmul(Q, hi)
    K = 0
    while shift(top, K) in pts and K < 64:
        K += 1
    if not K:
        return best
    R2 = (Q, 1, num(0), shift(hi, K))
    for R3, rw3 in runs:
        if R3 == R2:
            return R3, rw3
    k = P.addres(('sub', R2, (R,) + tuple(shift(top, i) for i in range(K)), 'concat'))
    st.runs.append((R2, ('derived', k)))
    P.stats['derive-extend'] += 1
    return R2, ('derived', k)


def addres(P, key, r):
    i = P.objres.get(key)
    if i is None:
        P.objres[key] = i = len(P.res)
        P.res.append(r)
        P.stats['res-subR'] += 1
    return i


def read(P, st, c, site, conds):
    P.cur = st
    if 'obj' not in F:
        return None
    for o in objs_of_mono(P, st, c):
        rr = run_for(P, st, o, conds)
        if rr is None:
            continue
        R, rw = rr
        if R[0][0] == c[0]:
            continue  # over the run's own base: the index rules' business
        key = ('pt', c[0], R)
        i = P.objres.get(key)
        if i is None:
            i = addres(P, key, ('subR', (c[0], c[1], c[1] + 1), R, 'obj'))
        else:
            _, (bs, a, b), _, tag = P.res[i]
            P.res[i] = ('subR', (bs, min(a, c[1]), max(b, c[1] + 1)), R, tag)
        P.stats['w-obj'] += 1
        return ('run', rw, [i])
    return None


def run(P, st, r, site, conds):
    P.cur = st
    for o in objs_of_mono(P, st, r[0]):
        rr = run_for(P, st, o, conds)
        if rr is None:
            continue
        R, rw = rr
        if R[0][0] == r[0][0] and R[1] == r[1]:
            continue
        i = addres(P, ('run', r, R), ('subR', r, R, 'obj'))
        P.stats['wr-obj'] += 1
        return ('run', rw, [i])
    return None


def inst(P, st, G, args, conds, tail=False):
    P.cur = st
    """The callee's ghosts at a call: each anchor resolved to the caller's object, its run's base and bound."""
    gi = [None] * len(G.ghosts)
    for j, anc in enumerate(G.ghosts):
        if anc[0] == 'hi':
            continue
        o = resolve(P, st, anc, args, gi, conds=conds or P.armconds)
        if o is None:
            continue
        rr = run_for(P, st, o, conds, create=not tail)
        if rr is None:
            continue
        R = rr[0]
        if R[1] != 1 or R[2] != num(0):
            continue
        gi[j] = R[0]
        gi[G.ghosts.index(('hi', j))] = R[3]
    return gi


def after_call(P, st, f, G, args, rets, ginst):
    for j, v in enumerate(rets or ()):
        P.retsite[v] = (f, tuple(args), j, ginst)
    for (Q, S), anc in G.postIn:
        o = resolve(P, st, anc, args, ginst)
        if o is None:
            continue
        old = P.ginst
        P.ginst = ginst
        t = P.tr(st, Q, args, None)
        P.ginst = old
        if t is not None:
            P.contents.append(((t, S), o))


def anchor_of(P, o):
    if o is None:
        return None
    if o[0] in ('param', 'cell'):
        return o
    if o[0] == 'ghost':
        a = P.sig.ghosts[o[1]] if o[1] < len(P.sig.ghosts) else None
        return a if a and a[0] != 'hi' else None
    return None


def summary(P, G):
    """`retIn` and `postIn`: what the returned words and the stored words point into, as anchors."""
    G.retIn = {}
    if not P.loop and P.rets and P.retvals:
        for j in range(len(P.retvals)):
            ancs = set()
            for st, vs in P.rets:
                if j < len(vs):
                    ancs.add(anchor_of(P, obj_of_mono(P, st, P.mono(st, vs[j]))))
            if len(ancs) == 1 and None not in ancs:
                G.retIn[j] = ancs.pop()
    sts = [t for t, *_ in P.tails] if P.loop else [t for t, _ in P.rets]
    cand = None
    for st in sts:
        got = {}
        for c, w in st.hv.items():
            if not anchorable(P, c):
                continue
            a = anchor_of(P, obj_of_mono(P, st, w))
            if a is None or a == ('cell', c):
                continue
            S = dict(c[0]).get(G.ctr, 0) if P.loop else 0
            Q = mk(tuple((b, e) for b, e in c[0] if not (P.loop and b == G.ctr)), c[1]) if S else c
            got[(Q, S)] = a
        cand = got if cand is None else {k: a for k, a in cand.items() if got.get(k) == a}
    G.postIn = sorted((cand or {}).items(), key=str)


def narrow_site(P, st, f, r, t, conds):
    """A callee's table run `r` (`⟨Q, 1, 0, N⟩`, constant `N`), at `t` here, not covered: which of its cells are
    written here (points in scope)."""
    Q, S, lo, hi = r
    if S != 1 or lo != num(0) or hi[0] or hi[1] > 256:
        return
    pts = set(st.pts)
    for cd in conds or ():
        pts |= set(cd[0])
    have = frozenset(k for k in range(hi[1]) if shift(t[0], k) in pts)
    I.NARROW_SITES.setdefault((f, r), []).append(have)


def narrow_update():
    """Each table run whose callers all write exactly the cells `a + S·j` of it: narrowed to them."""
    changed = False
    for (f, r), sites in I.NARROW_SITES.items():
        common = frozenset.intersection(*sites)
        ks = sorted(common)
        if len(ks) < 2:
            continue
        a, S = ks[0], ks[1] - ks[0]
        N = r[3][1]
        if S < 2 or ks != list(range(a, N, S)):
            continue
        if I.NARROW.get((f, r)) != (a, S):
            I.NARROW[(f, r)] = (a, S)
            changed = True
    return changed


def derive_for(P, st, v, runs, conds=None):
    """The object `v` written as `S` residue runs of stride `S` (a table filled `S` cells an iteration) and points
    before them: one run `⟨v, 1, 0, hi⟩` (`merge`, `concat`: index arithmetic, generic residuals)."""
    by = {}
    for R, rw in runs:
        Q, S, lo, hi = R
        if Q[0] == ((v, 1),) and S > 1 and Q[1] < S:
            by.setdefault((S, lo, hi), {})[Q[1]] = rw
    for (S, lo, hi), ds in by.items():
        if len(ds) != S:
            continue
        R = (((((v, 1),), 0)), 1, I.mpow(lo, S), I.mpow(hi, S))
        parts = [((((v, 1),), d), S, lo, hi) for d in range(S)]
        k = P.addres(('sub', R, tuple(parts), 'merge'))
        rw = ('derived', k)
        lo1 = R[2]
        if lo1 != num(0) and not lo1[0] and lo1[1] <= 64:
            # the cells below the merged run as points (a callee's guarantees before its loop)
            pts = set(st.pts).union(*[cd[0] for cd in conds or ()])
            if all(shift((((v, 1),), 0), i) in pts for i in range(lo1[1])):
                R2 = (R[0], 1, num(0), R[3])
                k2 = P.addres(('sub', R2, (R,) + tuple(shift((((v, 1),), 0), i) for i in range(lo1[1])), 'concat'))
                st.runs.append((R, rw))
                st.runs.append((R2, ('derived', k2)))
                P.stats['derive-obj'] += 1
                return R2, ('derived', k2)
        st.runs.append((R, rw))
        if lo1 == num(0):
            P.stats['derive-obj'] += 1
            return R, rw
    return None
