"""Inference rules beside `infer.py`'s and `rules_da.py`'s, installed into `infer.py` by `install(globals())`:
each extends what a function's inference finds, and the walks that follow must accept it."""
from walk import Fail, mul, shift, first

# the functions each rule extended (a report for the inference's callers)
APPLIED = {}

# `armBlocks` only in functions of at most this many instructions
DISPATCH_MAX = 64


def divides(f, x, y):
    """The code divides frame cell `y` by frame cell `x` (a `MUL` back-solving `[y] / [x]`), as a range check
    of the quotient does: the sign the bound `x` is below `y`."""
    return any(op == 'mul' and a[2] == y and x in a[:2] for op, a in f['ops'])


def boundSub(I, inf, i, r2, A):
    """A run up to frame cell `x`'s exponent inside a known run up to frame cell `y`'s, over the same product,
    stride and offset, the code dividing `y` by `x` (`verify_tables`' `zeta1`, up to the bus depth, read up
    to the zerocheck's): the residual `Res.sub` (its `subBound` family), `e(x) <= e(y)`."""
    q, lo, hi, S, d = r2
    if hi[0] != 'ex' or hi[1][0] != 'fr': return False
    for R in sorted(A.r, key=str):
        Rq, Rlo, Rhi, S2, d2 = R
        if Rq != q or S2 != S or d2 != d or Rhi[0] != 'ex' or Rhi[1][0] != 'fr' or Rhi[2] != hi[2]: continue
        if not A.le(Rlo, lo) or not divides(inf.f, hi[1][1], Rhi[1][1]): continue
        inf.addRes(i, ('sub', r2, [R])); A.r.add(r2)
        APPLIED.setdefault('boundSub', set()).add(inf.f['name'])
        return True
    return False


# a hinted index into a parameter's table is below this (`tabIdx`)
TAB_IDX = 64


def tabIdx(I, inf, k, i0, A):
    """A load from a parameter's table at a word no check bounds yet (`verify_sub`'s `g_squares` at a hinted
    table log, certified only later in `verify_tables`): the word's exponent below `TAB_IDX` (`Res.lt`), the
    table's cells up to it plus the offset a precondition, so the read is inside it (`Abs.tabCovered`)."""
    f = inf.f
    if k[0] != 0 or len(k[2]) != 2 or any(e != 1 for b, e in k[2]) or k[1] >= 2 ** 20: return False
    ps = I['params'](f)
    for (Qb, _), (b, _) in ((k[2][0], k[2][1]), (k[2][1], k[2][0])):
        if Qb[0] != 'fr' or Qb[1] not in ps or (b[0] == 'fr' and b[1] in ps): continue
        x = ('ex', b, 0)
        known = A.ltI(x, ('num', TAB_IDX))
        if not known and not inf.w.idxOk(A, x):
            # the index a word of an unchecked heap cell: the frame cell the pointer's product took it from,
            # named by its cell (`Res.name`), so the next pass reads the table at that cell
            c = indexCell(f, i0)
            if c is None: continue
            j = next((j for j in range(i0 - 1, -1, -1) if f['ops'][j][0] in ('mul', 'xor') and f['ops'][j][1][2] == c), None)
            if j is None or ('name', c) in inf.res[j + 1]: continue
            inf.addRes(j + 1, ('name', c))
            APPLIED.setdefault('tabIdx', set()).add(f['name'])
            return True
        r = ((0, 0, ((Qb, 1),)), ('num', 0), ('num', TAB_IDX + k[1]), 1, 0)
        if not known: inf.addRes(i0, ('lt', x, ('num', TAB_IDX))); A.lt.add((x, ('num', TAB_IDX)))
        if r not in inf.preR: inf.preR.add(r); inf.new = True
        A.r.add(r)
        APPLIED.setdefault('tabIdx', set()).add(f['name'])
        return True
    return False


def indexCell(f, i0):
    """The load at `i0` through a pointer `[p]` that a `MUL` of a parameter and one frame cell `c` wrote:
    `c`."""
    op, a = f['ops'][i0]
    if op != 'deref': return None
    for j in range(i0 - 1, -1, -1):
        op2, b = f['ops'][j]
        if op2 == 'mul' and b[2] == a[0]:
            ps = {2 + n for n in range(f.get('nargs', 0))}
            xs = [y for y in b[:2] if y not in ps]
            return xs[0] if len(xs) == 1 else None
    return None


def tileChain(A, a):
    """The known runs tiling run `a = (Q, 0, e(n), S, d)` part by part: part `k` the runs over
    `Q_k = Q·x_0^(S m_0)·…` from `0` up to `e(x_k)`, stride `S m_k`, at every offset `d + S t`, `t < m_k`,
    each part's bound `x_k` a word. At least two parts, the last of stride `S`, else `None`."""
    Q, lo, hi, S, d = a
    by = {}
    for R in A.r:
        Rq, Rlo, Rhi, S2, d2 = R
        if Rlo == ('num', 0) and Rhi[0] == 'ex' and Rhi[2] == 0 and S2 % S == 0 and d2 % S == d:
            by.setdefault((Rq, Rhi, S2), set()).add(d2)
    parts = []; q = Q; k = 0
    while True:
        got = [(hi2, S2) for (q2, hi2, S2), ds in by.items() if q2 == q and ds >= {d + S * t for t in range(S2 // S)}]
        if len(got) != 1 or k == 8: break
        hi2, S2 = got[0]
        parts += [(q, ('num', 0), hi2, S2, d + S * t) for t in range(S2 // S)]
        q = mul(q, (0, 0, ((hi2[1], S2),))); k += 1
    # the chain ends where the table does: no run past its last part
    if any(R[0] == q for R in A.r): return None
    return parts if len({r[2] for r in parts}) >= 2 and parts[-1][3] == S else None


def tileSub(I, inf, i, r2, A):
    """A run from `0` up to frame cell `n`'s exponent tiled by known runs part by part (`tileChain`: a
    table filled in pieces, each piece's length a frame cell, `main`'s claim tables, the declared claims
    then the duplicates): the residual `Res.sub`, `e(n) = Σ m_k e(x_k)`."""
    q, lo, hi, S, d = r2
    if lo != ('num', 0) or hi[0] != 'ex' or hi[2] != 0 or hi[1][0] != 'fr': return False
    bs = tileChain(A, r2)
    if not bs: return False
    inf.addRes(i, ('sub', r2, bs)); A.r.add(r2)
    APPLIED.setdefault('tileSub', set()).add(inf.f['name'])
    return True


# `tilePost` only in functions of at most this many instructions (each try is a walk)
TILE_POST_MAX = 256


def tilePost(I, n, sig, res):
    """A pointer parameter's table tiled, after a table call, by runs over the call's own counts
    (`claim_list_digest`: the big blocks, the groups, the rest, each a count `list_split` returned): the run
    up to a count parameter's exponent, its residual (`tileSub`) at the call's return, as a guarantee
    (`postR`). Kept if the function walks."""
    f = I['fns'][n]
    if n in I['isloop'] or not f['tabs'] or f['count'] > TILE_POST_MAX: return False
    walk = lambda keep=False: _walk(I, n, sig, res, keep)
    try: w = walk(True)
    except Fail: return False
    ps = sorted(I['params'](f))
    old = list(sig.postR); oldres = {k: list(v) for k, v in res.items()}
    added = []
    for it in sorted(f['tabs']):
        r = it + 1
        A = w.states[r] if r < len(w.states) else None
        if A is None: continue
        for p in ps:
            Q = (0, 0, ((('fr', p), 1),))
            Ss = sorted({R[3] for R in A.r if R[0] == Q})
            for c in ps:
                if c == p or not Ss: continue
                for S in sorted({R[3] for R in A.r if Q[2][0] in R[0][2]}):
                    a0 = [(Q, ('num', 0), ('ex', ('fr', c), 0), S, d) for d in range(S)]
                    chains = [tileChain(A, a) for a in a0]
                    if not all(chains): continue
                    for a, bs in zip(a0, chains):
                        if a in sig.postR: continue
                        res.setdefault(r, []).append(('sub', a, bs)); sig.postR.append(a); added.append(a)
                    break
    if not added: return False
    try:
        walk()
        APPLIED.setdefault('tilePost', set()).add(n)
        return True
    except Fail:
        sig.postR = old; res.clear(); res.update(oldres)
        return False


def _walk(I, n, sig, res, keep=False):
    f = I['fns'][n]
    w = I['Walk'](I['E'], f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main')
    w.run(f['ops'], keep=keep)
    return w


def armBlocks(I, f):
    """A table call's arms, arm `j` guaranteeing at least `j + c` cells from the start of one product over
    its parameters, the last exactly `n + c` (`eq_prefix_chain`'s `eq_prefix_run`, arm `n` the chain's
    `n + 1` entries): each arm's block also as a run of stride 1, which the arms met take up to the
    selector (`armRuns`). The runs are the arms' own points, so their walks still pass."""
    fns, E, block = I['fns'], I['E'], I['block']
    # a dispatch function only: in a large one the arms' runs weigh on every later lookup (`kprofile`)
    if f['count'] > DISPATCH_MAX: return
    for arms in I['tableArms'](f):
        if len(arms) < 3 or any(a in I['isloop'] for a in arms): continue
        Gs = [E.sigs.get(fns[a]['entry']) for a in arms]
        if not all(Gs): continue
        n = len(arms) - 1
        Qs = {(0, 0, m[2]) for m in Gs[-1].post if m[0] == 0 and m[2]} | \
            {(0, 0, r[0][2]) for r in Gs[-1].postR if r[0][0] == 0 and r[0][1] == 0 and r[0][2]}
        for Q in sorted(Qs):
            c = block(Gs[-1], Q) - n
            if c < 1 or any(block(G, Q) < j + c for j, G in enumerate(Gs)): continue
            for j, G in enumerate(Gs):
                r = (Q, ('num', 0), ('num', j + c), 1, 0)
                if r not in G.postR:
                    G.postR.append(r)
                    APPLIED.setdefault('armBlocks', set()).add(f['name'])


def _sameCells(R, q, S, d):
    """Run `R` is over the cells of `(q, ., ., S, d)`: the same bases and stride, the offsets split
    differently between the product and the run."""
    Rq, _, _, S2, d2 = R
    return Rq[0] == q[0] and Rq[2] == q[2] and S2 == S and Rq[1] + d2 == q[1] + d


def _idxDec(i):
    if i[0] == 'num': return ('num', i[1] - 1) if i[1] >= 1 else None
    return ('ex', i[1], i[2] - 1) if i[2] >= 1 else None


def runExt(I, inf, i, r2, A):
    """A run from `0` one stride past a known run that starts at its second point, its first point
    known (a row of a triangle, its first pair written last, the rest by a loop): the residual
    `Res.sub` with no value fact, the run inside the known run and the point."""
    q, lo, hi, S, d = r2
    if lo != ('num', 0) or S < 1: return False
    hm = _idxDec(hi)
    if hm is None or not A.covered(shift(q, d)): return False
    for R in sorted(A.r, key=str):
        if R[1] == ('num', 0) and R[2] == hm and _sameCells(R, q, S, d + S):
            inf.addRes(i, ('sub', r2, [R, (q, ('num', 0), ('num', 1), S, d)])); A.r.add(r2)
            APPLIED.setdefault('runExt', set()).add(inf.f['name'])
            return True
    return False


def rowCopy(I, inf, i, r2, A):
    """A run of stride 1 from `0` up to frame cell `m`'s exponent inside the known pairs of a row:
    two runs of stride 2 from `0` up to one exponent `e(h)`, at offsets 0 and 1, and the two points
    past them if known (`verify_bus_gkr`'s zeta, copied from the point triangle's last row): the
    residual `Res.sub`, `e(m) <= 2 e(h)`, plus 2 with the points."""
    q, lo, hi, S, d = r2
    if lo != ('num', 0) or S != 1 or hi[0] != 'ex' or hi[2] != 0 or hi[1][0] != 'fr': return False
    by = {}
    for R in A.r:
        if R[1] == ('num', 0) and R[2][0] == 'ex' and R[2][2] == 0 and R[3] == 2:
            for t in (0, 1):
                if _sameCells(R, q, 2, d + t): by.setdefault(R[2], {})[t] = R
    for h, Rs in sorted(by.items(), key=str):
        if len(Rs) != 2: continue
        bs = [Rs[0], Rs[1]]
        x = h[1]
        for t in (0, 1):
            P = shift(mul(q, (0, 0, ((x, 2),))), d + t)
            if A.covered(P): bs.append((P, ('num', 0), ('num', 1), 1, 0))
        inf.addRes(i, ('sub', r2, bs)); A.r.add(r2)
        APPLIED.setdefault('rowCopy', set()).add(inf.f['name'])
        return True
    return False


def exitRows(I, n, sig, res):
    """A loop's growing row, its run `(q·x^E, [0, e(x) + c), S, d)` over the counter `x` (`E >= 2`: a
    row a step), known at every return, and the point past it: as guarantees over the bound `b`
    (`x·g = b` at the exit, which the walk learns from the exit test): `(q·b^E·g^-E, [0, e(b) + c - 1),
    S, d)` (`postR`) and the point (`post`). Kept if the loop walks with them."""
    f = I['fns'][n]
    if n not in I['isloop']: return False
    b = I['BOUND'].get(n)
    if b is None or b[0] != 'ex' or b[2] != 0 or b[1][0] != 'fr': return False
    try: w = _walk(I, n, sig, res, True)
    except Fail: return False
    if not w.rets: return False
    x = ('fr', 2)

    def up(m):
        E = dict(m[2]).get(x, 0)
        return (m[0], m[1] - E, tuple(sorted([(c, e) for c, e in m[2] if c != x] + [(b[1], E)])))
    addR, addP = [], []
    for R in sorted(w.rets[0].r, key=str):
        q, lo, hi, S, d = R
        if lo != ('num', 0) or hi[0] != 'ex' or hi[1] != x or hi[2] < 1 or dict(q[2]).get(x, 0) < 2: continue
        if not all(R in A.r for A in w.rets[1:]): continue
        R2 = (up(q), lo, ('ex', b[1], hi[2] - 1), S, d)
        if not I['ifaceMono'](f, R2[0]) or R2 in sig.postR: continue
        addR.append(R2)
        P = shift(mul(q, (0, 0, ((x, S),))), S * hi[2] + d)
        if all(A.covered(P) for A in w.rets) and up(P) not in sig.post: addP.append(up(P))
    if not addR: return False
    old = (list(sig.postR), list(sig.post))
    sig.postR.extend(addR); sig.post.extend(addP)
    try:
        _walk(I, n, sig, res)
        APPLIED.setdefault('exitRows', set()).add(n)
        return True
    except Fail:
        sig.postR, sig.post = old
        return False


def armFirst(inf, k, i, A):
    """A table call's arm reading `Q·y·g^c`, `y` bases past a known run `(Q, [0, e(n)), 1, 0)` (`verify_tables`'
    `block_selector`, reading `zeta1·kappa` and the offset's bits over the `mu - kappa` arms): the run over
    `Q·y` below the selector inside it (`Res.sub`, `armSub`'s first shape), `e(y) + e(sel) <= e(n)`; the
    run whose bound the code divides by the selector's word first. Not a read at `Q·g^c` itself, which a
    run up to the selector over `Q` does not contain unless the run's bound is the selector's."""
    x = inf.w.cursel
    if x is None or k[0] != 0 or len(k[2]) < 2: return False
    cands = []
    for R in sorted(A.r, key=str):
        Q, lo, hi, S, d = R
        if lo != ('num', 0) or S != 1 or d != 0 or Q[1] != 0 or not Q[2] or Q[2] == k[2]: continue
        rest = dict(k[2])
        if not all(rest.get(b, 0) >= e for b, e in Q[2]): continue
        div = x[0] == 'fr' and hi[0] == 'ex' and hi[1][0] == 'fr' and divides(inf.f, x[1], hi[1][1])
        cands.append((not div, R))
    if not cands: return False
    R = min(cands, key=lambda t: (t[0], str(t[1])))[1]
    a = ((0, 0, k[2]), ('num', 0), ('ex', x, 0), 1, 0)
    inf.addRes(i, ('sub', a, [R])); A.r.add(a)
    APPLIED.setdefault('armFirst', set()).add(inf.f['name'])
    return True


def armRun(inf, k, i, A):
    """A table call's arm reading a constant point `Q·g^c` of a known run `(Q, [0, e(n)), 1, 0)` whose bound is
    not the selector (`verify_tables`' `padding_weight` arms, arm `tau` reading `zeta[..tau)`, `zeta` known up
    to the bus depth): the run over `Q` up to the selector inside it (`Res.sub`, `subBound`), `e(sel) <= e(n)`
    (every table's tau at most the zerocheck's depth, at most the bus depth); kept if it holds the point."""
    x = inf.w.cursel
    if x is None or k[0] != 0 or len(k[2]) != 1 or k[2][0][1] != 1: return False
    q = (0, 0, k[2])
    a = (q, ('num', 0), ('ex', x, 0), 1, 0)
    ps = I_PARAMS[0](inf.f) if I_PARAMS else set()
    # runs up to a parameter's exponent only: one up to a loaded word (an earlier arm meet's, up to another
    # table's log) bounds nothing here
    Rs = [R for R in A.r if R[0] == q and R[1] == ('num', 0) and R[3] == 1 and R[4] == 0 and R[2][0] == 'ex' and
          R[2][1][0] == 'fr' and R[2][1][1] in ps]
    # a run up to the selector itself: nothing to add
    if any(R[2][1] == x for R in Rs): return False
    # none over `Q`, the selector and `Q` parameters (`plus_one_run`'s arms on the bus depth): that run, a
    # precondition (which `seedRuns` then starts from)
    if not Rs and x[0] == 'fr' and x[1] in ps and k[2][0][0][0] == 'fr' and k[2][0][0][1] in ps:
        A.r.add(a)
        if not A.covered(k):
            A.r.discard(a); return False
        if a not in inf.preR: inf.preR.add(a); inf.new = True
        APPLIED.setdefault('armRun', set()).add(inf.f['name'])
        return True
    for R in sorted(Rs, key=str):
        Q, lo, hi, S, d = R
        new = a not in A.r
        A.r.add(a)
        if not A.covered(k):
            if new: A.r.discard(a)
            return False
        inf.addRes(i, ('sub', a, [R]))
        APPLIED.setdefault('armRun', set()).add(inf.f['name'])
        return True
    return False


# a loaded exponent bounding a run inside a known run of constant length is below it (`ltCover`)
LT_COVER_MIN = 64


def ltCover(I, inf, i, r2, A):
    """A run up to a loaded word's exponent, `(Q, [lo, e(b) + c), S, d)`, inside a known run over `Q` up to a
    constant `N >= LT_COVER_MIN` (`verify_sub`'s `g_squares` table, read by `verify_tables` up to the bus
    depth): the residual `Res.lt`, `e(b) < N - c` (the depth at most `MU_CAP`)."""
    q, lo, hi, S, d = r2
    if hi[0] != 'ex' or hi[1][0] != 'hp': return False
    for R in sorted(A.r, key=str):
        Rq, Rlo, Rhi, S2, d2 = R
        if Rq != q or S2 != S or d2 != d or Rhi[0] != 'num' or Rhi[1] < LT_COVER_MIN + hi[2] or not A.le(Rlo, lo): continue
        r = ('lt', ('ex', hi[1], 0), ('num', Rhi[1] - hi[2]))
        if not inf.w.idxOk(A, r[1]): continue
        new = (r[1], r[2]) not in A.lt
        A.lt.add((r[1], r[2]))
        if not A.coveredR(r2):
            if new: A.lt.discard((r[1], r[2]))
            continue
        inf.addRes(i, r)
        APPLIED.setdefault('ltCover', set()).add(inf.f['name'])
        return True
    return False


def ptsLt(I, inf, i, r2, A):
    """A run from a constant up to a loaded word's exponent, `(Q, [l, e(b) + c), S, d)`, whose points from `l`
    up to some `N <= 64` are known (`check_opening_terminal`'s `point1` up to the zerocheck's, the bus's,
    the memory's and the stack's depths, which every `open_stacked` arm returns written over
    `SIZE_BITS + SLOT_LOG` cells): the residual `Res.lt`, `e(b) + c <= N`."""
    q, lo, hi, S, d = r2
    if hi[0] != 'ex' or hi[1][0] != 'hp' or lo[0] != 'num' or S <= 0: return False
    n = lo[1]
    while n < 64 and A.covered(shift(q, S * n + d)): n += 1
    if n <= lo[1] or n - hi[2] + 1 <= 0: return False
    r = ('lt', ('ex', hi[1], 0), ('num', n - hi[2] + 1))
    if not inf.w.idxOk(A, r[1]): return False
    new = (r[1], r[2]) not in A.lt
    A.lt.add((r[1], r[2]))
    if not A.coveredR(r2):
        if new: A.lt.discard((r[1], r[2]))
        return False
    inf.addRes(i, r)
    APPLIED.setdefault('ptsLt', set()).add(inf.f['name'])
    return True


def headPoint(I, inf, k, i, A):
    """A cell `Q·g^c` of a known run `(Q, [0, e(b) + c'), S, d)` (`c = S j + d`) whose bound no fact places past
    `j` (`verify_sub`'s `z_vals` at the Keccak input point's coordinate `6`, inside the run up to `tau + 6`;
    `verify_sub`'s `zeta`, from the bus GKR up to its depth, read at its first coordinates): the
    residual `Res.lt`, `j < e(b)` (the depth at least `BUS_MIN_MU`)."""
    if k[0] != 0 or not k[2]: return False
    # the run whose product's offset is nearest the cell's first (the Keccak input point before `z_vals`)
    for R in sorted(A.r, key=lambda R: (-R[0][1], str(R))):
        Q, lo, hi, S, d = R
        if Q[0] != 0 or Q[2] != k[2] or lo != ('num', 0) or hi[0] != 'ex' or hi[2] < 0 or S < 1: continue
        off = k[1] - Q[1] - d
        if off < 0 or off % S or not hi[2] <= off // S < 64: continue
        # `j < e(b) + c` as `j - c < e(b)`
        r = ('lt', ('num', off // S - hi[2]), (hi[0], hi[1], 0))
        if not inf.w.idxOk(A, hi): continue
        new = (r[1], r[2]) not in A.lt
        A.lt.add((r[1], r[2]))
        if A.covered(k):
            inf.addRes(i, r)
            APPLIED.setdefault('headPoint', set()).add(inf.f['name'])
            return True
        if new: A.lt.discard((r[1], r[2]))
    return False


def retIdx(I, n, sig, res):
    """A run over the interface up to a returned word's exponent, `(Q, lo, e(r) + c, S, d)`, known at every
    return (`verify_tables`' `chi`, filled up to the zerocheck's `g_zc_n`, which it returns): a guarantee
    (`postR`) up to the return cell's exponent, the walk reading the cell's word at the return. Kept if
    the function walks."""
    f = I['fns'][n]
    if n in I['isloop'] or not f.get('nret'): return False
    try: w = _walk(I, n, sig, res, True)
    except Fail: return False
    if not w.rets: return False
    rc = list(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f['nret']))
    add = []
    A0 = w.rets[0]
    for R in sorted(A0.r, key=str):
        q, lo, hi, S, d = R
        if hi[0] != 'ex' or I['ifaceIdx'](f, hi) or not I['okIface'](f, q) or not I['ifaceIdx'](f, lo): continue
        for o in rc:
            if all(A.mono(o) == (0, 0, ((hi[1], 1),)) for A in w.rets):
                R2 = (q, lo, ('ex', ('fr', o), hi[2]), S, d)
                if R2 not in sig.postR and all(R in A.r for A in w.rets[1:]): add.append(R2)
                break
    if not add: return False
    old = list(sig.postR)
    sig.postR = sorted(old + add)
    try:
        _walk(I, n, sig, res)
        APPLIED.setdefault('retIdx', set()).add(n)
        return True
    except Fail:
        sig.postR = old
        return False


def soleBound(I, inf, i, r2, A):
    """A run up to a loaded word's exponent inside the one known run over the same product, stride and
    offset that ends at another exponent (`verify_sub`'s `chi` up to the KECCAK table's tau, inside
    `chi` up to the zerocheck's `g_zc_n`, which `verify_tables` returns): the residual `Res.sub` (its
    `subBound` family), `e(x) + c <= e(y) + c'` (every tau at most the zerocheck's depth)."""
    q, lo, hi, S, d = r2
    if hi[0] != 'ex' or hi[1][0] != 'hp': return False
    cands = [R for R in A.r if R[0] == q and R[3] == S and R[4] == d and R[2][0] == 'ex' and R[2][1] != hi[1]
             and A.le(R[1], lo)]
    if len(cands) != 1: return False
    inf.addRes(i, ('sub', r2, cands)); A.r.add(r2)
    APPLIED.setdefault('soleBound', set()).add(inf.f['name'])
    return True


ORD = 2 ** 64 - 1  # g's order: an immediate `g^-k` is named `g^(k (2^64 - 2))`


def shiftOf(I, f, c):
    """Frame cell `c` written as a parameter's word times an immediate `g^-t` (`t <= 64`), as the code's `MUL`
    has it: (that parameter's base, `-t`)."""
    sets = {a[0]: a[1] for op, a in f['ops'] if op == 'set' and a[2] == 0}
    for op, a in f['ops']:
        if op != 'mul' or a[2] != c: continue
        for p, k in ((a[0], a[1]), (a[1], a[0])):
            if p in I['params'](f) and k in sets:
                t = I['Infer'].invShift(None, sets[k])
                if t is not None: return ('fr', p), -t
    return None


def retShift(I, n, sig, res):
    """A run of stride 1 from `0` up to a frame cell's exponent, its word `b·g^-k` (`b` over the interface),
    known at every return (`verify_keccak`'s `z_vals·g^4` up to `pack_g = tau_g·INV_GEN^4`): the same cells
    as a run over the interface from `k` up to `e(b)` (`Res.sub` at each return, `e(pack) = e(tau) - 4`
    from the code's own product), a guarantee (`postR`). Kept if the function walks."""
    f = I['fns'][n]
    if n in I['isloop'] or not f.get('nret'): return False
    # a walk only where the code has such a cell
    if not any(op == 'mul' and shiftOf(I, f, a[2]) is not None for op, a in f['ops']): return False
    try: w = _walk(I, n, sig, res, True)
    except Fail: return False
    if not w.rets: return False
    add = []
    # a run some return knows, every other knowing it too or entailing it empty (a loop of no iteration)
    for R in sorted({R for A in w.rets for R in A.r}, key=str):
        q, lo, hi, S, d = R
        if lo != ('num', 0) or S != 1 or hi[0] != 'ex' or hi[2] != 0 or hi[1][0] != 'fr' or I['ifaceIdx'](f, hi): continue
        bk = shiftOf(I, f, hi[1][1])
        if bk is None: continue
        bb, K = bk
        if q[1] + K + d < 0: continue
        R2 = ((q[0], q[1] + K, q[2]), ('num', -K), ('ex', bb, 0), 1, d)
        if not I['okIface'](f, R2[0]) or not I['ifaceIdx'](f, R2[2]) or R2 in sig.postR: continue
        if not all(A.coveredR(R) for A in w.rets): continue
        add.append((R2, R))
    if not add: return False
    old = (list(sig.postR), {k: list(v) for k, v in res.items()})
    for R2, R in add:
        sig.postR.append(R2)
        for i in w.retAt: res.setdefault(i, []).append(('sub', R2, [R]))
    try:
        _walk(I, n, sig, res)
        APPLIED.setdefault('retShift', set()).add(n)
        return True
    except Fail:
        sig.postR = old[0]; res.clear(); res.update(old[1])
        return False


def ptsTile(I, inf, i, r2, A):
    """A run of stride 1 from `0` up to `e(b) + c` over `Q`: the known run `(Q, [s, e(b)), 1, 0)`, its `s`
    points below and the `c` points `Q·b·g^j` past it (`verify_sub`'s `z_vals`, which `verify_keccak` fills
    as the pack coordinates, the copied run and the output slot): the residual `Res.sub`, no value fact."""
    q, lo, hi, S, d = r2
    if lo != ('num', 0) or S != 1 or d != 0 or hi[0] != 'ex' or not 0 < hi[2] <= 64: return False
    b = hi[1]
    for R in sorted(A.r, key=str):
        if R[0] != q or R[3] != 1 or R[4] != 0 or R[1][0] != 'num' or R[2] != (hi[0], b, 0): continue
        s0 = R[1][1]
        if s0 > 64 or not all(A.covered(shift(q, j)) for j in range(s0)): continue
        qb = mul(q, (0, 0, ((b, 1),)))
        if not all(A.covered(shift(qb, j)) for j in range(hi[2])): continue
        bs = ([(q, ('num', 0), ('num', s0), 1, 0)] if s0 else []) + [R, (qb, ('num', 0), ('num', hi[2]), 1, 0)]
        inf.addRes(i, ('sub', r2, bs)); A.r.add(r2)
        APPLIED.setdefault('ptsTile', set()).add(inf.f['name'])
        return True
    return False


# consecutive points past a return cell stated as one run from this many on (`retRun`)
RET_RUN_MIN = 8


def retRun(I, n, sig, res):
    """The cells past a return cell that `retCells` states as points (`post`), `0..j` consecutive, as one
    run over the return cell (`postR`): one fact for the caller's state instead of `j` (`da_expand`'s
    blocks, `256` each, `da_weights` holding `128`). Kept if the function walks."""
    if n in I['isloop']: return False
    by = {}
    for m in sig.post:
        if m[0] == 0 and len(m[2]) == 1 and m[2][0][1] == 1 and m[2][0][0][0] == 'fr': by.setdefault(m[2][0][0], set()).add(m[1])
    rm, add = set(), []
    for b, ds in sorted(by.items()):
        j = 0
        while j in ds: j += 1
        if j < RET_RUN_MIN: continue
        rm |= {(0, d, ((b, 1),)) for d in range(j)}
        add.append(((0, 0, ((b, 1),)), ('num', 0), ('num', j), 1, 0))
    if not add: return False
    old = (list(sig.post), list(sig.postR))
    sig.post = [m for m in old[0] if m not in rm]
    sig.postR = sorted(old[1] + [r for r in add if r not in old[1]])
    try:
        _walk(I, n, sig, res)
        APPLIED.setdefault('retRun', set()).add(n)
        return True
    except Fail:
        sig.post, sig.postR = old
        return False


def runPreLo(I, inf, k, i0, A):
    """A table read below the table's start, `k = Q·b^e·g^c` with `c < 0`, where `Infer.key` would ask for the run
    from index `0` (`runPre`, or up to an interface bound) (`log2_ceil_in_the_exponent`'s
    `g_squares[g_log·INV_GEN]`, read only when `g_log != g^floor`): the run from the first index whose cell is
    in the table, `(Q, [m, N), e, c)`, `m = ceil(-c / e)`, and the residual `Res.lt`, `m - 1 < e(b)` (the
    exponent above the floor on that branch)."""
    f = inf.f
    c = k[1] - ORD if k[1] > ORD // 2 else k[1]  # `g^-t` is named `g^(ORD - t)`
    if k[0] != 0 or c >= 0 or A.covered(k): return False
    for b, e in k[2]:
        Q = (0, 0, tuple(x for x in k[2] if x[0] != b))
        nb = A.bound(('ex', b, 1))
        if e < 1 or nb is None or not 0 < nb <= 64 or not Q[2] or not I['ifaceMono'](f, Q): continue
        m = -(c // e)
        if m >= nb: continue
        lt = ('lt', ('num', m - 1), ('ex', b, 0))
        r = (Q, ('num', m), ('num', nb), e, k[1])
        new = (lt[1], lt[2]) not in A.lt
        A.lt.add((lt[1], lt[2])); A.r.add(r)
        if not A.covered(k):
            A.r.discard(r)
            if new: A.lt.discard((lt[1], lt[2]))
            continue
        inf.addRes(i0, lt)
        if r not in inf.preR: inf.preR.add(r); inf.new = True
        APPLIED.setdefault('runPreLo', set()).add(f['name'])
        return True
    return False


def ordSub(I, inf, i, r2, A):
    """A run between constants at an offset `g^-t` (named `g^(ORD - t)`), its first cell at or past the product
    (`log2_ceil_in_the_exponent`'s `g_squares[g_log·INV_GEN]`, from index `1`, which `verify_sub` passes up to
    `main`): inside a known run over the same product from offset `0` (`Res.sub`, `g^ORD = 1`)."""
    q, lo, hi, S, d = r2
    if lo[0] != 'num' or hi[0] != 'num' or d <= ORD // 2 or S < 1: return False
    c = S * lo[1] + d - ORD
    if c < 0: return False
    R1 = (q, ('num', 0), ('num', hi[1] - lo[1]), S, c)
    for R in sorted(A.r, key=str):
        if R[0] == q and R[3] in (1, S) and R[4] == 0 and R[1][0] == 'num' and A.coveredR(R1):
            Q, lo2, hi2, S2, d2 = R
            b = A.bound(hi2)
            if b is None or S2 * lo2[1] > c or S2 * b < c + S * (hi[1] - lo[1] - 1) + 1: continue
            if S2 != 1 and c % S2: continue
            inf.addRes(i, ('sub', r2, [R])); A.r.add(r2)
            APPLIED.setdefault('ordSub', set()).add(inf.f['name'])
            return True
    return False


def extHead(I, inf, k, i, A):
    """A cell past a known run's end, `(Q, [l, e(n) + c), S, d)`, the run's next point `Q·n^S·g^(S c + d)`
    known (`main`'s `da_digests`: the children's digests by the child loop, then this node's own at
    `n_children^2`, read at the hinted `da_pick <= n_children`): the run one point longer, the residual
    `Res.sub` (the run and the point), no value fact; kept if it covers the cell."""
    if k[0] != 0 or len(k[2]) < 2: return False
    bs = set(k[2])
    cand = [R for R in A.r if R[2][0] == 'ex' and R[0][0] == 0 and R[3] >= 1 and R[0][2] and
            len(R[0][2]) < len(k[2]) and bs.issuperset(R[0][2])]
    if not cand or A.covered(k): return False
    for R in sorted(cand, key=str):
        q, lo, hi, S, d = R
        pt = shift(mul(q, (0, 0, ((hi[1], S),))), S * hi[2] + d)
        if not A.covered(pt): continue
        R2 = (q, lo, (hi[0], hi[1], hi[2] + 1), S, d)
        if R2 in A.r: continue
        A.r.add(R2)
        if not A.covered(k):
            A.r.discard(R2); continue
        inf.addRes(i, ('sub', R2, [R, (pt, ('num', 0), ('num', 1), 1, 0)]))
        APPLIED.setdefault('extHead', set()).add(inf.f['name'])
        return True
    return False


def mulShifts(I, f, c):
    """Frame cell `c` written as another cell's word times an immediate `g^-t` (`t <= 64`), as the code's `MUL`s
    have it: each (that cell, `t`)."""
    sets = {a[0]: a[1] for op, a in f['ops'] if op == 'set' and a[2] == 0}
    out = []
    for op, a in f['ops']:
        if op != 'mul' or a[2] != c: continue
        for u, k in ((a[0], a[1]), (a[1], a[0])):
            if k in sets:
                t = I['Infer'].invShift(None, sets[k])
                if t is not None: out.append((u, t))
    return out


def selShift(I, inf, i, r2, A):
    """A run up to a word's exponent, `(Q, [l, e(b) + c), S, d)`, inside a known run up to a cell `x` the code
    computes as `b·g^-t`, `(Q, [l', e(x) + c'), S, d)` with `c + t <= c'` (`verify_sub`'s `ood_z` and `point1`,
    which the `size_sel` table call's arms fill up to `e(size_sel) + LIG_MIN_LOG_SIZE`, read up to the stack's
    `e(gmv)`, `size_sel = gmv·LIG_MIN_SHIFT_INV`): the residual `Res.sub`, `e(x) = e(b) - t` from the `MUL`."""
    q, lo, hi, S, d = r2
    if hi[0] != 'ex': return False
    for R in sorted(A.r, key=str):
        if R[0] != q or R[3] != S or R[4] != d or R[2][0] != 'ex' or R[2][1] == hi[1] or R[2][1][0] != 'fr' or \
                not A.le(R[1], lo):
            continue
        for u, t in mulShifts(I, inf.f, R[2][1][1]):
            if A.mono(u) != (0, 0, ((hi[1], 1),)) or hi[2] + t > R[2][2]: continue
            inf.addRes(i, ('sub', r2, [R])); A.r.add(r2)
            APPLIED.setdefault('selShift', set()).add(inf.f['name'])
            return True
    return False


# `infer.params`, set by `install`
I_PARAMS = []

# the runs an inference starts from (`seedRuns`), by function, and each try's outcome
SEED = {}
SEEDLOG = {}
# pre points over one product, at least this many, worth a second inference (`seedRuns`)
SEED_MIN = 8


def seedRuns(I, n, named, sig, res, infer1):
    """A run over a parameter's buffer up to a parameter's exponent among the preconditions (`preR`), and
    many constant points over the same buffer among them (`pre`), which reads before the run's demand added
    (`verify_tables`' `padding_weight` arms read `zeta[..tau)` before `plus_one_run` asks for `zeta` up to
    the bus depth): the inference again from those runs, `armRun` then placing the arms' reads inside
    them. The same for any run of constant length over that buffer (`preR`): an arm reached first on a
    path that bounds a base of its read's product (`shared_selector_tables`' arms past a skipped loop,
    `q = 1`) asks for `Q·g^c` unconditionally, where from the run `armFirst` places it inside the run up to
    the selector. Kept if it walks with fewer points and constant runs over those buffers."""
    if n in I['isloop'] or n in SEED: return None
    pts = {}
    for m in sig.pre:
        if m[0] == 0 and len(m[2]) == 1 and m[2][0][1] == 1: pts.setdefault(m[2], []).append(m)
    ps = I['params'](I['fns'][n])

    def consts(s, qs):
        return sum(1 for R in s.preR if R[0][1] == 0 and R[0][2] in qs and R[1] == ('num', 0) and R[2][0] == 'num')

    def isRun(R):
        return R[1] == ('num', 0) and R[3] == 1 and R[4] == 0 and R[2][0] == 'ex' and R[2][1][0] == 'fr' and \
            R[0][1] == 0

    seeds = {R for R in sig.preR if isRun(R) and
             (len(pts.get(R[0][2], [])) >= SEED_MIN or (R[2][1][1] in ps and consts(sig, {R[0][2]})))}
    if not seeds: return None
    qs = {R[0][2] for R in seeds}
    SEED[n] = seeds
    try:
        sig2, res2 = infer1(n, named)
    except Fail as e:
        SEEDLOG[n] = ('fail', str(e.args[0][:3])[:300])
        del SEED[n]; return None
    c1, c2 = consts(sig, qs), consts(sig2, qs)
    SEEDLOG[n] = (len(sig.pre), len(sig2.pre), c1, c2)
    if len(sig2.pre) > len(sig.pre) or len(sig2.pre) + c2 >= len(sig.pre) + c1:
        del SEED[n]; return None
    APPLIED.setdefault('seedRuns', set()).add(n)
    return sig2, res2


# arm name -> (the runs its inference starts from, its residuals at offset 0, the parameter products they are
# over) (`armForm`)
ARMSEED = {}
ARMFORM_DBG = __import__('os').environ.get('ARMFORM_DBG')


def _armCells(r):
    """A run between constants' cell offsets past its product (`None` if a bound is not a constant)."""
    q, lo, hi, S, d = r
    if lo[0] != 'num' or hi[0] != 'num': return None
    return [q[1] + S * j + d for j in range(lo[1], hi[1])]


def _shifted(q, lo, hi, S, d):
    """The same cells, the run's index one up and its offset `S` down (named `g^(ORD - S + d)`)."""
    return (q, (lo[0], lo[1] + 1) if lo[0] == 'num' else (lo[0], lo[1], lo[2] + 1),
            (hi[0], hi[1] + 1) if hi[0] == 'num' else (hi[0], hi[1], hi[2] + 1), S, ORD - S + d)


def armForm(I, n, sig, res):
    """A table call's arm `j` reading cells of a parameter's buffer below `S·j`, which its caller holds only as
    `S` runs of stride `S` up to the selector's exponent, `(Q, [0, e(x)), S, ρ)` for each `ρ < S`
    (`verify_tables`' shared selector tables, read by the `block_selector_tab` arms), each cell a lookup per arm:
    the arm's preconditions over that buffer as `S` runs `(P, [1, m + 1), S, ORD - S + ρ)`, the cells
    `P·g^(S·i + ρ)` for `i < m`, `S·m` past the last cell it reads, its residuals `Res.sub` at its entry naming
    them from `0`, `(P, [0, m), S, ρ)`; the caller's residuals `Res.sub` at the call naming its runs the same way,
    `(Q, [1, e(x) + 1), S, ORD - S + ρ)`, which hold the arm's at once (`Abs.coveredR`'s containment: `m <= j`
    from the selector's exponent `j`, `j < e(x) + 1`). The arm's guarantees over those buffers dropped (it only
    reads them). Kept if the arms and the caller walk."""
    f = I['fns'][n]
    if not f['tabs']: return False
    Walk = I['Walk']; fns = I['fns']; byentry = I['byentry']
    seen = {}
    oe = Walk.entryOk

    def entryOk(w, A, mq, G, i, name):
        if w.cursel is not None and G.pc in byentry: seen.setdefault((i, G.pc), (A, mq, w, w.cursel))
        return oe(w, A, mq, G, i, name)
    Walk.entryOk = entryOk
    try:
        _walk(I, n, sig, res)
    except Fail as e:
        if ARMFORM_DBG: print('armForm: walk fails', str(e.args[0][:3])[:300])
        return False
    finally:
        Walk.entryOk = oe
    want = {}; cres = {}
    for (i, pc), (A, mq, w, x) in sorted(seen.items(), key=str):
        a = byentry[pc]['name']
        if a in I['isloop'] or any(a in I['calls'][y] for y in I['calls'] if y != n): continue
        G = I['E'].sigs[pc]
        if a in ARMSEED: G = None
        by = {}
        for r in (G.preR if G else []):
            q = r[0]
            if r[3] != 1 or q[0] != 0 or len(q[2]) != 1 or q[2][0][1] != 1 or q[2][0][0][0] != 'fr': continue
            cs = _armCells(r)
            if cs is None: continue
            by.setdefault((0, 0, q[2]), []).append(cs)
        for m in (G.pre if G else []):
            if m[0] == 0 and len(m[2]) == 1 and m[2][0][1] == 1 and (0, 0, m[2]) in by: by[(0, 0, m[2])].append([m[1]])
        if G is None:
            seeds, rs0, Ps = ARMSEED[a]; got = True
            for r in seeds:
                c2 = w.trRngDown(A, mq, r)
                R = (c2[0], ('num', 0), ('ex', x, 0), c2[3], c2[4] - ORD + c2[3]) if c2 else None
                if R is None or R not in A.r: got = False; break
                cres.setdefault(i, set()).add(('sub', _shifted(*R), (R,)))
            if not got and ARMFORM_DBG: print('armForm: seeded arm not held', i, a)
            continue
        seeds = set(); rs0 = []; Ps = set()
        for P, xs in by.items():
            Q = w.trMono(A, mq, P)
            if Q is None: continue
            Ss = sorted({R[3] for R in A.r if R[0] == Q and R[3] >= 2 and R[1] == ('num', 0) and R[2] == ('ex', x, 0)})
            top = max(c for cs in xs for c in cs)
            j = None
            for p_, q_ in A.lt:
                if q_ == ('ex', x, 1) and p_[0] == 'num': j = p_[1] if j is None else max(j, p_[1])
            for S in Ss:
                m = top // S + 1
                if j is None or m > j: continue
                Rs = [(Q, ('num', 0), ('ex', x, 0), S, rho) for rho in range(S)]
                if not all(R in A.r for R in Rs): continue
                for rho, R in enumerate(Rs):
                    seeds.add(_shifted(P, ('num', 0), ('num', m), S, rho))
                    rs0.append(('sub', (P, ('num', 0), ('num', m), S, rho), [_shifted(P, ('num', 0), ('num', m), S, rho)]))
                    cres.setdefault(i, set()).add(('sub', _shifted(*R), (R,)))
                Ps.add(P)
                break
        if seeds: want[a] = (frozenset(seeds), rs0, frozenset(Ps))
        if ARMFORM_DBG: print('armForm:', i, a, len(by), len(seeds))
    if not want and not cres: return False
    old = {a: (ARMSEED.get(a), I['LAST'].get(a), I['E'].sigs[fns[a]['entry']]) for a in want}
    oldres = {k: list(v) for k, v in res.items()}
    try:
        for a, sd in sorted(want.items()):
            ARMSEED[a] = sd
            G = I['infer'](a)[0]
            if not set(G.preR) <= sd[0]: raise Fail(('armForm', a, sorted(set(G.preR) - sd[0], key=str)[:3]))
        # the caller's residuals, each at the first call needing it
        done = set()
        for i in sorted(cres):
            for r in sorted(cres[i], key=str):
                if r[1] in done: continue
                done.add(r[1])
                r = ('sub', r[1], list(r[2]))
                if r not in res.setdefault(i, []): res[i].append(r)
        try:
            _walk(I, n, sig, res)
        except Fail:
            # at every call
            for i in sorted(cres):
                for r in sorted(cres[i], key=str):
                    r = ('sub', r[1], list(r[2]))
                    if r not in res[i]: res[i].append(r)
            _walk(I, n, sig, res)
    except Fail as e:
        if ARMFORM_DBG: print('armForm: fails after', str(e.args[0][:4])[:400])
        for a, (s0, l0, g0) in old.items():
            if s0 is None: ARMSEED.pop(a, None)
            else: ARMSEED[a] = s0
            if l0 is not None: I['LAST'][a] = l0
            I['E'].sigs[fns[a]['entry']] = g0
        res.clear(); res.update(oldres)
        return False
    APPLIED.setdefault('armForm', set()).add(n)
    return True


def armShift(I, inf, i, r2, A):
    """A table call's arm's precondition `armForm` gave, `(Q, [l, m), S, ORD - S + ρ)`, `l >= 1`, the caller
    holding `(Q, [0, e(x)), S, ρ)` up to the selector `x`: the residual `Res.sub` naming that run so,
    `(Q, [1, e(x) + 1), S, ORD - S + ρ)` (the same cells), which holds the arm's (a caller inferred again
    after its arms were)."""
    q, lo, hi, S, d = r2
    x = inf.w.cursel if inf.w is not None else None
    if x is None or lo[0] != 'num' or lo[1] < 1 or hi[0] != 'num' or S < 2 or not (ORD - S <= d < ORD): return False
    R = (q, ('num', 0), ('ex', x, 0), S, d - ORD + S)
    if R not in A.r: return False
    a = _shifted(*R)
    A.r.add(a)
    if not A.coveredR(r2):
        A.r.discard(a); return False
    inf.addRes(i, ('sub', a, [R]))
    APPLIED.setdefault('armShift', set()).add(inf.f['name'])
    return True


def armFormPost(n, sig):
    """An arm `armForm` seeded: its guarantees over the buffers it only reads, and those that repeat its
    preconditions, dropped (its caller held them; kept, each would be a fact of the arm's condition at every
    call, `condOf`)."""
    Ps = ARMSEED[n][2]
    pre = set(sig.pre)
    sig.postR = [r for r in sig.postR if (0, 0, r[0][2]) not in Ps and r not in sig.preR and
                 not (r[1][0] == 'num' and r[2][0] == 'num' and
                      all(shift(r[0], r[3] * j + r[4]) in pre for j in range(r[1][1], r[2][1])))]
    sig.post = [m for m in sig.post if (0, 0, m[2]) not in Ps and m not in pre]

def install(I):
    """Hook the rules into `infer.py`'s namespace `I`."""
    Infer = I['Infer']
    I_PARAMS[:] = [I['params']]
    demand = Infer.demand

    def demand2(self, kind, i, *rest):
        if demand(self, kind, i, *rest): return True
        if kind == 'preR':
            name, r, r2, A = rest
            if r2 is not None and not (isinstance(name, tuple) and name[0] == 'tail') and \
                    (boundSub(I, self, i, r2, A) or tileSub(I, self, i, r2, A) or rowCopy(I, self, i, r2, A) or
                     ltCover(I, self, i, r2, A) or soleBound(I, self, i, r2, A) or ptsTile(I, self, i, r2, A) or
                     selShift(I, self, i, r2, A) or ptsLt(I, self, i, r2, A) or ordSub(I, self, i, r2, A)):
                return True
            # a single point (`headPoint`)
            if r2 is not None and not (isinstance(name, tuple) and name[0] == 'tail') and r2[1][0] == 'num' and \
                    r2[2] == ('num', r2[1][1] + 1) and headPoint(I, self, first(r2), i, A):
                return True
            # a loop's tail call too: the next iteration's row from this one's writes
            if r2 is not None and runExt(I, self, i, r2, A): return True
        if kind == 'lnk':
            o, (k, i0), A = rest
            if tabIdx(I, self, k, i0, A) or extHead(I, self, k, i0, A): return True
        if kind == 'pre':
            name, m, k, A = rest
            if k is not None and not (isinstance(name, tuple) and name[0] == 'tail') and \
                    (tabIdx(I, self, k, i, A) or headPoint(I, self, k, i, A) or extHead(I, self, k, i, A)):
                return True
        return False

    def demand3(self, kind, i, *rest):
        # an `armForm` arm's precondition first: `ordSub` would take it for one unconditional run
        if kind == 'preR':
            name, r, r2, A = rest
            if r2 is not None and not (isinstance(name, tuple) and name[0] == 'tail') and armShift(I, self, i, r2, A):
                return True
        # a table call's arm reading inside a run up to the selector (`armSub`) before the cell's own
        # justifications (`Infer.key`), which hold of one arm's reads but not of every arm's
        if kind == 'pre' and self.w is not None and self.w.cursel is not None:
            name, m, k, A = rest
            if k is not None and not (isinstance(name, tuple) and name[0] == 'tail') and (armFirst(self, k, i, A) or armRun(self, k, i, A)):
                return True
        return demand2(self, kind, i, *rest)

    Infer.demand = demand3
    key = Infer.key

    def key2(self, k, i0, A, depth=0):
        if depth == 0 and (runPreLo(I, self, k, i0, A) or extHead(I, self, k, i0, A)): return True
        # a cell at a loaded index inside a run up to an exponent: that run (`runPoint`) before a run
        # between constants an earlier pass's state held, which a later pass may not (`verify_tables`'
        # `zc_peq[tau]` inside `eq_prefix_chain`'s chain)
        if depth == 0 and k[0] == 0 and len(k[2]) >= 2 and any(b[0] == 'hp' for b, e in k[2]) and \
                not A.covered(k) and self.runPoint(k, i0, A):
            APPLIED.setdefault('exPoint', set()).add(self.f['name'])
            return True
        return key(self, k, i0, A, depth)

    Infer.key = key2
    infer1 = I['infer1']

    init = Infer.__init__

    def init2(self, f):
        init(self, f)
        self.preR |= SEED.get(f['name'], set())
        if f['name'] in ARMSEED:
            self.preR |= set(ARMSEED[f['name']][0])
            for r in ARMSEED[f['name']][1]:
                if r not in self.res[0]: self.res[0].append(r)

    Infer.__init__ = init2

    def infer1s(n, named):
        sig, res = infer1(n, named)
        got = seedRuns(I, n, named, sig, res, infer1)
        return got if got is not None else (sig, res)

    def infer1c(n, named):
        armBlocks(I, I['fns'][n])
        sig, res = infer1s(n, named)
        if n in ARMSEED: armFormPost(n, sig)
        retRun(I, n, sig, res)
        exitRows(I, n, sig, res)
        retIdx(I, n, sig, res)
        retShift(I, n, sig, res)
        if not tilePost(I, n, sig, res) and n not in I['STRIDES'] and len(I['fns'][n]['tabs']) == 1 and \
                I['fns'][n].get('nargs', 0) == 2:
            # the rest's arms as strided runs (`armStrides`), then again
            I['STRIDES'].add(n)
            try:
                sig2, res2 = infer1(n, named)
                if tilePost(I, n, sig2, res2): return sig2, res2
            except Fail:
                pass
            I['STRIDES'].discard(n)
            sig, res = infer1(n, named)
        return sig, res

    def infer1f(n, named):
        sig, res = infer1c(n, named)
        armForm(I, n, sig, res)
        return sig, res

    I['infer1'] = infer1f
