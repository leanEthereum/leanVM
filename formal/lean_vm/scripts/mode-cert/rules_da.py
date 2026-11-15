"""Inference rules beside `infer.py`'s, installed into it by `install(globals())`: each extends what a
function's inference finds, and the walks that follow must accept it."""
import walk as W
from walk import Walk, Fail, shift, mul

# the functions each rule extended (a report for the inference's callers)
APPLIED = {}

# cells past a returned word, at most
RET_CAP = 256


def retCells(I, n, sig, res):
    """A returned word the interface cannot name (a pointer into the function's own frame, a `StackBuf`
    returned by address as `da_expand`'s, or a word a callee returned so): the cells past it that every
    return knows written, consecutive from the word, as points over the return cell (`post`), which a loop
    storing the word keeps as a run of pointers with those cells past each. Kept if the function walks."""
    f = I['fns'][n]
    if n in I['isloop']: return
    walk = lambda: Walk(I['E'], f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main')
    w = walk()
    try:
        w.run(f['ops'])
    except Fail:
        return
    if not w.rets: return
    na, nr = f.get('nargs', 0), f.get('nret', 0)
    okIface, renameRet = I['okIface'], I['renameRet']
    ks = []
    for o in range(2 + na, 2 + na + nr):
        ms = [A.mono(o) for A in w.rets]
        if any(m is None or okIface(f, renameRet(f, A, (m[0], 0, m[2]))) for A, m in zip(w.rets, ms)): continue
        if all(m[0] == 0 and not m[2] for m in ms): continue
        j = 0
        while j < RET_CAP and all(A.covered(shift(m, j)) for A, m in zip(w.rets, ms)): j += 1
        ks += [k for k in ((0, d, ((('fr', o), 1),)) for d in range(j)) if k not in sig.post]
    if not ks: return
    old = list(sig.post)
    sig.post = sorted(old + ks)
    try:
        walk().run(f['ops'])
        APPLIED.setdefault('retCells', set()).add(n)
    except Fail:
        sig.post = old


def retRuns(I, n, sig, res):
    """A run over the interface that some return knows and every other entails empty (a loop of no
    iteration on a branch of its own, `da_pad`'s): a guarantee (`postR`). Kept if the function walks."""
    f = I['fns'][n]
    if n in I['isloop']: return
    walk = lambda: Walk(I['E'], f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main')
    w = walk()
    try:
        w.run(f['ops'])
    except Fail:
        return
    if len(w.rets) < 2: return
    ok = lambda r: I['okIface'](f, r[0]) and I['ifaceIdx'](f, r[1]) and I['ifaceIdx'](f, r[2])
    cand = sorted({r for A in w.rets for r in A.r if ok(r)} - set(sig.postR), key=str)
    rs = [r for r in cand if all(A.coveredR(r) for A in w.rets)]
    if not rs: return
    old = list(sig.postR)
    sig.postR = sorted(old + rs)
    try:
        walk().run(f['ops'])
        APPLIED.setdefault('retRuns', set()).add(n)
    except Fail:
        sig.postR = old


# guarantees over one product at least this many runs are merged; a merged run has at most `MERGE_MAX` cells
MERGE_MIN, MERGE_MAX = 24, 4096
# a merge may not double the walk's estimate of a function within this one (`gen.py`'s `XCOST`)
MERGE_COST = 2000000


def mergeRuns(I, n, sig, res):
    """Many guaranteed runs between constants over one product (a table filled in pieces, as
    `da_column_offsets`' doublings): each stretch of consecutive cells they and the points over it cover
    as one run of stride 1, which the return checks cell by cell. Kept if the function walks and its walk
    stays as checkable as it was (`MERGE_COST`)."""
    f = I['fns'][n]
    walk = lambda: Walk(I['E'], f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main')

    def cost():
        c0 = W.COST[0]; W.COST[0] = 0
        try:
            walk().run(f['ops'])
            return W.COST[0]
        finally:
            W.COST[0] += c0
    by = {}
    for r in sig.postR:
        q, lo, hi, S, d = r
        if lo[0] == 'num' and hi[0] == 'num' and q[0] == 0 and q[2]: by.setdefault((0, 0, q[2]), []).append(r)
    old = list(sig.post), list(sig.postR)
    got = False
    before = None
    for Q, rs in by.items():
        if len(rs) < MERGE_MIN: continue
        if before is None:
            try: before = cost()
            except Fail: return
        cs = {r[0][1] + r[3] * j + r[4] for r in rs for j in range(r[1][1], r[2][1])}
        cs |= {m[1] for m in sig.post if m[0] == 0 and m[2] == Q[2]}
        ks = sorted(cs); runs = []; i = 0
        while i < len(ks):
            j = i
            while j + 1 < len(ks) and ks[j + 1] == ks[j] + 1 and ks[j + 1] - ks[i] < MERGE_MAX: j += 1
            runs.append((ks[i], ks[j] + 1)); i = j + 1
        if len(runs) >= len(rs): continue
        inside = lambda c: any(a <= c < b for a, b in runs)
        sig.postR = [r for r in sig.postR if r not in rs] + \
            [(Q, ('num', a), ('num', b), 1, 0) for a, b in runs]
        sig.post = [m for m in sig.post if not (m[0] == 0 and m[2] == Q[2] and inside(m[1]))]
        got = True
    if not got: return
    sig.postR = sorted(sig.postR); sig.post = sorted(sig.post)
    try:
        if before <= MERGE_COST and cost() > 2 * before: raise Fail(('merge cost',))
        APPLIED.setdefault('mergeRuns', set()).add(n)
    except Fail:
        sig.post, sig.postR = old


def retLoads(I, n, sig, res):
    """A return cell loaded from a heap cell over the interface that nothing wrote first (`da_levels`
    returning a one-leaf tree's root): that cell a precondition, so the return cell is written. Kept if
    the function walks."""
    f = I['fns'][n]
    if n in I['isloop']: return
    walk = lambda: Walk(I['E'], f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main')
    w = walk()
    try:
        w.run(f['ops'])
    except Fail:
        return
    if not w.rets: return
    na, nr = f.get('nargs', 0), f.get('nret', 0)
    ks, os = [], []
    for o in range(2 + na, 2 + na + nr):
        if o in sig.ret or any(o in A.w for A in w.rets): continue
        k = w.lnk.get(o, (None,))[0]
        if k is None or k[0] != 0 or not k[2] or not I['ifaceMono'](f, k): break
        ks.append(k); os.append(o)
    else:
        if not ks: return
        old = list(sig.pre), list(sig.ret)
        sig.pre = sorted(set(sig.pre) | set(ks)); sig.ret = sorted(set(sig.ret) | set(os))
        try:
            walk().run(f['ops'])
            APPLIED.setdefault('retLoads', set()).add(n)
        except Fail:
            sig.pre, sig.ret = old


def splitRun(I, inf, i, r2, A):
    """A run between constants over a parameter product `Q` (or one cell of it), the function knowing runs
    over `Q·[x]^S` up to `[y]`'s exponent, `x` a parameter (a table whose second part a callee wrote past
    the first's `[x]` entries, `da_roots_tree`'s padding): inside those and the runs over `Q` up to `[x]`'s
    exponent (`Res.sub`), which are preconditions."""
    f = inf.f
    q, lo, hi, S, d = r2
    if q[0] != 0 or q[1] != 0 or not q[2] or lo[0] != 'num' or hi[0] != 'num' or not I['ifaceMono'](f, q):
        return False
    ps = I['params'](f)
    parts = []
    for R in sorted(A.r, key=str):
        Rq, Rlo, Rhi, S2, d2 = R
        if Rq[0] != 0 or Rq[1] != 0 or Rlo != ('num', 0) or Rhi[0] != 'ex' or Rhi[2] != 0: continue
        for x, e in Rq[2]:
            if x[0] != 'fr' or x[1] not in ps or e != S2: continue
            if mul(q, (0, 0, ((x, S2),))) != Rq: continue
            parts.append((R, (q, ('num', 0), ('ex', x, 0), S2, d2)))
    if not parts: return False
    bs = []
    for R, B in parts:
        if B not in inf.preR: inf.preR.add(B); inf.new = True
        A.r.add(B); bs += [B, R]
    inf.addRes(i, ('sub', r2, bs)); A.r.add(r2)
    APPLIED.setdefault('splitRun', set()).add(f['name'])
    return True


def widePtrs(I, n, sig, res):
    """A run of returned pointers whose pointees every return knows written past the `64` cells
    `ptrRuns` looks at (`da_weights`' weights, `256` each): the cells up to `RET_CAP` (`postP`). Kept
    if the function walks."""
    f = I['fns'][n]
    if n in I['isloop'] or not sig.postP: return
    walk = lambda: Walk(I['E'], f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main')
    try:
        w = walk(); w.run(f['ops'])
    except Fail:
        return
    if not w.rets: return
    renameRet = I['renameRet']
    new = []
    for q, os in sig.postP:
        b, lo, hi, S, d = q
        if len(os) != 64 or lo[0] != 'num' or hi[0] != 'num' or S != 1 or d != 0:
            new.append((q, os)); continue
        m = RET_CAP
        for A in w.rets:
            seen = set()
            for k, x in A.hv.items():
                if x[0] != 'm': continue
                k2 = renameRet(f, A, k)
                if k2[0] != b[0] or k2[2] != b[2] or not lo[1] <= k2[1] < hi[1]: continue
                c = 0
                while c < RET_CAP and A.covered(shift(x[1], c)): c += 1
                m = min(m, c); seen.add(k2[1])
            if len(seen) != hi[1] - lo[1]: m = 0
        new.append((q, tuple(range(m))) if m > len(os) else (q, os))
    if new == list(sig.postP): return
    old = list(sig.postP)
    sig.postP = sorted(new)
    try:
        walk().run(f['ops'])
        APPLIED.setdefault('widePtrs', set()).add(n)
    except Fail:
        sig.postP = old


def install(I):
    """Hook the rules into `infer.py`'s namespace `I`."""
    Infer, infer1 = I['Infer'], I['infer1']
    demand = Infer.demand

    def demand2(self, kind, i, *rest):
        if kind == 'preR':
            name, r, r2, A = rest
            if r2 is not None and not (isinstance(name, tuple) and name[0] == 'tail') and splitRun(I, self, i, r2, A):
                return True
        if kind == 'pre':
            name, m, k, A = rest
            if k is not None and not (isinstance(name, tuple) and name[0] == 'tail') and k[0] == 0 and k[2] and \
                    splitRun(I, self, i, ((0, 0, k[2]), ('num', k[1]), ('num', k[1] + 1), 1, 0), A):
                return True
        return demand(self, kind, i, *rest)

    def infer1b(n, named):
        sig, res = infer1(n, named)
        retRuns(I, n, sig, res)
        retLoads(I, n, sig, res)
        retCells(I, n, sig, res)
        mergeRuns(I, n, sig, res)
        widePtrs(I, n, sig, res)
        return sig, res

    Infer.demand = demand2
    I['infer1'] = infer1b
