"""`heapOkC` (`LeanVM/Guest/CoreMode/HeapC.lean`) in Python, step for step: the check of an emitted certificate before
the kernel sees it, and the pass `emitc.py` solves each witness in (`Solver`: the witness is looked for in the check's
own scope, the inference's choice a hint).

Data as in `CoreMode/Defs.lean`: a cell `(bases, off)`, `bases` a tuple of `(value, exponent)` in `CCell.mul`'s order;
a pass run `(base, stride, lo, hi)`, bounds cells; a signature run `(base, stride, lo, hi)`, bounds `CIdx`
(`('num', n)`, `('val', v)`, `('mono', cell)`); residuals `('lt', a, b)`, `('sub', cell, run)`, `('subR', run, run)`;
witnesses `('ev', n)`, `('pre', k)`, `('run', r, res)`, `('pf', n)`, `('pfr', r, res)`, `('word', m)`, `('pts',)`,
`('empty',)`, `('skip', res)`, `('cat', k)`, `('mrg', S, res)`, `('perm', k, ns)`, `('evs', n, k, res)`, `('back', r, ns, res)`, `('prep', r, q, res)`,
`('prep2', r, q, q2, res)`, `('vp', j, offs)`; residuals also `('subP', cell, cells)`, `('under', conds, r)`. Round 4's last rules (`eqs`/`retEq`,
`ptBack`, `perm`, `prep`, `vp`, `baseFacts`, `log2Ceil` bits, words at return of a dispatch) included.
"""
import collections

CAPE = 2 ** 62
GB = 1 << 20
DB = 1 << 19   # value `DB + k` is the word at the cell `ders[k]` (`HCert.ders`)


# ---- monomials (`CoreMode/Heap.lean`)

def baseC(k):
    return (((k, 1),), 0)


def insB(k, e, l):
    for i, (k2, e2) in enumerate(l):
        if k == k2:
            return l[:i] + ((k, e + e2),) + l[i + 1:]
        if k < k2:
            return l[:i] + ((k, e),) + l[i:]
    return l + ((k, e),)


def mergeB(a, l):
    for k, e in reversed(a):
        l = insB(k, e, l)
    return l


def cmul(a, b):
    return (mergeB(a[0], b[0]), a[1] + b[1])


def cpow(c, e):
    return (tuple((b, x * e) for b, x in c[0]), c[1] * e)


def cshift(c, o):
    return (c[0], c[1] + o)


def tsub(a, b):
    return a - b if a > b else 0


def ndiv(a, b):
    return a // b if b else 0


# ---- signatures and certificates

def gw_def(st, gw, c, d):
    """`CoreMode.gwDef`: `d` read from the cell `c` of an own parameter word `(c, j)` (`HSig.gw`) names ghost `j`; then
    `d`'s monomial."""
    for cg, j in gw:
        if cg == c:
            st.define(d, baseC(GB + j))
            break
    return mono(st.env, d)


class HSig:
    FIELDS = ('pre', 'post', 'preR', 'postR', 'term', 'retM', 'preP', 'postP', 'prePR', 'postPR', 'postV', 'retEq',
              'postQ', 'nv', 'postN', 'postRN')

    def __init__(self, **kw):
        for f in self.FIELDS:
            setattr(self, f, list(kw.get(f, ())))
        self.ghosts = kw.get('ghosts', 0)
        self.gw = list(kw.get('gw', ()))   # own parameter words: (cell, j), ghost `j` the word at the cell (`HSig.gw`)


EMPTY = HSig()


class HCert:
    def __init__(self, sig):
        self.sig = sig
        self.reads = {}          # (d, p, off) -> witness
        self.res = []
        self.calls = []
        self.rets = []
        self.divs = []
        self.hvs = []
        self.gargs = []
        self.eqs = []
        self.fas = []            # frame run cells guaranteed at return: `(kp, i)`, cell `i` of `frameAddr kp run`
        self.ders = []           # words at cells: value `DB + k` is the word at the cell `ders[k]`
        self.dups = []           # `ite`s (by guard) whose continuation is checked in each branch (`dupB`)


def nth(l, n):
    return l[n] if 0 <= n < len(l) else None


def instB(ms, bases, acc):
    for b, e in bases:
        m = nth(ms, b)
        if m is None:
            return None
        acc = cmul(acc, cpow(m, e))
    return acc


def instC(ms, c):
    return instB(ms, c[0], ((), c[1]))


def instI(ms, i):
    if i[0] == 'num':
        return ((), i[1])
    if i[0] == 'val':
        return nth(ms, i[1])
    return instC(ms, i[1])


def instR(ms, r):
    b, l, h = instC(ms, r[0]), instI(ms, r[2]), instI(ms, r[3])
    if b is None or l is None or h is None:
        return None
    return (b, r[1], l, h)


def instAll(ms, cs):
    out = []
    for c in cs:
        x = instC(ms, c)
        if x is None:
            return None
        out.append(x)
    return out


def instAllR(ms, rs):
    out = []
    for r in rs:
        x = instR(ms, r)
        if x is None:
            return None
        out.append(x)
    return out


def instPP(ms, ps):
    out = []
    for c, offs in ps:
        x = instC(ms, c)
        if x is None:
            return None
        out.append((x, tuple(offs)))
    return out


def instPRL(ms, ps):
    out = []
    for r, offs in ps:
        x = instR(ms, r)
        if x is None:
            return None
        out.append((x, tuple(offs)))
    return out


def instRM(ms, l):
    out = []
    for k, c in l:
        x = instC(ms, c)
        if x is not None:
            out.append((k, x))
    return out


# ---- the state

class St:
    __slots__ = ('env', 'sc', 'c2s', 'rs', 'ad', 'sv', 'src', 'pf', 'pr', 'n', 'nr', 'nc', 'nt', 'cd', 'eqs', 'dq')

    def __init__(self):
        self.env, self.sc, self.c2s, self.rs, self.ad, self.sv = {}, {}, {}, {}, {}, {}
        self.src, self.pf, self.pr = {}, {}, {}
        self.n = self.nr = self.nc = self.nt = 0
        self.cd = ()
        self.eqs = ()
        self.dq = ()

    def copy(self):
        s = St()
        s.env, s.sc, s.c2s, s.rs, s.ad, s.sv = dict(self.env), dict(self.sc), dict(self.c2s), dict(self.rs), \
            dict(self.ad), dict(self.sv)
        s.src, s.pf, s.pr = dict(self.src), dict(self.pf), dict(self.pr)
        s.n, s.nr, s.nc, s.nt, s.cd, s.eqs, s.dq = self.n, self.nr, self.nc, self.nt, self.cd, self.eqs, self.dq
        return s

    def cnt(self, o):
        s = self.copy()
        s.n, s.nr, s.nc, s.nt = o.n, o.nr, o.nc, o.nt
        return s

    def define(self, k, c):
        if k not in self.env:
            self.env[k] = c

    def put_sc(self, n, c):
        self.sc[n] = c
        self.c2s[c] = self.c2s.get(c, ()) + (n,)

    def push(self, c):
        self.put_sc(self.n, c)
        self.n += 1

    def pushP(self, p):
        self.pf[self.n] = p
        self.n += 1

    def pushR(self, r):
        self.rs[self.nr] = r
        self.nr += 1

    def pushPR(self, p):
        self.pr[self.nr] = p
        self.nr += 1


def mono(env, v):
    return env.get(v, baseC(v))


def monos(env, vs):
    return [mono(env, v) for v in vs]


def idxF(env, i):
    if i[0] == 'num':
        return ((), i[1])
    if i[0] == 'val':
        return env.get(i[1], baseC(i[1]))
    return i[1]


def runF(env, r):
    return (r[0], r[1], idxF(env, r[2]), idxF(env, r[3]))


# ---- coverage

def hasF(F, a, b):
    return any(p[0] == a and p[1] == b for p in F)


def hasFC(F, k, b):
    return any(not p[0][0] and k <= p[0][1] < CAPE and p[1] == b for p in F)


def hasFU(F, a, j):
    return any(p[0] == a and not p[1][0] and p[1][1] <= j and p[1][1] < CAPE for p in F)


def expOf(bs, k):
    for k2, e in bs:
        if k2 == k:
            return e
    return 0


def divB(b, S, l):
    return tuple((k, ndiv(e - expOf(b, k), S)) for k, e in l if expOf(b, k) < e)


def idxOf(b, c, S):
    return (divB(b[0], S, c[0]), ndiv(tsub(c[1], b[1]), S))


def ptIdx(F, R, c, J):
    base, S, lo, hi = R
    return c == cmul(base, cpow(J, S)) and hasF(F, J, hi) and (lo == ((), 0) or lo == J or hasF(F, lo, cshift(J, 1)))


def ptConst(F, R, c):
    base, S, lo, hi = R
    if not (c[0] == base[0] and base[1] <= c[1] and S != 0 and (c[1] - base[1]) % S == 0 and not lo[0]
            and lo[1] < CAPE):
        return False
    k = (c[1] - base[1]) // S
    return lo[1] <= k and ((not hi[0] and hi[1] < CAPE and k < hi[1]) or hasFC(F, k, hi))


def backK(R, c):
    base, S, lo, hi = R
    return ndiv(tsub(cmul(base, cpow(hi, S))[1], c[1]), S)


def ptBack(F, R, c):
    """A cell `k >= 1` indices below the upper bound (`ptBack`)."""
    base, S, lo, hi = R
    k = backK(R, c)
    return 0 < k and cshift(c, S * k) == cmul(base, cpow(hi, S)) and not lo[0] and lo[1] < CAPE and \
        hasFC(F, k - 1 + lo[1], hi)


def backC(F, R, c, ns):
    base, S, lo, hi = R
    k = backK(R, c)
    return 0 < k and cshift(c, S * k) == cmul(base, cpow(hi, S)) and not lo[0] and lo[1] < CAPE and \
        hasExp(F, hi) and len(ns) == lo[1] + k


def backCells(R, k, n):
    """`backW`'s cells, for the exponents `y < n` of the upper bound: `base·g^(S·y - S·k)` (`None` below `g^0`)."""
    base, S = R[0], R[1]
    return [(base[0], base[1] + S * y - S * k) if S * k <= base[1] + S * y else None for y in range(n)]


def backW(st, R, k, ns):
    return all(x is not None and st.sc.get(n) == x for x, n in zip(backCells(R, k, len(ns)), ns))


def ptRun(F, R, c):
    base, S, lo, hi = R
    return (c == cmul(base, cpow(lo, S)) and hasF(F, lo, hi)) or ptIdx(F, R, c, idxOf(base, c, S)) or \
        ptConst(F, R, c) or ptBack(F, R, c)


def powK(M, x):
    if M[0]:
        b, e = M[0][0]
        return ndiv(expOf(x[0], b), e)
    return ndiv(x[1], M[1])


def eqR(p, x, y):
    k = powK(p[0], x)
    return x == cpow(p[0], k) and y == cpow(p[1], k)


def eqV(E, x, y):
    return x == y or any(eqR(p, x, y) or eqR((p[1], p[0]), x, y) for p in E)


def cdivC(x, m):
    return (tuple((k, tsub(e, expOf(m[0], k))) for k, e in x[0] if tsub(e, expOf(m[0], k)) != 0), tsub(x[1], m[1]))


def eqM(p, x, y):
    k = powK(p[0], x)
    m = cpow(p[0], k)
    A = cdivC(x, m)
    return x == cmul(A, m) and y == cmul(A, cpow(p[1], k))


def eqVM(E, x, y):
    return eqV(E, x, y) or any(eqM(p, x, y) or eqM((p[1], p[0]), x, y) for p in E)


def keepL(X, st, qs, ws, i):
    """`keepL`: the guarantee runs a `callIf` keeps (where it is not entered, rewritten by the equations), and the
    index after their witnesses; `None` if one fails."""
    ks = []
    while i < len(ws):
        w = ws[i]
        q = nth(qs, w[1]) if w[0] == 'keep' else None
        if q is None or not (eqVM(st.eqs, q[0], w[2]) and eqVM(st.eqs, q[2], w[3]) and eqVM(st.eqs, q[3], w[4])):
            return None
        i = runOk(X, st, (w[2], q[1], w[3], w[4]), ws, i + 1)
        if i is None:
            return None
        ks.append(q)
    return i, ks


def loOk(F, E, Q, R):
    return eqV(E, Q[2], R[2]) or (not Q[2][0] and not R[2][0] and R[2][1] <= Q[2][1] < CAPE) or \
        (Q[2] == cshift(R[2], 1) and hasF(F, R[2], R[3]))


def hiOk(F, E, Q, R):
    return eqV(E, Q[3], R[3]) or hasF(F, Q[3], R[3]) or (0 < Q[3][1] and hasF(F, (Q[3][0], Q[3][1] - 1), R[3])) or \
        (not Q[3][0] and not R[3][0] and Q[3][1] <= R[3][1] < CAPE) or \
        (not Q[3][0] and Q[3][1] < CAPE and hasFC(F, tsub(Q[3][1], 1), R[3])) or hasF(F, Q[3], cshift(R[3], 1))


def runRun(F, E, Q, R):
    return Q[0] == R[0] and Q[1] == R[1] and loOk(F, E, Q, R) and hiOk(F, E, Q, R)


def shiftR(Q, R):
    """`CoreMode.shiftR`: `R` rebased onto `Q`'s base (its base `t` strides past, constant lower bounds,
    `R.lo + t <= Q.lo`), its cells from `Q.lo` to its upper bound; or `None`."""
    if not (0 < Q[1] and Q[1] == R[1] and Q[0][0] == R[0][0] and Q[0][1] <= R[0][1] and
            (R[0][1] - Q[0][1]) % Q[1] == 0 and not Q[2][0] and not R[2][0] and
            R[2][1] + (R[0][1] - Q[0][1]) // Q[1] <= Q[2][1] < CAPE):
        return None
    return (Q[0], Q[1], Q[2], R[3])


def runRunS(F, E, Q, R):
    R2 = shiftR(Q, R)
    return R2 is not None and runRun(F, E, Q, R2)


def emptyR(Q):
    return not Q[2][0] and not Q[3][0] and Q[3][1] <= Q[2][1] and Q[2][1] < CAPE


def emptyE(E, Q):
    return emptyR(Q) or eqV(E, Q[3], Q[2])


def constR(Q):
    return not Q[2][0] and not Q[3][0] and Q[2][1] < CAPE and Q[3][1] < CAPE


def rootC(c, S):
    return (tuple((b, ndiv(e, S)) for b, e in c[0]), ndiv(c[1], S))


def mrgPart(Q, S, r, lo, hi):
    return (cshift(Q[0], Q[1] * r), Q[1] * S, lo, hi)


def hasExp(F, m):
    return (not m[0] and m[1] < CAPE) or any(p[0] == m or p[1] == m for p in F)


def evsR(Q, k):
    return (Q, 1, ((), 0), ((), k))


def prepQ(R):
    return (R[0][0], tsub(R[0][1], R[1]))


def prepIdx(F, R, c):
    """A cell of a run extended by its point before it (`prepIdx`)."""
    base, S, lo, hi = R
    Q = prepQ(R)
    J = idxOf(Q, c, S)
    return S <= base[1] and not lo[0] and lo[1] == 0 and c == cmul(Q, cpow(J, S)) and (
        (J[0] == hi[0] and J[1] <= hi[1] and tsub(hi[1], J[1]) < CAPE and hasExp(F, hi) and
         (J == hi or hasExp(F, J))) or hasF(F, J, cshift(hi, 1)))


def appQ(R):
    return cmul(R[0], cpow(R[3], R[1]))


def appIdx(F, R, c):
    """A cell of a run extended by its point after it (`appIdx`)."""
    base, S, lo, hi = R
    J = idxOf(base, c, S)
    return not lo[0] and lo[1] == 0 and c == cmul(base, cpow(J, S)) and hasF(F, J, cshift(hi, 1))

def prepIdx2(F, R, c):
    """A cell of a run of lower bound `g^1` extended by its two points before it (`prepIdx2`)."""
    base, S, lo, hi = R
    Q = prepQ(R)
    J = idxOf(Q, c, S)
    return S <= base[1] and not lo[0] and lo[1] == 1 and c == cmul(Q, cpow(J, S)) and J[0] == hi[0] and \
        J[1] <= hi[1] and tsub(hi[1], J[1]) < CAPE and hasExp(F, hi) and (J == hi or hasExp(F, J))


def subL(offs, o):
    return all(x in o for x in offs)


def keyOk(args, ks):
    return len(args) == len(ks) and all(a == k for a, k in zip(args, ks))


def gargsOf(ga, g, args):
    for g2, ks, ms in ga:
        if g2 == g and keyOk(args, ks):
            return list(ms)
    return []


def boundsOf(p, q):
    return (q[2] == p[0] and q[3] == p[1]) or (q[2] == p[1] and q[3] == p[0])


def noSlot0(c):
    return all(b != 0 for b, _ in c[0])


def noSlot0I(i):
    if i[0] == 'val':
        return i[1] != 0
    if i[0] == 'num':
        return True
    return noSlot0(i[1])


def noSlot0R(r):
    return noSlot0(r[0]) and noSlot0I(r[2]) and noSlot0I(r[3])


def setNth(l, n, b):
    l = list(l)
    if 0 <= n < len(l):
        l[n] = b
    return l


class Fail(Exception):
    pass


# ---- the check (and, with a solver, the pass that finds the witnesses)

class X:
    """What the pass reads (`CX`), the branch conditions of the site (`path`), and the solver if the witnesses are
    being found."""

    def __init__(self, pows, H, sigOf, params, solver=None):
        self.pows, self.H, self.sigOf, self.params = pows, H, sigOf, params
        self.sig = H.sig
        self.dv, self.hv, self.eqk = set(H.divs), set(H.hvs), set(H.eqs)
        self.solver = solver
        self.path = []

    def resAt(self, i):
        r = nth(self.H.res, i)
        return unU(self.path, r) if r is not None else None

    def facts(self, env, res):
        F = [(idxF(env, a), idxF(env, b)) for a, b in self.sig.term]
        for i in res:
            r = self.resAt(i)
            if r is not None and r[0] == 'lt':
                F.append((idxF(env, r[1]), idxF(env, r[2])))
        return F + pathF(env, self.path)

    def subPt(self, F, env, res, R, c):
        for i in res:
            r = self.resAt(i)
            if r is None:
                continue
            if r[0] == 'sub' and r[1] == c and runF(env, r[2]) == R:
                return True
            if r[0] == 'subR' and runF(env, r[2]) == R and ptRun(F, runF(env, r[1]), c):
                return True
        return False

    def subRun(self, env, res, Q, R):
        for i in res:
            r = self.resAt(i)
            if r is not None and r[0] == 'subR' and runF(env, r[1]) == Q and runF(env, r[2]) == R:
                return True
        return False


def onPath(path, g):
    return all(c in path for c in g)


def unU(path, r):
    """`under g r` is `r` on a path with `g` (`unU`)."""
    while r[0] == 'under':
        if not onPath(path, r[1]):
            return None
        r = r[2]
    return r


def expFacts(m, e):
    if not e + 1 < CAPE:
        return []
    return ([] if e == 0 else [(((), e - 1), m)]) + [(m, ((), e + 1))]


def baseFacts(m, j):
    if len(m[0]) == 1 and m[0][0][1] == 1 and m[1] <= j:
        return expFacts(baseC(m[0][0][0]), j - m[1])
    return []


def pathF(env, path):
    """The facts of arm conditions: in arm `j` of `x`, `x`'s exponent is `j` (`expFacts`), and, `x`'s monomial being
    `b·g^t`, `b`'s is `j - t` (`baseFacts`)."""
    F = []
    for c in path:
        if c[0] == 'arm':
            mx = idxF(env, ('val', c[1]))
            F += expFacts(mx, c[2]) + baseFacts(mx, c[2])
    return F


def srcOf(st, c):
    if len(c[0]) == 1 and c[0][0][1] == 1:
        return st.src.get(c[0][0][0])
    return None


def ptOk(X, st, c, w):
    k = w[0]
    if k == 'ev':
        return st.sc.get(w[1]) == c
    if k == 'pre':
        return nth(X.sig.pre, w[1]) == c
    if k == 'run':
        R = st.rs.get(w[1])
        if R is None:
            return False
        F = X.facts(st.env, w[2])
        return ptRun(F, R, c) or X.subPt(F, st.env, w[2], R, c)
    if k == 'pf':
        p, a = st.pf.get(w[1]), srcOf(st, c)
        return p is not None and a is not None and a == p[0] and c[1] in p[1]
    if k == 'pfr':
        p, a = st.pr.get(w[1]), srcOf(st, c)
        return p is not None and a is not None and ptRun(X.facts(st.env, w[2]), p[0], a) and c[1] in p[1]
    if k == 'perm':
        r = X.resAt(w[1])
        return r is not None and r[0] == 'subP' and r[1] == c and len(r[2]) == len(w[2]) and \
            all(st.sc.get(n) == c2 for c2, n in zip(r[2], w[2]))
    if k == 'prep':
        R = st.rs.get(w[1])
        return R is not None and prepIdx(X.facts(st.env, w[3]), R, c) and ptOk(X, st, prepQ(R), w[2])
    if k == 'back':
        R = st.rs.get(w[1])
        return R is not None and backC(X.facts(st.env, w[3]), R, c, w[2]) and backW(st, R, backK(R, c), w[2])
    if k == 'evs':
        Q, n, kk = st.sc.get(w[1]), w[1], w[2]
        if Q is None or kk >= CAPE or any(st.sc.get(n + t) != cshift(Q, t) for t in range(kk)):
            return False
        R = evsR(Q, kk)
        F = X.facts(st.env, w[3])
        return ptRun(F, R, c) or X.subPt(F, st.env, w[3], R, c)
    if k == 'app':
        R = st.rs.get(w[1])
        return R is not None and appIdx(X.facts(st.env, w[3]), R, c) and ptOk(X, st, appQ(R), w[2])

    if k == 'prep2':
        R = st.rs.get(w[1])
        return R is not None and prepIdx2(X.facts(st.env, w[4]), R, c) and ptOk(X, st, prepQ(R), w[2]) and \
            ptOk(X, st, R[0], w[3])
    return False


def ptOkD(X, st, c, w):
    """`ptOkD`: `ptOk`, or `der Q res ws`: the cell in the run `Q` (`ptRun`, these residuals' facts), `Q` witnessed by
    `ws` (`runOk`)."""
    if w[0] == 'der':
        _, Q, res, ws = w
        return ptRun(X.facts(st.env, res), Q, c) and runOk(X, st, Q, list(ws), 0) == len(ws)
    return ptOk(X, st, c, w)


def runOkD(X, st, Q, ws, i):
    """`runOkD`: `drv R res` and `R`'s witnesses, `Q` inside `R` (`runRun`, or a residual `subR Q R`); else `runOk`."""
    if i < len(ws) and ws[i][0] == 'drv':
        _, R, res = ws[i]
        j = runOk(X, st, R, ws, i + 1)
        if j is None:
            return None
        F = X.facts(st.env, res)
        return j if runRun(F, st.eqs, Q, R) or X.subRun(st.env, res, Q, R) else None
    return runOk(X, st, Q, ws, i)


def rnOk(X, st, Q, w):
    if w[0] == 'run':
        R = st.rs.get(w[1])
        return R is not None and (runRun(X.facts(st.env, w[2]), st.eqs, Q, R) or X.subRun(st.env, w[2], Q, R) or
                                  runRunS(X.facts(st.env, w[2]), st.eqs, Q, R))
    if w[0] == 'empty':
        return emptyE(st.eqs, Q)
    return False


# Each requirement consumes witnesses from the front of `ws` (a list, read from index `i`): the index after them, or
# `None`.

def ptsW(X, st, m, offs, ws, i):
    for o in offs:
        if i >= len(ws) or not ptOk(X, st, cshift(m, o), ws[i]):
            return None
        i += 1
    return i


def ptrOk(X, st, c, offs, ws, i):
    if i >= len(ws):
        return None
    w = ws[i]
    if w[0] == 'pf':
        p = st.pf.get(w[1])
        return i + 1 if p is not None and p[0] == c and subL(offs, p[1]) else None
    if w[0] == 'pfr':
        p = st.pr.get(w[1])
        return i + 1 if p is not None and ptRun(X.facts(st.env, w[2]), p[0], c) and subL(offs, p[1]) else None
    if w[0] == 'word':
        p = st.sv.get(w[1])
        return ptsWR(X, st, p[1], offs, ws, i + 1) if p is not None and p[0] == c else None
    return None


def ptsWR(X, st, m, offs, ws, i):
    """`ptsWR`: after the marker `pts`, the cells past the word inside one run witness (`rnOk`), else `ptsW`."""
    if i + 1 < len(ws) and ws[i] == ('pts',) and offs:
        hi = max(offs) + 1
        return i + 2 if hi < CAPE and rnOk(X, st, (m, 1, ((), 0), ((), hi)), ws[i + 1]) else None
    return ptsW(X, st, m, offs, ws, i)


def ptrPts(X, st, b, S, offs, j, n, ws, i):
    for t in range(n):
        i = ptrOk(X, st, cshift(b, S * (j + t)), offs, ws, i)
        if i is None:
            return None
    return i


def ptrROk(X, st, Q, offs, ws, i):
    if i >= len(ws):
        return None
    w = ws[i]
    if w[0] == 'pfr':
        p = st.pr.get(w[1])
        return i + 1 if p is not None and runRun(X.facts(st.env, w[2]), st.eqs, Q, p[0]) and subL(offs, p[1]) \
            else None
    if w[0] == 'empty':
        return i + 1 if emptyE(st.eqs, Q) else None
    if w[0] == 'pts':
        return ptrPts(X, st, Q[0], Q[1], offs, Q[2][1], tsub(Q[3][1], Q[2][1]), ws, i + 1) if constR(Q) else None
    return None


def reqP(X, st, ms, cs, ws, i):
    for c in cs:
        c2 = instC(ms, c)
        if c2 is None or i >= len(ws) or not ptOk(X, st, c2, ws[i]):
            return None
        i += 1
    return i


def ptsRun(X, st, b, S, j, n, ws, i):
    for t in range(n):
        if i >= len(ws) or not ptOk(X, st, cshift(b, S * (j + t)), ws[i]):
            return None
        i += 1
    return i


def runOk1(X, st, Q, ws, i):
    if i >= len(ws):
        return None
    if ws[i][0] == 'pts':
        return ptsRun(X, st, Q[0], Q[1], Q[2][1], tsub(Q[3][1], Q[2][1]), ws, i + 1) if constR(Q) else None
    return i + 1 if rnOk(X, st, Q, ws[i]) else None


def runOk0(X, st, Q, ws, i):
    if i < len(ws) and ws[i][0] == 'cat':
        k = ws[i][1]
        if k >= CAPE:
            return None
        j = runOk1(X, st, (Q[0], Q[1], Q[2], ((), k)), ws, i + 1)
        return None if j is None else runOk1(X, st, (Q[0], Q[1], ((), k), Q[3]), ws, j)
    if i < len(ws) and ws[i][0] in ('mrg', 'mrgE'):
        S, res = ws[i][1], ws[i][-1]
        lo, hi = Q[2], Q[3]
        if ws[i][0] == 'mrg':
            rt = rootC(hi, S)
            rok = cpow(rt, S) == hi
        else:
            rt = ws[i][2]
            rok = eqV(st.eqs, cpow(rt, S), hi) or hasF(X.facts(st.env, res), hi, cshift(cpow(rt, S), 1))
        if not (0 < S and not lo[0] and lo[1] % S == 0 and lo[1] < CAPE and rok
                and hasExp(X.facts(st.env, res), rt)):
            return None
        j = i + 1
        for r in range(S):
            j = runOk1(X, st, mrgPart(Q, S, r, ((), lo[1] // S), rt), ws, j)
            if j is None:
                return None
        return j
    return runOk1(X, st, Q, ws, i)


def runOk(X, st, Q, ws, i, part=None):
    """`catM k h res`: the run split at the symbolic index `k` (`k·h` the upper bound by `eqV`), the part from `k`
    split once more (`runOkL`, `part` `runOk0`), else `runOk0`."""
    if i < len(ws) and ws[i][0] == 'catM':
        _, k, h, res = ws[i]
        F = X.facts(st.env, res)
        if not (eqV(st.eqs, cmul(k, h), Q[3]) and hasExp(F, k) and hasExp(F, h)):
            return None
        j = runOk0(X, st, (Q[0], Q[1], Q[2], k), ws, i + 1)
        return None if j is None else (part or runOkL)(X, st, (cmul(Q[0], cpow(k, Q[1])), Q[1], ((), 0), h), ws, j)
    return runOk0(X, st, Q, ws, i)


def runOkL(X, st, Q, ws, i):
    return runOk(X, st, Q, ws, i, runOk0)


def reqN(X, st, G, ws, i):
    """`CoreMode.reqN`: the guarantees over values, at their monomials."""
    mn = monos(st.env, G.nv)
    i = reqP(X, st, mn, G.postN, ws, i)
    return None if i is None else reqR(X, st, mn, G.postRN, ws, i)


def reqR(X, st, ms, rs, ws, i):
    for r in rs:
        q = instR(ms, r)
        if q is None:
            return None
        i = runOkD(X, st, q, ws, i)
        if i is None:
            return None
    return i


def reqPP(X, st, ms, ps, ws, i):
    for c, offs in ps:
        c2 = instC(ms, c)
        if c2 is None:
            return None
        i = ptrOk(X, st, c2, offs, ws, i)
        if i is None:
            return None
    return i


def reqPR(X, st, ms, ps, ws, i):
    for r, offs in ps:
        q = instR(ms, r)
        if q is None:
            return None
        i = ptrROk(X, st, q, offs, ws, i)
        if i is None:
            return None
    return i


def instQ(ms, qs):
    """`instQ`: a callee's `postQ` at the slots `ms`, those that instantiate."""
    out = []
    for c, q in qs:
        c2, q2 = instC(ms, c), instR(ms, q)
        if c2 is not None and q2 is not None:
            out.append((c2, q2))
    return out


def promoteQ(st, c, m):
    """`promoteQ`: the runs at the word of the cell `c`, its monomial `m` (the cell read), into the scope."""
    for c2, q in st.dq:
        if c2 == c:
            st.pushR((cmul(m, q[0]), q[1], q[2], q[3]))


def reqQ(X, st, ms, qs, ws, i):
    """`reqQ`: each `postQ` run at the word a load event stored at its cell (`word n`), then the run."""
    for c, q in qs:
        c2, q2 = instC(ms, c), instR(ms, q)
        if c2 is None or q2 is None or i >= len(ws) or ws[i][0] != 'word':
            return None
        p = st.sv.get(ws[i][1])
        if p is None or p[0] != c2:
            return None
        i = runOk(X, st, (cmul(p[1], q2[0]), q2[1], q2[2], q2[3]), ws, i + 1)
        if i is None:
            return None
    return i


def reqS(X, st, ms, G, ws, i):
    for f, k in ((reqP, G.pre), (reqR, G.preR), (reqPP, G.preP), (reqPR, G.prePR)):
        i = f(X, st, ms, k, ws, i)
        if i is None:
            return None
    return i


def derKs(ms):
    """The words at cells the monomials name: `k` for each base `DB + k` below `GB`, once, in order (`derKs`)."""
    out = []
    for c in ms:
        for b, _ in c[0]:
            if DB <= b < GB and b - DB not in out:
                out.append(b - DB)
    return out


def derWs(X, st, ks, ws, i):
    for k in ks:
        c = nth(X.H.ders, k)
        if c is None or i >= len(ws) or not ptOk(X, st, c, ws[i]):
            return None
        i += 1
    return i


def derSt(X, ks, st):
    if not ks:
        return st
    st = st.copy()
    for k in ks:
        c = nth(X.H.ders, k)
        if c is not None:
            st.src[DB + k] = c
    return st


def reqG(X, st, ma, g, args, ws, i):
    ga = gargsOf(X.H.gargs, g, args)
    if len(ga) != X.sigOf(g).ghosts:
        return None
    ks = derKs(ga)
    i = derWs(X, st, ks, ws, i)
    if i is None:
        return None
    return reqS(X, derSt(X, ks, st), ma + ga, X.sigOf(g), ws, i)


def armSkip(X, st, mx, j, ws, i):
    if i < len(ws) and ws[i][0] == 'skip' and j < CAPE and hasFU(X.facts(st.env, ws[i][1]), mx, j):
        return i + 1
    return None


def condSt(mx, j, cd, st):
    """`cd`: per dispatch `(mx, arms)`, arm `j`'s guarantees `arms[j] = (cs, rs, ps, prs)`."""
    st = st.copy()
    for e in cd:
        if e[0] == mx and j < len(e[1]):
            cs, rs, ps, prs = e[1][j]
            for c in cs:
                st.push(c)
            for p in ps:
                st.pushP(p)
            for r in rs:
                st.pushR(r)
            for p in prs:
                st.pushPR(p)
    return st


def pushPost(G, ms, st):
    ps, pps, rs, prs = instAll(ms, G.post), instPP(ms, G.postP), instAllR(ms, G.postR), instPRL(ms, G.postPR)
    if ps is None or pps is None or rs is None or prs is None:
        return False
    for c in ps:
        st.push(c)
    for p in pps:
        st.pushP(p)
    for r in rs:
        st.pushR(r)
    for p in prs:
        st.pushPR(p)
    return True


def postVE(G, ms, n0):
    out = []
    for i, m in G.postV:
        c = nth(G.post, i)
        if c is None:
            continue
        c2, m2 = instC(ms, c), instC(ms, m)
        if c2 is not None and m2 is not None:
            out.append((n0 + i, c2, m2))
    return out


def retDefs(st, rets, l):
    for k, m in l:
        r = nth(rets, k)
        if r is not None:
            st.define(r, m)


def endsRet(ss):
    return any(s[0] == 'ret' for s in ss)


def joinE(ls):
    ls = [l for ret, l in ls if not ret]
    if not ls:
        return []
    return [(k, a) for k, a in ls[0] if all(any(b == a for _, b in l) for l in ls[1:])]


def joinSt(bs, st, s):
    """`bs`: (returns, start, end) per block."""
    out = st.copy()
    for fld, cnt in (('sc', 'n'), ('rs', 'nr'), ('pf', 'n'), ('pr', 'nr')):
        ent = []
        for ret, b0, b1 in bs:
            lo, hi = getattr(b0, cnt), getattr(b1, cnt)
            d = getattr(b1, fld)
            ent.append((ret, [(k, d[k]) for k in range(lo, hi) if k in d]))
        for k, a in joinE(ent):
            if fld == 'sc':
                out.put_sc(k, a)
            else:
                getattr(out, fld)[k] = a
    out.n, out.nr, out.nc, out.nt = s.n, s.nr, s.nc, s.nt
    return out


def condE(sigOf, ms, mx, fs):
    """One entry for the dispatch: each arm's guarantees, empty where they do not instantiate."""
    arms = []
    for g in fs:
        G = sigOf(g)
        cs, rs, ps, prs = instAll(ms, G.post), instAllR(ms, G.postR), instPP(ms, G.postP), instPRL(ms, G.postPR)
        arms.append((tuple(cs), tuple(rs), tuple(ps), tuple(prs)) if None not in (cs, rs, ps, prs) else
                    ((), (), (), ()))
    return [(mx, tuple(arms))]


class Pass:
    """`chkC` and the loop's tail. `X.solver`, when set, supplies the witnesses (`need_*`) as the pass reaches them
    and records them in the certificate; failures are recorded and the pass goes on as if the witness were found."""

    def __init__(self, X, callee, body):
        self.X = X
        self.callee = callee        # a statement's name -> the `sigOf` key
        self.body = body
        self.fails = []

    def fail(self, what, *info):
        if self.X.solver is None:
            raise Fail((what,) + info)
        self.fails.append((what,) + info)

    # -- atoms
    def divOf(self, st, d, q, b):
        if q not in self.X.dv:
            return None
        md = st.env.get(d)
        mb = mono(st.env, b)
        if md is None or mb[0] or mb[1] > md[1]:
            return None
        return (md[0], md[1] - mb[1])

    def eqAt(self, st, a):
        """An atom's equation kept (`eqAt`): a listed `mul d a b` whose `d` has a monomial, `assertEq`, `copy`."""
        k, X = a[0], self.X
        if k == 'mul':
            d, x, y = a[1:]
            if d in X.eqk and d in st.env:
                st.eqs = ((cmul(mono(st.env, x), mono(st.env, y)), st.env[d]),) + st.eqs
        elif k in ('assertEq', 'copy'):
            x, y = a[1], a[2]
            if x in X.eqk:
                st.eqs = ((mono(st.env, x), mono(st.env, y)),) + st.eqs

    def atom(self, st, a):
        if self.X.solver is not None:
            self.X.solver.eq(self, st, a)
        self.eqAt(st, a)
        k = a[0]
        X = self.X
        if k == 'load':
            d, p, off = a[1:]
            c = cshift(mono(st.env, p), off)
            key = (d, p, off)
            S = X.solver
            if S is not None and S.is_read(key):
                w = S.read(self, st, c, d, key)
                if w is None:
                    self.fail('read', key, c)
            else:
                w = X.H.reads.get(key)
            if w is not None and w[0] != 'fail':
                if not ptOkD(X, st, c, w):
                    self.fail('read-check', key, c, w)
                elif w[0] == 'ev' and d in X.hv:
                    p2 = st.sv.get(w[1])
                    if p2 is not None and p2[0] == c:
                        st.define(d, p2[1])
            # loadPush (after `gwDef`: a read of an own parameter word names its ghost)
            st.sv[st.n] = (c, gw_def(st, X.sig.gw, c, d) if getattr(X.sig, "gw", None) else mono(st.env, d))
            st.push(c)
            if d not in st.src:
                st.src[d] = c
            promoteQ(st, c, mono(st.env, d))
        elif k == 'mul':
            d, x, y = a[1:]
            S = X.solver
            if S is not None:
                S.div(self, st, d, x, y)
            q = self.divOf(st, d, x, y)
            if q is not None:
                st.define(x, q)
            else:
                q = self.divOf(st, d, y, x)
                if q is not None:
                    st.define(y, q)
                else:
                    st.define(d, cmul(mono(st.env, x), mono(st.env, y)))
        elif k == 'add':
            d, x, y = a[1:]
            if d not in st.ad:
                st.ad[d] = (mono(st.env, x), mono(st.env, y))
        elif k == 'const':
            d, (l0, l1) = a[1], a[2]
            e = (0 if l0 == 1 else X.pows.get(l0)) if l1 == 0 else None
            if e is not None:
                st.define(d, ((), e))
        elif k in ('copy', 'assertEq'):
            x, y = a[1], a[2]
            if x not in st.env:
                st.define(x, mono(st.env, y))
            elif y not in st.env:
                st.define(y, st.env[x])
        elif k == 'hint':
            h = a[1]
            hd = hint_heap(h)
            if hd is not None:
                p, off, n = hd
                m = mono(st.env, p)
                if n >= HINT_RUN and m is not None:
                    # a long hint's cells as one run, in place of its points (`longRun`)
                    st.pushR((cshift(m, off), 1, ((), 0), ((), n)))
                    return
                for j in range(n):
                    st.push(cshift(m, off + j))
            elif h[0] == 'log2Ceil' and h[1][0] == 'heap':
                _, p, off, ln = h[1]
                dst = h[4]
                m = mono(st.env, p)
                for j in range(min(h[2], ln)):
                    key, c = (dst, p, off + j), cshift(m, off + j)
                    S = X.solver
                    w = S.bit(self, st, c, key) if S is not None else X.H.reads.get(key)
                    if w is None or w[0] == 'fail' or not ptOk(X, st, c, w):
                        self.fail('log2Ceil-bit', key, c, w)

    # -- calls
    def call(self, st, g, args, rets):
        X = self.X
        ma = monos(st.env, args)
        G = X.sigOf(g)
        ws = self.call_ws(st, ('call', g), lambda ws, i: reqG(X, st, ma, g, args, ws, i), g, args, ma)
        st.nc += 1
        retDefs(st, rets, instRM(ma, G.retM))
        ms = ma + monos(st.env, rets)
        n0 = st.n
        if not pushPost(G, ms, st):
            self.fail('post-inst', g)
            return
        for n, c, m in postVE(G, ms, n0):
            st.sv[n] = (c, m)
        st.eqs = tuple(instEq(ms, G.retEq)) + st.eqs
        st.dq = tuple(instQ(ms, G.postQ)) + st.dq

    def call_ws(self, st, site, check, g, args, ma):
        X = self.X
        if X.solver is not None:
            ws = X.solver.call(self, st, site, g, args, ma)
            if ws is None:
                self.fail('call', site)
                return None
            if check(ws, 0) != len(ws):
                self.fail('call-check', site, ws)
            return ws
        else:
            ws = nth(X.H.calls, st.nc)
            if ws is None:
                raise Fail(('no-call-wits', st.nc))
        if check(ws, 0) != len(ws):
            self.fail('call-check', site, ws)
        return ws

    def callIf(self, st, c, g, args):
        X = self.X
        ma = monos(st.env, args)
        G = X.sigOf(g)
        p = st.ad.get(c)
        qs, prs = instAllR(ma, G.postR), instPRL(ma, G.postPR)
        full = p is not None and qs is not None and prs is not None
        st0 = zeroEq(st.copy(), c)
        kept = []

        def check(ws, i):
            j = reqG(X, st, ma, g, args, ws, i)
            if j is None or not full:
                return j
            # the kept runs, where the call is not entered (`X.ext (czero c)`, `zeroEq`)
            saved = X.path
            X.path = [('zero', c)] + saved[1:]
            try:
                r = keepL(X, st0, qs, ws, j)
            finally:
                X.path = saved
            if r is None:
                return None
            kept[:] = r[1]
            return r[0]

        def ws_of():
            ws = self.call_ws(st, ('callIf', g), check, g, args, ma)
            if ws is not None and X.solver is not None and full:
                extra = X.solver.keeps(self, st, st0, c, g, qs, ws)
                if extra:
                    ws += extra
                    X.H.calls[st.nc] = ws
                    if check(ws, 0) != len(ws):
                        self.fail('call-check', ('callIf', g), ws)
            return ws
        self.under(('nonzero', c), ws_of)
        st.nc += 1
        if full:
            for q in qs:
                if boundsOf(p, q):
                    st.pushR(q)
            for q in kept:
                st.pushR(q)
            for q in prs:
                if boundsOf(p, q[0]):
                    st.pushPR(q)

    def dispatch(self, st, x, fs, args, rets):
        X = self.X
        ma = monos(st.env, args)
        mx = mono(st.env, x)
        if X.solver is not None:
            ws = X.solver.dispatch(self, st, x, fs, args, ma, mx, rets)
            if ws is None:
                self.fail('dispatch', fs)
        else:
            ws = nth(X.H.calls, st.nc)
            if ws is None:
                raise Fail(('no-call-wits', st.nc))
        kept = []
        vps, i = vpHead(ws) if ws is not None else ([], 0)
        abs_, i = abHead(ws, i) if ws is not None else ([], 0)
        if ws is not None:
            for j, g in enumerate(fs):
                i2 = armSkip(X, st, mx, j, ws, i)
                if i2 is not None:
                    i = i2
                    continue
                sj = condSt(mx, j, st.cd, st)
                i2 = self.under(('arm', x, j), lambda: reqG(X, sj, ma, g, args, ws, i))
                if i2 is not None:
                    i2 = self.under(('arm', x, j), lambda: vpArm(X, sj, ma, g, rets, vps, ws, i2))
                if i2 is not None:
                    i2 = self.under(('arm', x, j), lambda: abArm(X, sj, ma, g, rets, j, abs_, ws, i2))
                if i2 is None:
                    self.fail('dispatch-check', fs, j, ws)
                    i = None
                    break
                i = i2
                kept.append(g)
            if i is not None and i != len(ws):
                self.fail('dispatch-check-left', fs)
        if ws is None or i is None:
            kept = [g for j, g in enumerate(fs) if not (ws and armSkip(X, st, mx, j, ws, vps and len(vps) or 0))] \
                or list(fs)
        st.nc += 1
        if not kept:
            return
        g0, gs = kept[0], kept[1:]
        rms = [instRM(ma, X.sigOf(g).retM) for g in gs]
        retDefs(st, rets, [p for p in instRM(ma, X.sigOf(g0).retM)
                           if all(any(q[0] == p[0] and q[1] == p[1] for q in l) for l in rms)])
        ms = ma + monos(st.env, rets)
        arms = []
        for g in kept:
            G = X.sigOf(g)
            p, r = instAll(ms, G.post), instAllR(ms, G.postR)
            if p is None or r is None:
                self.fail('post-inst', g)
                return
            arms.append((p, r))
        meetc = [c for c in arms[0][0] if all(any(c2 == c for c2 in a[0]) for a in arms[1:])]
        n0 = st.n
        for c in meetc:
            st.push(c)
        for t, c in enumerate(meetc):
            m = armsV(X.sigOf, ms, kept, c)
            if m is not None:
                st.sv[n0 + t] = (c, m)
        for q in arms[0][1]:
            if all(any(q2 == q for q2 in a[1]) for a in arms[1:]):
                st.pushR(q)
        ptr = []
        for g in kept:
            G = X.sigOf(g)
            p, r = instPP(ms, G.postP), instPRL(ms, G.postPR)
            if p is None or r is None:
                ptr = None
                break
            ptr.append((p, r))
        if ptr:
            for q in ptr[0][0]:
                if all(any(q2 == q for q2 in a[0]) for a in ptr[1:]):
                    st.pushP(q)
            for q in ptr[0][1]:
                if all(any(q2 == q for q2 in a[1]) for a in ptr[1:]):
                    st.pushPR(q)
        mr = monos(st.env, rets)
        for j, offs in vps:
            m = nth(mr, j)
            if m is not None:
                for o in offs:
                    st.push(cshift(m, o))
        for q, a, S, hi, b in abs_:
            st.pushR((abBase(mx, q, a), S, ((), 0), abBase(mx, hi, b)))
        if len(fs) < CAPE:
            st.cd = st.cd + tuple(condE(X.sigOf, ms, mx, fs))

    def ret(self, st, vs):
        """`retC`: the frame run cells (`fas`) pushed first, into the state the guarantees are checked in only."""
        st0, st = st, st.copy()
        for kp, i in self.X.H.fas:
            st.push(cshift(mono(st.env, kp), i))
        self.ret1(st, vs)
        st0.nt = st.nt

    def ret1(self, st, vs):
        X = self.X
        G = X.sig
        mp, mv = monos(st.env, X.params), monos(st.env, vs)
        ms = mp + mv
        if X.solver is not None:
            ws = X.solver.ret(self, st, ms)
            if ws is None:
                self.fail('ret')
        else:
            ws = nth(X.H.rets, st.nt)
            if ws is None:
                raise Fail(('no-ret-wits', st.nt))
        if ws is not None:
            i = 0
            for f, l in ((reqP, G.post), (reqR, G.postR), (reqPP, G.postP), (reqPR, G.postPR), (reqQ, G.postQ)):
                i = f(X, st, ms, l, ws, i)
                if i is None:
                    break
            if (i if i is None or not (G.postN or G.postRN) else reqN(X, st, G, ws, i)) != len(ws):
                self.fail('ret-check', ws)
            elif not retVC(st, ms, G.post, ws, G.postV):
                self.fail('postV', ws)
        if not retEqC(st.eqs, ms, G.retEq):
            self.fail('retEq', G.retEq)
        for k, c in G.retM:
            m, c2 = nth(mv, k), instC(mp, c)
            if m is None or c2 is None or m != c2:
                self.fail('retM', k, c, m, c2)
        st.nt += 1

    # -- statements
    def under(self, c, f):
        """`f()` with the branch condition `c` on the site's path (`CX.ext`)."""
        self.X.path.insert(0, c)
        try:
            return f()
        finally:
            self.X.path.pop(0)

    def block(self, ss, st):
        for s in ss:
            k = s[0]
            if k == 'a':
                self.atom(st, s[1])
            elif k == 'ite':
                s1 = self.under(('zero', s[1]), lambda: self.block(s[2], zeroEq(st.copy(), s[1])))
                s2 = self.under(('nonzero', s[1]), lambda: self.block(s[3], st.cnt(s1)))
                st = joinSt([(endsRet(s[2]), st, s1), (endsRet(s[3]), st.cnt(s1), s2)], st, s2)
            elif k == 'match':
                bs = []
                cur = st
                for j, arm in enumerate(s[2]):
                    s1 = self.under(('arm', s[1], j), lambda: self.block(arm, cur.copy()))
                    bs.append((endsRet(arm), cur, s1))
                    cur = st.cnt(s1)
                st = joinSt(bs, st, bs[-1][2] if bs else st)
            elif k == 'call':
                self.call(st, s[1], s[2], s[3])
            elif k == 'callIf':
                self.callIf(st, s[1], s[2], s[3])
            elif k == 'dispatch':
                self.dispatch(st, s[1], s[2], s[3], s[4])
            elif k == 'ret':
                self.ret(st, s[1])
                return st
        return st

    # -- a loop's tail
    def tail(self, st, args, ei):
        X = self.X
        G = X.sig
        mp = monos(st.env, X.params)
        mi = mono(st.env, args[0])
        mx = setNth(mp, 1, mi)
        ex = ei == ('val', 1)
        if X.solver is not None:
            ws = X.solver.tail(self, st, mp, mx, ex, ei)
            if ws is None:
                self.fail('tail')
                return
        else:
            ws = nth(X.H.rets, st.nt)
            if ws is None:
                raise Fail(('no-ret-wits', st.nt))
        i = tail_check(X, st, mp, mx, ex, ei, ws)
        if i != len(ws) or G.postN or G.postRN:
            self.fail('tail-check', ws)


def instEq(ms, l):
    out = []
    for a, b in l:
        x, y = instC(ms, a), instC(ms, b)
        if x is not None and y is not None:
            out.append((x, y))
    return out


def retEqC(E, ms, l):
    for a, b in l:
        x, y = instC(ms, a), instC(ms, b)
        if x is None or y is None or not eqV(E, x, y):
            return False
    return True


def vpHead(ws):
    vps, i = [], 0
    while i < len(ws) and ws[i][0] == 'vp':
        vps.append((ws[i][1], tuple(ws[i][2])))
        i += 1
    return vps, i


def abHead(ws, i):
    """`abHead`: the blocks `(q, a, S, hi, b)`, `ab q S d` the block `(q, 0, S, g^d, 1)`."""
    abs_ = []
    while i < len(ws) and ws[i][0] in ('ab', 'abx'):
        if ws[i][0] == 'ab':
            abs_.append((ws[i][1], 0, ws[i][2], ((), ws[i][3]), 1))
        else:
            abs_.append(tuple(ws[i][1:6]))
        i += 1
    return abs_, i


def abArmR(j, e):
    """`abArmR`: arm `j`'s run of a block."""
    q, a, S, hi, b = e
    return (cshift(q, a * j), S, ((), 0), cshift(hi, b * j))


def abBase(mx, c, a):
    return c if a == 0 else cmul(c, cpow(mx, a))


def abArm(X, st, ma, g, rets, j, abs_, ws, i):
    """A dispatch arm `j`'s blocks: the runs `abArmR j e`, witnessed with the callee's guarantees pushed
    (`abArm`)."""
    if not abs_:
        return i
    G = X.sigOf(g)
    mr = setRM(monos(st.env, rets), instRM(ma, G.retM))
    S_ = st.copy()
    if not pushPost(G, ma + mr, S_):
        return None
    for e in abs_:
        i = runOk(X, S_, abArmR(j, e), ws, i)
        if i is None:
            return None
    return i


def setRM(mr, l):
    mr = list(mr)
    for k, m in reversed(l):
        if 0 <= k < len(mr):
            mr[k] = m
    return mr


def vpArm(X, st, ma, g, rets, vps, ws, i):
    """A dispatch arm's returned pointers' cells, each witnessed with the callee's guarantees pushed (`vpArm`)."""
    if not vps:
        return i
    G = X.sigOf(g)
    mr = setRM(monos(st.env, rets), instRM(ma, G.retM))
    S = st.copy()
    if not pushPost(G, ma + mr, S):
        return None
    for j, offs in vps:
        m = nth(mr, j)
        if m is None:
            return None
        i = ptsW(X, S, m, offs, ws, i)
        if i is None:
            return None
    return i


def wordAt(G, ms, c):
    for i, m in G.postV:
        cc = nth(G.post, i)
        if cc is not None and instC(ms, cc) == c:
            return instC(ms, m)
    return None


def armsV(sigOf, ms, gs, c):
    if not gs:
        return None
    m = wordAt(sigOf(gs[0]), ms, c)
    if m is None or not all(wordAt(sigOf(g), ms, c) == m for g in gs[1:]):
        return None
    return m


def retVC(st, ms, post, ws, l):
    for i, m in l:
        w, c = nth(ws, i), nth(post, i)
        if w is None or c is None or w[0] != 'ev':
            return False
        q, c2, m2 = st.sv.get(w[1]), instC(ms, c), instC(ms, m)
        if q is None or c2 is None or m2 is None or q[0] != c2 or q[1] != m2:
            return False
    return True


def tailP1(X, st, mp, mx, ex, c, w):
    c1 = instC(mp, c)
    if c1 is not None and ptOk(X, st, c1, w):
        return True
    c2 = instC(mx, c) if ex and noSlot0(c) else None
    return c2 is not None and ptOk(X, st, c2, w)


def tailR1(X, st, mp, mx, ex, ei, r, w):
    q = instR(mp, r)
    if q is not None and rnOk(X, st, q, w):
        return True
    q = instR(mx, r) if ex and noSlot0R(r) else None
    if q is not None and rnOk(X, st, q, w):
        return True
    if r[2] == ('val', 0) and r[3] == ei and noSlot0(r[0]):
        b, m0 = instC(mp, r[0]), nth(mp, 0)
        return b is not None and m0 is not None and ptOk(X, st, cmul(b, cpow(m0, r[1])), w)
    return False


def tailPP1(X, st, mp, mx, ex, p, ws, i):
    c = instC(mp, p[0])
    j = ptrOk(X, st, c, p[1], ws, i) if c is not None else None
    if j is not None:
        return j
    if ex and noSlot0(p[0]):
        c = instC(mx, p[0])
        return ptrOk(X, st, c, p[1], ws, i) if c is not None else None
    return None


def tailPR1(X, st, mp, mx, ex, ei, p, ws, i):
    q = instR(mp, p[0])
    j = ptrROk(X, st, q, p[1], ws, i) if q is not None else None
    if j is not None:
        return j
    if ex and noSlot0R(p[0]):
        q = instR(mx, p[0])
        j = ptrROk(X, st, q, p[1], ws, i) if q is not None else None
        if j is not None:
            return j
    if p[0][2] == ('val', 0) and p[0][3] == ei and noSlot0(p[0][0]):
        b, m0 = instC(mp, p[0][0]), nth(mp, 0)
        if b is not None and m0 is not None:
            return ptrOk(X, st, cmul(b, cpow(m0, p[0][1])), p[1], ws, i)
    return None


def tail_check(X, st, mp, mx, ex, ei, ws):
    G = X.sig
    i = 0
    for c in G.post:
        if i >= len(ws) or not tailP1(X, st, mp, mx, ex, c, ws[i]):
            return None
        i += 1
    for r in G.postR:
        if i >= len(ws):
            return None
        if tailR1(X, st, mp, mx, ex, ei, r, ws[i]):
            i += 1
            continue
        q = instR(mx, r) if ex and noSlot0R(r) else None
        i = runOk(X, st, q, ws, i) if q is not None else None
        if i is None:
            return None
    for p in G.postP:
        i = tailPP1(X, st, mp, mx, ex, p, ws, i)
        if i is None:
            return None
    for p in G.postPR:
        i = tailPR1(X, st, mp, mx, ex, ei, p, ws, i)
        if i is None:
            return None
    return i


HINT_RUN = 2048     # `longRun`: a heap hint of at least this many cells pushes its run, not its points


def hint_heap(h):
    idx = {'witness': 2, 'bits': 4, 'bitsExp': 3, 'digitsExp': 7, 'windowsExp': 5}.get(h[0])
    if idx is None:
        return None
    d = h[idx]
    return (d[1], d[2], d[3]) if d[0] == 'heap' else None


def stmts(ss):
    """The statements of a block, nested ones included (`stmtsOf`)."""
    for s in ss:
        yield s
        if s[0] == 'ite':
            yield from stmts(s[2])
            yield from stmts(s[3])
        elif s[0] == 'match':
            for a in s[2]:
                yield from stmts(a)


def values(params, body):
    out = set(params)
    for s in stmts(body):
        k = s[0]
        if k == 'a':
            a = s[1]
            n = {'const': 1, 'add': 3, 'mul': 3, 'copy': 2, 'load': 2, 'assertEq': 2, 'assertNe': 3, 'rangeCheck': 5,
                 'assertInK': 2, 'touch': 2, 'frameAddr': 1}.get(a[0], 0)
            out.update(a[1:1 + n])
            if a[0] == 'keccak':
                out.update(a[1]); out.update(a[2])
            elif a[0] == 'frameAddr':
                out.update(a[2])
        elif k in ('ite', 'match'):
            out.add(s[1])
        elif k == 'call':
            out.update(s[2]); out.update(s[3])
        elif k == 'callIf':
            out.add(s[1]); out.update(s[3])
        elif k == 'dispatch':
            out.add(s[1]); out.update(s[3]); out.update(s[4])
        elif k == 'ret':
            out.update(s[1])
    return out


def noret(s):
    """No `ret` in the statement, nested ones included."""
    return all(t[0] != 'ret' for t in stmts([s]))


def atomDst(a):
    """The values an atom defines in its frame (`atomDst`)."""
    if a[0] in ('const', 'add', 'mul', 'copy'):
        return [a[1]]
    if a[0] == 'hint':
        h = a[1]
        if h[0] in ('witness', 'bits', 'bitsExp', 'digitsExp', 'windowsExp'):
            d = h[-1]
            if d[0] == 'stack':
                return list(d[1])
    return []


def fa_past_ok(body, kp, i):
    """`CoreMode.faAt`'s second case: a top-level `frameAddr kp run`, the run nonempty and `i` past it."""
    for s in body:
        if not noret(s):
            break
        if s[0] == 'a' and s[1][0] == 'frameAddr' and s[1][1] == kp and s[1][2] and len(s[1][2]) <= i:
            return True
    return False


def fa_pairs(body):
    """Every `(kp, i)` `faOk` accepts: a `frameAddr kp run` and an atom defining `run[i]` among `topAtoms` (the
    top-level atoms before the first statement with a `ret` inside)."""
    top = []
    for s in body:
        if not noret(s):
            break
        if s[0] == 'a':
            top.append(s[1])
    D = {v for a in top for v in atomDst(a)}
    return [(a[1], i) for a in top if a[0] == 'frameAddr' for i, v in enumerate(a[2]) if v in D]


def idxOver(m, i):
    if i[0] == 'val':
        return i[1] < m
    if i[0] == 'num':
        return True
    return all(b < m for b, _ in i[1][0])


def dersOk(ders):
    return len(ders) < GB - DB and all(b < DB or b >= GB for c in ders for b, _ in c[0])


def zeroEq(st, c):
    """`zeroEq`: an `ite`'s zero branch keeps the equation of its guard's sum."""
    p = st.ad.get(c)
    if p is not None and p[0] is not None and p[1] is not None:
        st.eqs = (p,) + st.eqs
    return st


def dupB(ds, ss):
    """`dupB`: a top-level `ite` whose guard is listed takes its continuation into each branch."""
    out = []
    for i, s in enumerate(ss):
        if s[0] == 'ite' and s[1] in ds:
            rest = list(ss[i + 1:])
            return out + [('ite', s[1], list(s[2]) + rest, list(s[3]) + rest)]
        out.append(s)
    return out


def heapOkC(pows, sigOf, name, params, body, H, solver=None):
    """The check; with a `solver`, the pass finding the witnesses (into `H`). Returns the `Pass` (its `fails`), or
    raises `Fail` (check mode)."""
    G = H.sig
    m = len(params)
    X_ = X(pows, H, sigOf, params, solver)
    P = Pass(X_, sigOf, body)
    if list(params) != list(range(m)):
        P.fail('params')
    if not all(b < m for c in G.pre for b, _ in c[0]):
        P.fail('preOver')
    if not all(idxOver(m, a) and idxOver(m, b) for a, b in G.term):
        P.fail('term-over')
    if any(v >= DB for v in values(params, body)):
        P.fail('noGhost')
    if not dersOk(H.ders):
        P.fail('dersOk')
    fps = set(fa_pairs(body))
    if not all(p in fps or fa_past_ok(body, *p) for p in map(tuple, H.fas)):
        P.fail('faOk')
    st = St()
    for i in range(m):
        st.env[i] = baseC(i)
    ms = monos(st.env, params) + [baseC(GB + j) for j in range(G.ghosts)]
    pps, rs, prs = instPP(ms, G.preP), instAllR(ms, G.preR), instPRL(ms, G.prePR)
    if pps is None or rs is None or prs is None:
        P.fail('init-inst')
        return P
    for p in pps:
        st.pushP(p)
    for r in rs:
        st.pushR(r)
    for p in prs:
        st.pushPR(p)
    if not G.term:
        P.block(dupB(H.dups, body) if H.dups else body, st)
    elif len(G.term) == 1 and G.term[0][0] == ('val', 0) and G.term[0][1][0] in ('val', 'num') and (
            G.term[0][1] == ('val', 1) or G.term[0][1][0] == 'num'):
        if G.retM or G.postV or G.retEq or G.postQ:
            P.fail('loop-retM-postV')
        ei = G.term[0][1]
        if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf':
            P.fail('loop-shape')
            return P
        _, c, g, args = body[-2]
        st1 = P.block(body[:-2], st)
        P.callIf(st1, c, g, args)
        P.tail(st1, args, ei)
    else:
        P.fail('term-shape', G.term)
    return P
