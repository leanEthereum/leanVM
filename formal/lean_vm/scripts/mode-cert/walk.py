"""A mirror of `LeanVM/Guest/Mode/Abs.lean`, rule for rule, with demand hooks for inference."""
import collections

MAXCELLS = 2 ** 28
# `g^-1`, the immediate `x^63 + x^3 + x^2 + 1`, named as `g^(2^64 - 2)`
GINV = 2 ** 63 + 13

# ---------------------------------------------------------------- products
# Base: ('fr', o) | ('hp', q, d); Mono: (fp, k, bs) bs sorted tuple of (base, e)


def mk(fp, k, bs):
    d = collections.OrderedDict()
    for b, e in bs:
        d[b] = d.get(b, 0) + e
    return (fp, k, tuple(sorted((b, e) for b, e in d.items() if e)))


ONE = (0, 0, ())
def gp(e): return (0, e, ())
def root(o): return (0, 0, ((('fr', o), 1),))
def own(d): return (1, d, ())
def shift(m, o): return (m[0], m[1] + o, m[2])
def mul(a, b): return mk(a[0] + b[0], a[1] + b[1], a[2] + b[2])


def npow(x, e):
    r = ONE
    for _ in range(e): r = mul(r, x)
    return r


def removeBs(a, bs):
    for i, (b, e) in enumerate(bs):
        if b == a[0]:
            return bs[:i] + bs[i + 1:] if e == a[1] else None
    return None


def ownCell(m):
    return m[1] if m[0] == 1 and not m[2] and m[1] < 2 ** 62 else None


def rootCell(m):
    if m[0] == 0 and m[1] == 0 and len(m[2]) == 1 and m[2][0][1] == 1 and m[2][0][0][0] == 'fr':
        return m[2][0][0][1]
    return None

# ---------------------------------------------------------------- exponents
# Idx: ('num', n) | ('ex', base, c)


def isucc(i): return ('num', i[1] + 1) if i[0] == 'num' else ('ex', i[1], i[2] + 1)
def ishift(i, t): return ('num', i[1] + t) if i[0] == 'num' else ('ex', i[1], i[2] + t)


def ioff(a, b):
    if a[0] == 'num' and b[0] == 'num': return b[1] - a[1] if a[1] <= b[1] else None
    if a[0] == 'ex' and b[0] == 'ex': return b[2] - a[2] if a[1] == b[1] and a[2] <= b[2] else None
    return None


def ismall(i): return i[1] < 2 ** 62 if i[0] == 'num' else i[2] == 0


def sle(a, b):
    if a[0] == 'num' and b[0] == 'num': return a[1] <= b[1]
    if a[0] == 'num': return a[1] <= b[2]
    if b[0] == 'num': return False
    return a[1] == b[1] and a[2] <= b[2]

# ---------------------------------------------------------------- the state


class Abs:
    __slots__ = ('w', 'v', 'nz', 'hv', 'h', 'r', 'lt', 'pr', 'xs', 'p')

    def __init__(s):
        s.w = set(); s.v = {}; s.nz = set(); s.hv = {}; s.h = set(); s.r = set(); s.lt = set(); s.pr = []
        s.xs = {}
        s.p = set()

    def copy(s):
        t = Abs(); t.w = set(s.w); t.v = dict(s.v); t.nz = set(s.nz); t.hv = dict(s.hv); t.h = set(s.h)
        t.r = set(s.r); t.lt = set(s.lt); t.pr = list(s.pr); t.xs = dict(s.xs); t.p = set(s.p)
        return t

    def addV(s, o, x):
        if o not in s.v: s.v[o] = x

    def mono(s, o):
        x = s.v.get(o)
        if x is None: return root(o)
        return x[1] if x[0] == 'm' else None


    def hvGet(s, k):
        d = ownCell(k)
        if d is not None:
            return s.v.get(d, ('m', root(d))) if d in s.w else None
        return s.hv.get(k)

    def addHv(s, k, x):
        d = ownCell(k)
        if d is not None: s.addV(d, x); return
        if k not in s.hv: s.hv[k] = x

    def addH(s, k):
        d = ownCell(k)
        if d is not None: s.w.add(d); return
        s.h.add(k)

    def le(s, a, b):
        if sle(a, b): return True
        for p, q in s.lt:
            t = ioff(q, b)
            if t is not None and sle(a, ishift(isucc(p), t)): return True
        return False

    def ltI(s, a, b):
        if sle(isucc(a), b): return True
        for p, q in s.lt:
            t = ioff(p, a)
            if t is not None and sle(ishift(q, t), b): return True
        return False

    def knownB(s, b):
        if b[0] == 'fr': return b[1] in s.w
        return b[1] in s.w and s.covered((0, b[2], ((('fr', b[1]), 1),)))

    def known(s, m):
        return all(s.knownB(b) for b, e in m[2])

    def small(s, j):
        return ismall(j) or any(ismall(q) and s.le(j, q) for p, q in s.lt)

    def hasIdx(s, i):
        if i[0] == 'num': return True
        return any((p[0] == 'ex' and p[1] == i[1]) or (q[0] == 'ex' and q[1] == i[1]) for p, q in s.lt)

    def inRng(s, k, r):
        def at1(r):
            i = idxOf(r, k)
            return i is not None and s.le(r[1], i) and s.ltI(i, r[2])
        if at1(r): return True
        q, lo, hi, S, d = r
        if 0 < S <= d:
            t = d // S
            return at1((q, ishift(lo, t), ishift(hi, t), S, d - S * t))
        return False

    def covered(s, k):
        d = ownCell(k)
        if d is not None: return d in s.w
        return k in s.h or any(s.inRng(k, r) for r in s.r)

    def coveredR(s, r):
        q, lo, hi, S, d = r
        for (q2, lo2, hi2, S2, d2) in s.r:
            if q2 == q and S2 == S and d2 == d and s.le(lo2, lo) and s.le(hi, hi2) and s.hasIdx(lo) and s.hasIdx(hi):
                return True
        if lo[0] == 'num' and hi[0] == 'num':
            n = max(0, hi[1] - lo[1])
            return n <= 4096 and all(b[0] == 'fr' and b[1] in s.w for b, e in q[2]) and all(s.covered(shift(q, S * (lo[1] + j) + d)) for j in range(n))
        return False

    def ptrAt(s, k, os):
        x = s.hvGet(k)
        return x is not None and x[0] == 'm' and all(s.covered(shift(x[1], o)) for o in os)

    def coveredP(s, r, os):
        q, lo, hi, S, d = r
        for ((q2, lo2, hi2, S2, d2), os2) in s.p:
            if q2 == q and S2 == S and d2 == d and s.le(lo2, lo) and s.le(hi, hi2) and s.hasIdx(lo) and s.hasIdx(hi) and set(os) <= set(os2):
                return True
        if hi == isucc(lo) and s.hasIdx(lo) and s.ptrAt(first(r), os):
            return True
        if lo[0] == 'num' and hi[0] == 'num':
            n = max(0, hi[1] - lo[1])
            return n <= 4096 and all(b[0] == 'fr' and b[1] in s.w for b, e in q[2]) and all(s.ptrAt(shift(q, S * (lo[1] + j) + d), os) for j in range(n))
        return False


def idxOf(r, k):
    q, lo, hi, S, d = r
    if not (k[0] == q[0] and q[1] + d <= k[1] and S > 0 and (k[1] - q[1] - d) % S == 0): return None
    c = (k[1] - q[1] - d) // S
    if k[2] == q[2]: return ('num', c)
    qb = {b for b, e in q[2]}
    for b, e in k[2]:
        if e == S and b not in qb:
            rest = removeBs((b, S), k[2])
            if rest is not None and rest == q[2]: return ('ex', b, c)
            return None
    return None


def inter(A, B):
    t = Abs()
    t.w = A.w & B.w
    t.v = {o: x for o, x in A.v.items() if B.v.get(o) == x}
    t.nz = A.nz & B.nz
    t.hv = {k: x for k, x in A.hv.items() if B.hv.get(k) == x}
    t.h = A.h & B.h; t.r = A.r & B.r; t.lt = A.lt & B.lt; t.pr = []
    t.xs = {c: p for c, p in A.xs.items() if B.xs.get(c) == p}
    t.p = A.p & B.p
    return t

# ---------------------------------------------------------------- the walk


class Fail(Exception):
    pass


KECCAK_N = {'.one': 1, '.two': 2, '.all': 13}


def keccakIns(m0, m1, m2, m3, tail, b8, cap):
    return [m0, m1, m2, m3, tail, tail + 1, tail + 2, tail + 3, b8, cap, cap + 1, cap + 2, cap + 3]


class Env:
    def __init__(self, pows, jt, jtLo, jtHi, halt):
        self.pows = pows; self.jt = jt; self.jtLo = jtLo; self.jtHi = jtHi; self.halt = halt
        self.sigs = {}


def jtRng(E): return (ONE, ('num', E.jtLo), ('num', E.jtHi), 1, 0)


class Sig:
    def __init__(self, pc, entry, self_=None, pre=(), preR=(), term=(), ret=(), post=(), postR=(), postL=(),
                 preP=(), postP=(), postLP=()):
        self.pc = pc; self.entry = list(entry); self.self_ = self_; self.pre = list(pre); self.preR = list(preR)
        self.term = list(term); self.ret = list(ret); self.post = list(post); self.postR = list(postR)
        self.postL = list(postL); self.preP = list(preP); self.postP = list(postP); self.postLP = list(postLP)


class Walk:
    """`walk E F code` (Abs.lean), with hooks: `self.demand(kind, ...)` is called where the Lean
    walk fails; it returns True to continue as if the requirement held (inference)."""

    def __init__(self, E, entry, length, sig, hints, res, tabs, main=False, demand=None):
        self.E = E; self.entry = entry; self.len = length; self.sig = sig; self.hints = hints
        self.res = res; self.tabs = tabs; self.main = main
        self.demand = demand or (lambda *a: False)
        self.lnk = {}  # inference metadata: frame cell -> heap key it was linked to
        self.lnks = {}  # heap key -> frame cells linked to it
        self.rets = []; self.tails = []
        self.ld = {}  # inference metadata: frame cell -> heap key it was loaded from
        self.states = None

    def need(self, ok, *why):
        if ok: return
        if self.demand(*why): return
        raise Fail(why)

    def needW(self, A, o, i):
        if o in A.w: return
        if o in self.lnk and self.demand('lnk', i, o, self.lnk[o], A):
            A.w.add(o)
            x = self.loadVal(A, self.lnk[o][0])
            if x is not None: A.addV(o, x)
            return
        raise Fail(('W', i, o))

    def valOfImm(self, k0, k1):
        if k1 == 0:
            if k0 == 1: return ('m', ONE)
            if k0 == GINV: return ('m', gp(2 ** 64 - 2))
            e = self.E.pows.get(k0)
            if e is not None: return ('m', gp(e))
        return ('imm', k0, k1)

    def loadVal(self, A, k):
        x = A.hvGet(k)
        if x is not None: return x
        if k[0] == 0 and not k[2]:
            d = k[1]
            if self.E.jtLo <= d < self.E.jtHi and d in self.E.jt: return ('m', gp(self.E.jt[d]))
            return None
        if k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1:
            if A.inRng(k, jtRng(self.E)): return ('tab', k[2][0][0], k[1])
            if k[2][0][0][0] == 'fr': return ('m', (0, 0, ((('hp', k[2][0][0][1], k[1]), 1),)))
        return None

    def rangeFact(self, A, y):
        if A.pr:
            x, y2, z = A.pr[0]
            if y2 == y and A.ltI(('ex', ('fr', x), 0), ('num', MAXCELLS)):
                m = A.mono(z)
                if m is not None:
                    if m[0] == 0 and not m[2]:
                        if m[1] < 2 ** 62: A.lt.add((('ex', ('fr', x), 0), ('num', m[1] + 1)))
                    elif m[0] == 0 and len(m[2]) == 1 and m[2][0][1] == 1:
                        if m[1] == 0 or (m[1] < 2 ** 62 and A.ltI(('ex', m[2][0][0], 0), ('num', MAXCELLS))):
                            A.lt.add((('ex', ('fr', x), 0), ('ex', m[2][0][0], m[1] + 1)))
                        elif m[1] == 2 ** 64 - 2:
                            A.lt.add((('ex', ('fr', x), 0), ('ex', m[2][0][0], 0)))

    def stepOp(self, i, A, op, a):
        pc = self.entry + i
        if op == 'xor':
            x, y, z = a
            self.needW(A, x, i); self.needW(A, y, i)
            mx, my = A.mono(x), A.mono(y)
            A.w.add(z); A.pr = []
            if z not in A.xs: A.xs[z] = (x, y)
            if mx is not None and my is not None and mx[0] == 0 and my[0] == 0 and not mx[2] and not my[2]:
                if mx[1] != my[1] and mx[1] < 2 ** 62 and my[1] < 2 ** 62: A.nz.add(z)
            return
        if op == 'mul':
            x, y, z = a
            for o in (x, y, z):
                if o not in A.w and o in self.lnk and self.demand('lnk', i, o, self.lnk[o], A):
                    A.w.add(o)
                    vx = self.loadVal(A, self.lnk[o][0])
                    if vx is not None: A.addV(o, vx)
            if x in A.w and y in A.w:
                mx, my = A.mono(x), A.mono(y)
                A.w.add(z)
                if mx is not None and my is not None: A.addV(z, ('m', mul(mx, my)))
                if x in A.nz and y in A.nz: A.nz.add(z)
                A.pr = [(x, y, z)]
                return
            for kn, un in ((x, y), (y, x)):
                if z in A.w and kn in A.w:
                    if kn not in A.nz:
                        self.need(False, 'nz', i, kn, A)
                        A.nz.add(kn)
                    A.w.add(un)
                    if z in A.nz: A.nz.add(un)
                    A.pr = [(x, y, z)]
                    return
            self.needW(A, x, i); self.needW(A, y, i)
            return self.stepOp(i, A, op, a)
        if op == 'set':
            o, k0, k1 = a
            A.w.add(o); A.addV(o, self.valOfImm(k0, k1))
            if self.valOfImm(k0, k1)[0] == 'm': A.nz.add(o)
            if A.pr:
                x, inv, p = A.pr[0]
                if p == o and k0 == 1 and k1 == 0: A.nz.add(x); A.nz.add(inv)
            A.pr = []
            return
        if op == 'deref':
            p, o, c, mode = a
            self.needW(A, p, i)
            m = A.mono(p)
            if m is None: raise Fail(('ptrimm', i, p))
            k = shift(m, o)
            covered = A.covered(k)
            ps = [os for (r, os) in A.p if A.inRng(k, r)]
            cW = c in A.w
            cv = A.v.get(c, ('m', root(c)))
            lv = self.loadVal(A, k)
            pr = A.pr
            A.nz.add(p); A.lt.add((('ex', ('fr', p), 0), ('num', MAXCELLS)))
            if o == 0: self.rangeFact(A, p)
            if mode == '.pc':
                A.addH(k); A.addHv(k, ('m', gp(pc + 2))); A.pr = []; return
            if mode == '.fp':
                A.addH(k); A.addHv(k, ('m', own(0))); A.pr = []; return
            if cW:
                A.addH(k); A.addHv(k, cv); A.pr = pr; return
            if covered:
                self.ld.setdefault(c, k)
                A.w.add(c)
                if lv is not None: A.addV(c, lv)
                m = A.mono(c)
                if m is not None:
                    for os in ps:
                        for o in os: A.addH(shift(m, o))
                A.pr = pr; return
            self.lnk.setdefault(c, (k, i))
            self.lnks.setdefault(k, []).append(c)
            A.pr = pr
            return
        if op == 'jump':
            c, d, f = a
            for o in (c, d, f): self.needW(A, o, i)
            return
        if op == 'keccak':
            m0, m1, m2, m3, tail, b8, cap, out = a[:8]
            for o in keccakIns(m0, m1, m2, m3, tail, b8, cap): self.needW(A, o, i)
            for j in range(KECCAK_N[a[10]]): A.w.add(out + j)
            A.pr = []
            return
        raise Fail(('op', op))

    # -------------------------------------------------------- hints
    def destOf(self, A, dest, i):
        if dest[0] == 's': return (dest[1], None)
        self.needW(A, dest[1], i)
        m = A.mono(dest[1])
        if m is None: raise Fail(('destimm', i))
        return (None, m)

    def writeRun(self, A, dst, pos, n, bits):
        base, m = dst
        if base is not None:
            for j in range(n):
                o = base + pos + j
                A.w.add(o)
                if bits is not None:
                    A.nz.add(o)
                    if bits <= 61: A.lt.add((('ex', ('fr', o), 0), ('num', 2 ** bits)))
        else:
            for j in range(n): A.addH(shift(m, pos + j))

    def stepHint(self, i, A, h):
        t = h[0]
        if t == 'fa': return
        if t == 'av': return
        if t in ('al', 'ad', 'aa', 'af'):
            if t == 'ad': self.needW(A, h[2], i)
            if t == 'aa': self.needW(A, h[2], i)
            if t == 'af': self.needW(A, h[3], i)
            A.w.add(h[1]); return
        if t == 'ca':
            A.w.add(h[1]); A.addV(h[1], ('m', own(h[2]))); A.nz.add(h[1]); return
        if t == 'ws':
            self.writeRun(A, (h[2], None), 0, h[3], None); return
        if t == 'wh':
            self.writeRun(A, self.destOf(A, ('h', h[2]), i), h[3], h[4], None); return
        if t == 'lc':
            dst = self.destOf(A, h[1], i)
            if dst[0] is not None:
                for j in range(h[3]): self.needW(A, dst[0] + j, i)
            else:
                for j in range(h[3]): self.need(A.covered(shift(dst[1], j)), 'H', i, shift(dst[1], j), A)
            A.w.add(h[2]); A.nz.add(h[2]); return
        if t in ('bd', 'be'):
            self.needW(A, h[1], i)
            self.writeRun(A, self.destOf(A, h[2], i), 0, h[3], None); return
        if t == 'we':
            self.needW(A, h[1], i)
            self.writeRun(A, self.destOf(A, h[2], i), h[3], h[6], h[5]); return
        if t == 'dd':
            self.needW(A, h[1], i)
            if h[7] != '-': self.needW(A, int(h[7]), i)
            self.writeRun(A, self.destOf(A, h[2], i), 0, h[4], h[5]); return
        if t == 'fl':
            self.needW(A, h[1], i)
            self.writeRun(A, (h[2], None), 0, h[3], None); return
        if t == 'iv':
            self.needW(A, h[1], i)
            A.w.add(h[2])
            if h[1] in A.nz: A.nz.add(h[2])
            return
        raise Fail(('hint', h))

    def addRes(self, A, i, rs):
        for r in rs:
            if r[0] == 'lt':
                for x in (r[1], r[2]):
                    if x[0] == 'ex':
                        b = x[1]
                        ok = (b[1] in A.w) if b[0] == 'fr' else A.covered((0, b[2], ((('fr', b[1]), 1),)))
                        if not ok: raise Fail(('resW', i, r))
                A.lt.add((r[1], r[2]))
            elif r[0] == 'nz':
                if r[1] not in A.w: raise Fail(('resW', i, r))
                A.nz.add(r[1])

    # -------------------------------------------------------- calls
    def trFr(self, A, mq, o):
        if o >= 2 ** 30: return None
        x = A.hvGet(shift(mq, o))
        if x is not None: return x[1] if x[0] == 'm' else None
        q = rootCell(mq)
        return (0, 0, ((('hp', q, o), 1),)) if q is not None else None

    def trBase(self, A, mq, b):
        if b[0] == 'fr': return self.trFr(A, mq, b[1])
        mp = self.trFr(A, mq, b[1])
        if mp is None or b[2] >= 2 ** 30: return None
        x = A.hvGet(shift(mp, b[2]))
        if x is not None: return x[1] if x[0] == 'm' else None
        if mp[0] == 0 and len(mp[2]) == 1 and mp[2][0][1] == 1 and mp[2][0][0][0] == 'fr':
            return (0, 0, ((('hp', mp[2][0][0][1], mp[1] + b[2]), 1),))
        return None

    def trMono(self, A, mq, m):
        acc = mul(npow(mq, m[0]), gp(m[1]))
        for b, e in m[2]:
            x = self.trBase(A, mq, b)
            if x is None or e == 0: return None
            acc = mul(acc, npow(x, e))
        return acc

    def trIdxK(self, A, mq, i):
        if i[0] == 'num': return (i, 0)
        x = self.trBase(A, mq, i[1])
        if x is None or x[0] != 0 or x[1] >= 2 ** 62: return None
        if not x[2]: return (('num', i[2] + x[1]), 0)
        if len(x[2]) == 1 and x[2][0][1] == 1: return (('ex', x[2][0][0], i[2] + x[1]), x[1])
        return None

    def trIdx(self, A, mq, i):
        t = self.trIdxK(A, mq, i)
        return t[0] if t is not None else None

    def idxUp(self, A, mq, i):
        t = self.trIdxK(A, mq, i)
        if t is None: return None
        return t[0] if t[1] == 0 or A.hasIdx(t[0]) else None

    def idxDown(self, A, mq, i):
        t = self.trIdxK(A, mq, i)
        if t is None: return None
        return t[0] if t[1] == 0 or A.small(t[0]) else None

    def trRngBy(self, A, mq, tr, r):
        q = self.trMono(A, mq, r[0]); lo = tr(A, mq, r[1]); hi = tr(A, mq, r[2])
        if q is None or lo is None or hi is None: return None
        return (q, lo, hi, r[3], r[4])

    def trRngUp(self, A, mq, r): return self.trRngBy(A, mq, self.idxUp, r)
    def trRngDown(self, A, mq, r): return self.trRngBy(A, mq, self.idxDown, r)

    def entryOk(self, A, mq, G, i, name):
        for o in G.entry:
            self.need(o < 2 ** 30 and A.covered(shift(mq, o)), 'entry', i, name, o, A, self.lnks.get(shift(mq, o), []), self.lnk)
        if G.self_ is not None:
            self.need(G.self_ < 2 ** 30 and A.hvGet(shift(mq, G.self_)) == ('m', mq), 'self', i, name)
        for m in G.pre:
            k = self.trMono(A, mq, m)
            self.need(k is not None and A.known(k) and A.covered(k), 'pre', i, name, m, k, A)
        for r in G.preR:
            r2 = self.trRngDown(A, mq, r)
            self.need(r2 is not None and A.coveredR(r2), 'preR', i, name, r, r2, A)
        for r, os in G.preP:
            r2 = self.trRngDown(A, mq, r)
            self.need(r2 is not None and A.coveredP(r2, os), 'preP', i, name, r, os, r2, A)

    def afterCall(self, A, mq, G):
        A = A.copy()
        for o in G.ret: A.addH(shift(mq, o))
        for m in G.post:
            k = self.trMono(A, mq, m)
            if k is not None: A.addH(k)
        for r in G.postR + G.postL:
            r2 = self.trRngUp(A, mq, r)
            if r2 is not None: A.r.add(r2)
        for r, os in G.postP + G.postLP:
            r2 = self.trRngUp(A, mq, r)
            if r2 is not None: A.p.add((r2, os))
        self.atCall(A, mq, G)
        return A

    def atCall(self, A, mq, G):
        for p, q in G.term:
            a, b = self.idxUp(A, mq, p), self.idxUp(A, mq, q)
            if a is not None and b is not None: A.lt.add((a, b))

    def loopOk(self, A, i):
        for r in self.sig.postL:
            k = self.trMono(A, own(0), first(r))
            self.need(k is not None and A.covered(k), 'loop', i, r, A)
        for r, os in self.sig.postLP:
            k = self.trMono(A, own(0), first(r))
            self.need(k is not None and A.ptrAt(k, os), 'loopP', i, r, os, A)

    def retOk(self, A, i):
        self.loopOk(A, i)
        for o in self.sig.ret: self.need(o in A.w, 'retW', i, o, A)
        for m in self.sig.post:
            k = self.trMono(A, own(0), m)
            self.need(k is not None and A.covered(k), 'post', i, m, A)
        for r in self.sig.postR:
            r2 = self.trRngDown(A, own(0), r)
            self.need(r2 is not None and A.coveredR(r2), 'postR', i, r, A)
        for r, os in self.sig.postP:
            r2 = self.trRngDown(A, own(0), r)
            self.need(r2 is not None and A.coveredP(r2, os), 'postP', i, r, os, A)

    def calleesOf(self, A, i, t):
        v = A.v.get(t)
        if v is not None and v[0] == 'm' and v[1][0] == 0 and not v[1][2]:
            G = self.E.sigs.get(v[1][1])
            return [G] if G is not None else None
        if v is not None and v[0] == 'tab':
            _, x, d = v
            n = self.tabs.get(i)
            if n is None: return None
            self.need(A.ltI(('ex', x, 0), ('num', n)), 'sel', i, x, n, A)
            if not (self.E.jtLo <= d and d + n <= self.E.jtHi): return None
            out = []
            for j in range(n):
                pc = self.E.jt.get(d + j)
                G = self.E.sigs.get(pc) if pc is not None else None
                if G is None: return None
                out.append(G)
            return out
        return None

    def armsOf(self, A, i, t):
        v = A.v.get(t); n = self.tabs.get(i)
        if v is None or n is None or v[0] != 'tab': return None
        _, x, d = v
        self.need(A.ltI(('ex', x, 0), ('num', n)), 'sel', i, x, n, A)
        if not (self.E.jtLo <= d and d + n <= self.E.jtHi): return None
        out = []
        for j in range(n):
            pc = self.E.jt.get(d + j)
            if pc is None or not (self.entry + i < pc < self.entry + self.len): return None
            out.append(pc - self.entry)
        return out

    def jumpI(self, i, A, d, f):
        if d == 0 and f == 1:
            self.retOk(A, i); self.rets.append(A.copy()); return ('out', A)
        mf = A.mono(f)
        selfp = mf == own(0) or (mf == ONE and self.main)
        if selfp:
            md = A.mono(d)
            if md is not None and md[0] == 0 and not md[2]:
                e = md[1]
                if self.entry + i < e < self.entry + self.len: return ([e - self.entry], A)
                if self.main and e == self.E.halt: return ('out', A)
                raise Fail(('localjump', i, e))
            ts = self.armsOf(A, i, d)
            if ts is None: raise Fail(('arms', i))
            return (ts, A)
        if mf is not None and mf[0] == 1 and not mf[2]:
            e = mf[1]
            md = A.mono(d)
            if md is not None and md[0] == 0 and not md[2] and md[1] in self.E.sigs:
                G = self.E.sigs[md[1]]
                self.need(md[1] == self.entry, 'tailself', i)
                self.entryOk(A, own(e), G, i, ('tail', md[1]))
                for r in G.postL + [r for r, os in G.postLP]:
                    self.need(self.trRngUp(A, own(e), r) == (r[0], isucc(r[1]), r[2], r[3], r[4]), 'stride', i, r, A)
                for p, q in G.term:
                    ok = p[0] == 'ex' and p[2] == 0 and q[0] == 'ex' and q[2] == 0
                    if ok:
                        a2, b2 = self.idxUp(A, own(e), p), self.idxUp(A, own(e), q)
                        t = ioff(p, a2) if a2 is not None else None
                        ok = t is not None and t > 0 and b2 == q
                    self.need(ok, 'termstep', i, p, q, A)
                self.loopOk(A, i)
                self.tails.append((A.copy(), e, md[1], i))
                return ('out', A)
            raise Fail(('tail', i))
        if mf is None: raise Fail(('fimm', i))
        mq = mf
        h1, h0 = A.hvGet(shift(mq, 1)), A.hvGet(shift(mq, 0))
        if h1 == ('m', own(0)) and h0 is not None and h0[0] == 'm' and h0[1][0] == 0 and not h0[1][2]:
            r = h0[1][1]
            A = A.copy()
            Gs = self.calleesOf(A, i, d)
            if not Gs: raise Fail(('callees', i))
            for G in Gs: self.atCall(A, mq, G)
            for G in Gs: self.entryOk(A, mq, G, i, G.pc)
            if not (self.entry + i < r < self.entry + self.len): raise Fail(('callret', i))
            B = self.afterCall(A, mq, Gs[0])
            for G in Gs[1:]: B = inter(B, self.afterCall(A, mq, G))
            return ([r - self.entry], B)
        raise Fail(('jumpkind', i))

    def condOf(self, A, c):
        if c in A.nz: return True
        x = A.v.get(c)
        if x is None: return None
        if x == ('imm', 0, 0): return False
        if x[0] == 'imm': return True if x[1] < 2 ** 64 and x[2] < 2 ** 64 else None
        if not x[1][2]: return True
        return None

    def run(self, code, keep=False):
        cur = [entryAbs(self.E, self.sig)]
        # pending edges hold shared snapshots, copied when taken; meets are memoized (order-free)
        pend = {}
        memo = {}
        alive = []
        if keep: self.states = []
        for i, (op, a) in enumerate(code):
            edges = pend.pop(i, [])
            if len(cur) + len(edges) > 2:
                key = (tuple(id(x) for x in cur), frozenset(id(x) for x in edges))
                if cur or key not in memo:
                    memo[key] = cap(cur + edges)[0]
                sts = [memo[key].copy()]
            else:
                sts = cur + [x.copy() for x in edges]
            if keep: self.states.append(sts[0].copy() if sts else None)
            cur = []
            for A in sts:
                for h in self.hints.get(i, []): self.stepHint(i, A, h)
                self.addRes(A, i, self.res.get(i, []))
                self.stepOp(i, A, op, a)
                if op != 'jump':
                    cur.append(A)
                    continue
                c, d, f = a
                k = self.condOf(A, c)
                if k is False: cur.append(learn0(A, c)); continue
                go, A2 = self.jumpI(i, A, d, f)
                if go != 'out':
                    snap = A2.copy(); alive.append(snap)
                    for t in go:
                        if t <= i: raise Fail(('backjump', i, t))
                        pend.setdefault(t, []).append(snap)
                if k is not True: cur.append(learn0(A, c))
        if pend: raise Fail(('pend', sorted(pend)))

def cap(sts):
    """At most two paths: more are met into one."""
    if len(sts) <= 2: return sts
    B = sts[0]
    for X in sts[1:]: B = inter(B, X)
    return [B]


def first(r):
    q, lo, hi, S, d = r
    if lo[0] == 'num': return shift(q, S * lo[1] + d)
    return shift(mul(q, (0, 0, ((lo[1], S),))), S * lo[2] + d)


def entryAbs(E, G):
    A = Abs()
    A.w = set(G.entry); A.h = set(G.pre); A.r = {jtRng(E)} | set(G.preR); A.lt = set(G.term)
    A.p = set(G.preP)
    if G.self_ is not None:
        A.w.add(G.self_); A.addV(G.self_, ('m', own(0))); A.nz.add(G.self_)
    return A


def learn0(A, c):
    """The fall-through of a jump on `[c]`: a sum `[c] = [a] + [b]` gives `[a] = [b]`."""
    p = A.xs.get(c)
    if p is None: return A
    a, b = p
    B = A.copy()
    if b not in B.v: B.addV(b, B.v.get(a, ('m', root(a))))
    else: B.addV(a, B.v.get(b, ('m', root(b))))
    return B
