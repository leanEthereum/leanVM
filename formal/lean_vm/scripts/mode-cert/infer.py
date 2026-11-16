"""Signatures and residuals for the mode walk (`LeanVM/Guest/Mode/Abs.lean`), inferred callee
first, by `walk.py`, a mirror of the Lean walk with demand hooks. Prints how many functions pass,
and the residuals and failures; `gen.py` writes the certificates from them."""
import sys, os, collections
sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from walk import *
import data
P = data.load()
fns, HINTS, POWS, JT = P['fns'], P['hints'], P['pows'], P['jt']
byentry = {f['entry']: f for f in fns.values()}
JT_LO, HALT = 430, 2 ** 19 - 1
# the jump table's end: past its last slot (`__jump_tables` writes the slots from JT_LO on)
JT_HI = max(JT) + 1
assert sorted(JT) == list(range(JT_LO, JT_HI))


def conv(op, a):
    if op in ('xor', 'mul'): return tuple(map(int, a))
    if op == 'set': return tuple(map(int, a))
    if op == 'deref': return (int(a[0]), int(a[1]), int(a[2]), a[3])
    if op == 'jump': return tuple(map(int, a))
    if op == 'keccak': return tuple(map(int, a[:8])) + (a[8] == 'true', a[9] == 'true', a[10])
    raise Exception(op)


for f in fns.values():
    f['ops'] = [(op, conv(op, a)) for op, a in f['code']]
    f['hints'] = {pc - f['entry']: hs for pc, hs in HINTS.items() if f['entry'] <= pc < f['entry'] + f['count']}

_b = set()
for f in fns.values():
    c = f['ops']
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            _b.add(a[1][1])
_bl = sorted(_b)
REGION = {t: (_bl[k + 1] if k + 1 < len(_bl) else JT_HI) - t for k, t in enumerate(_bl)}
for f in fns.values():
    c = f['ops']; f['tabs'] = {}
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            f['tabs'][i] = REGION[a[1][1]]

E = Env(POWS, JT, JT_LO, JT_HI, HALT)

calls = collections.defaultdict(set)
for f in fns.values():
    for op, a in f['ops']:
        if op == 'set' and a[2] == 0 and POWS.get(a[1]) in byentry:
            calls[f['name']].add(byentry[POWS[a[1]]]['name'])
    c = f['ops']
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            for j in range(REGION[a[1][1]]):
                g = byentry.get(JT.get(a[1][1] + j))
                if g: calls[f['name']].add(g['name'])
# each function a table call's arms reach, with its arm indices
ARMIDX = collections.defaultdict(set)
for f in fns.values():
    c = f['ops']
    for i in range(1, len(c)):
        a, b = c[i - 1], c[i]
        if a[0] == 'deref' and b[0] == 'jump' and a[1][3] == '.cell' and a[1][2] == b[1][1]:
            for j in range(REGION[a[1][1]]):
                g = byentry.get(JT.get(a[1][1] + j))
                if g: ARMIDX[g['name']].add(j)
order = []; seen = set()


def dfs(n):
    seen.add(n)
    for m in sorted(calls[n]):
        if m not in seen and m != n: dfs(m)
    order.append(n)


for n in sorted(fns, key=lambda n: fns[n]['entry']):
    if n not in seen: dfs(n)

# loop helpers: a tail call into themselves; their self cell
isloop = set()
selfc = {}
for f in fns.values():
    c = f['ops']
    for i, (op, a) in enumerate(c):
        if op == 'deref' and a[3] == '.cell' and a[0] == a[2]:
            for d in range(1, 5):
                if i + d < len(c) and c[i + d][0] == 'jump':
                    od = c[i + d][1][1]
                    for k in range(i - 1, max(-1, i - 300), -1):
                        if c[k][0] == 'set' and c[k][1][0] == od:
                            e = POWS.get(c[k][1][1])
                            if e is not None: selfc[e] = a[1]
                            break
                    break
for f in fns.values():
    if f['name'] in calls[f['name']]: isloop.add(f['name'])


def loopBound(f):
    """A loop's bound: the exponent its next counter meets at the exit, a parameter's or a constant."""
    c = f['ops']
    sets = {a[0]: a[1] for op, a in c if op == 'set' and a[2] == 0}
    muls = {a[2]: a for op, a in c if op == 'mul'}
    for op, a in c:
        if op == 'jump' and a[1] in sets and POWS.get(sets[a[1]]) == f['entry']:
            for x, y, z in (a2 for op2, a2 in c if op2 == 'xor' and a2[2] == a[0]):
                for nx, b in ((x, y), (y, x)):
                    m = muls.get(nx)
                    if m is not None and 2 in m[:2] and POWS.get(sets.get(m[1] if m[0] == 2 else m[0])) == 1:
                        if b in sets and POWS.get(sets[b]) is not None: return ('num', POWS[sets[b]])
                        return ('ex', ('fr', b), 0)
    return ('ex', ('fr', 3), 0)


BOUND = {n: loopBound(fns[n]) for n in isloop}


def params(f): return set(range(2, 2 + f.get('nargs', 0)))


def ifaceBase(f, b):
    return b[1] in params(f)


def ifaceMono(f, m):
    return m[0] == 0 and all(ifaceBase(f, b) for b, e in m[2])


def ifaceIdx(f, i):
    return i[0] == 'num' or ifaceBase(f, i[1])


class Infer:
    def __init__(self, f):
        self.f = f; self.pre = set(); self.preR = set(); self.res = collections.defaultdict(list)
        self.preP = {}
        self.new = False; self.unres = []; self.w = None
        # residuals read off the state of one pass, kept only if the final walk needs them
        self.prunable = []

    def demand(self, kind, i, *rest):
        f = self.f
        if kind == 'lnk':
            o, (k, i0), A = rest
            return self.key(k, i0, A)
        if kind == 'nz':
            kn, A = rest
            self.res[i].append(('nz', kn)); self.new = True; return True
        if kind == 'pre':
            name, m, k, A = rest
            if isinstance(name, tuple) and name[0] == 'tail':
                return False
            if k is None: return False
            # the callee's bounded reads as runs, and this function walked again
            if self.runPre(name, m): return False
            if self.armRun(('pt', k), A): return True
            if self.key(k, i, A): return True
            if self.armSub(k, i, A, m): return True
            # a heap cell linked to frame cells loaded from unknown cells: those loads' cells
            for c in self.w.lnks.get(k, []):
                if c in self.w.lnk and c not in A.w and self.key(self.w.lnk[c][0], self.w.lnk[c][1], A): return True
            return False
        if kind == 'preP':
            name, r, os, r2, A = rest
            if isinstance(name, tuple) and name[0] == 'tail': return False
            if r2 is not None and ifaceMono(f, r2[0]) and ifaceIdx(f, r2[1]) and ifaceIdx(f, r2[2]) and r2[0][2]:
                self.addP(r2, os, A); return True
            return False
        if kind == 'preR':
            name, r, r2, A = rest
            if isinstance(name, tuple) and name[0] == 'tail': return False
            if r2 is None: return self.smallIdx([r[1], r[2]], i, A)
            if r2 is not None and self.armRun(('run', r2), A): return True
            if r2 is not None and ifaceMono(f, r2[0]) and ifaceIdx(f, r2[1]) and ifaceIdx(f, r2[2]) and r2[0][2]:
                self.preR.add(r2); self.new = True; A.r.add(r2); return True
            return r2 is not None and (self.linSub(r2, i, A) or self.splitPre(r2, i, A) or self.downSub(r2, i, A) or
                                       self.blkRun(r2, i, A) or self.narrow(name, r, r2, A))
        if kind == 'entry':
            name, o, A, cs, lnk = rest
            for c in cs:
                if c in lnk and lnk[c][0] != None:
                    k2, i0 = lnk[c]
                    if self.key(k2, i0, A):
                        return True
            return False
        if kind == 'H':
            k, A = rest
            return self.key(k, i, A)
        if kind == 'sel':
            x, n, A = rest
            r = ('lt', ('ex', x, 0), ('num', n))
            self.res[i].append(r); self.new = True; A.lt.add((r[1], r[2])); return True
        return False

    def runPre(self, pc, m):
        """A callee's point at a product with a base this function cannot bound: the callee inferred again,
        needing every cell its own bound on that index lets it name (`RUNPRE`), and this function walked again."""
        g = byentry.get(pc)
        if g is None or g['name'] in RUNPRE or not any(b[0] == 'hp' for b, e in m[2]): return False
        # with the other arms of its table call
        gs = {g['name']}
        for t, n in REGION.items():
            if any(JT.get(t + j) == pc for j in range(n)):
                gs |= {byentry[JT[t + j]]['name'] for j in range(n) if JT.get(t + j) in byentry}
        # their other callers walked against their signatures already
        if any(x in calls[y] for x in gs for y in DONE if y != self.f['name']): return False
        for x in sorted(gs, key=lambda x: fns[x]['entry']):
            RUNPRE.add(x)
            try: infer(x)
            except Fail:
                RUNPRE.discard(x); infer(x)
        self.new = True
        return True

    def armCopies(self, w):
        """An arm `armStrides` asks for: storing at a cell over the interface a word it loads from a cell its
        sibling arms need already, not known written: that cell a precondition, so that its guarantees hold
        the stored one."""
        f = self.f; got = False
        ok = COPYPRE.get(f['name'])
        if not ok: return False
        for k, cs in sorted(w.lnks.items(), key=str):
            if not ifaceMono(f, k): continue
            for c in cs:
                src = w.lnk.get(c, (None,))[0]
                if src is not None and src != k and src in ok and src not in self.pre:
                    self.pre.add(src); got = True
        if got: self.new = True
        return got

    def splitRes(self, w):
        """A parameter whose word at a return is `[s]^K·[r]`: a table written over `T` in blocks of `S1 = K·S2`
        cells up to `[s]`'s exponent, then past `[s]^S1` in blocks of `S2` up to `[r]`'s, is written in blocks of
        `S2` up to the parameter's exponent (`Res.sub`, a split's)."""
        f = self.f; got = False
        for A, i in zip(w.rets, w.retAt):
            for p in sorted(params(f)):
                m = A.mono(p)
                if m is None or m[0] != 0 or m[1] != 0 or len(m[2]) != 2: continue
                for (bs, K), (br, er) in (tuple(m[2]), tuple(reversed(m[2]))):
                    if er != 1 or K < 2: continue
                    for R in sorted(A.r, key=str):
                        T, lo, hi, S1, o = R
                        if o != 0 or lo != ('num', 0) or hi != ('ex', bs, 0) or S1 % K or T[1] != 0 or not ifaceMono(f, T):
                            continue
                        S2 = S1 // K
                        Tq = mul(T, (0, 0, ((bs, S1),)))
                        if not all((T, lo, hi, S1, x) in A.r for x in range(S1)): continue
                        if not all((Tq, ('num', 0), ('ex', br, 0), S2, d) in A.r for d in range(S2)):
                            # the part past `[s]^S1` from a table call's arms, walked again
                            if f['name'] not in STRIDES: STRIDES.add(f['name']); got = True
                            continue
                        if A.coveredR((T, ('num', 0), ('ex', ('fr', p), 0), S2, 0)): continue
                        # the parameter named by its cell, so a guarantee over its exponent translates
                        if ('name', p) not in self.res[i]: self.res[i].insert(0, ('name', p)); got = True
                        for d in range(S2):
                            a = (T, ('num', 0), ('ex', ('fr', p), 0), S2, d)
                            r = ('sub', a, [(T, lo, hi, S1, t * S2 + d) for t in range(K)] + [(Tq, ('num', 0), ('ex', br, 0), S2, d)])
                            if r not in self.res[i]: self.res[i].append(r); got = True
        if got: self.new = True
        return got

    def smallIdx(self, idxs, i, A):
        """A callee's exponent bound translated to `e(x) + c`, `c > 0`, `x`'s exponent not known small: its
        bound below `2^32` (`Res.lt`), so that it translates (`idxDown`)."""
        mq = getattr(self.w, 'curMq', None)
        if mq is None: return False
        got = False
        for j in idxs:
            t = self.w.trIdxK(A, mq, j)
            if t is None or t[1] == 0 or A.small(t[0]) or not self.w.idxOk(A, t[0]): continue
            self.addRes(i, ('lt', t[0], ('num', SMALL))); A.lt.add((t[0], ('num', SMALL))); got = True
        return got

    def armSub(self, k, i, A, m=None):
        """A table call's arm reading `q·g^c`, inside a run the function holds over part of `q`: the run
        over `q` below the selector's exponent is inside it (`Res.sub`), and `c` below the arm's index."""
        x = self.w.cursel if self.w is not None else None
        if x is None or k[0] != 0 or not k[2]: return False
        q = (0, 0, k[2])
        for R in sorted(A.r, key=str):
            Q, lo, hi, S, d = R
            if lo != ('num', 0) or S != 1 or d != 0 or not Q[2] or Q[1] != 0 or Q[2] == k[2]: continue
            rest = dict(k[2])
            if not all(rest.get(b, 0) >= e for b, e in Q[2]): continue
            a = (q, ('num', 0), ('ex', x, 0), 1, 0)
            self.addRes(i, ('sub', a, [R])); A.r.add(a); return True
        # the arm's `m`-th point of its parameter's run `o·g^j` (`o = k / g^m`), `m` below the arm's index:
        # that run below the selector's exponent inside a known run over `o`'s bases (`Res.sub`)
        off = m[1] if m is not None and m[0] == 0 and len(m[2]) == 1 and m[2][0][1] == 1 else k[1]
        if off > k[1] or not A.ltI(('num', off), ('ex', x, 0)): return False
        o = (0, k[1] - off, k[2])
        for R in sorted(A.r, key=str):
            Q, lo, hi, S, d = R
            if lo == ('num', 0) and S == 1 and d == 0 and Q[1] == 0 and Q[2] and \
                    all(dict(o[2]).get(b, 0) >= e for b, e in Q[2]):
                a = (o, ('num', 0), ('ex', x, 0), 1, 0)
                self.addRes(i, ('sub', a, [R])); A.r.add(a); return True
        return False

    def armRun(self, d, A):
        """A table call's arm needing a point `Q·g^c` or a run `Q·[0, c)` over the interface, `c` within the
        selector's exponent `e(x)` plus `t < 3` on this arm: the run `Q·[0, e(x) + t)` a precondition."""
        x = self.w.cursel if self.w is not None else None
        f = self.f
        if x is None or x[0] != 'fr' or x[1] not in params(f): return False
        if d[0] == 'pt':
            k = d[1]
            if k[0] != 0 or not k[2] or not ifaceMono(f, k): return False
            q, S, off, ok = (0, 0, k[2]), 1, 0, lambda t: A.ltI(('num', k[1]), ('ex', x, t))
        else:
            q, lo, hi, S, off = d[1]
            if lo != ('num', 0) or hi[0] != 'num' or not q[2] or not ifaceMono(f, q): return False
            ok = lambda t: A.le(hi, ('ex', x, t))
        for t in range(3):
            if ok(t):
                r = (q, ('num', 0), ('ex', x, t), S, off)
                self.preR.add(r); self.new = True; A.r.add(r); return True
        return False

    def narrow(self, pc, r, r2, A):
        """A callee's run of `n` consecutive cells it reads at a bounded index, of which the caller holds
        only every `S`-th, the least such `S`: the callee needs that strided part, its read inside it a
        residual (`key`), and is inferred again."""
        q, lo, hi, S1, d = r2
        if r[1] != ('num', 0) or r[2][0] != 'num' or lo != ('num', 0) or hi != r[2] or S1 != r[3]: return False
        n = hi[1]; S = 2
        while S <= n and not (n % S == 0 and A.coveredR((q, lo, ('num', n // S), S1 * S, d))): S *= 2
        g = byentry.get(pc)
        if S > n or g is None or NARROW[g['name']].get(r) == S: return False
        # its other callers walked against its signature already
        if any(g['name'] in calls[m] for m in DONE if m != self.f['name']): return False
        NARROW[g['name']][r] = S
        try:
            infer(g['name'])
        except Fail:
            del NARROW[g['name']][r]
            infer(g['name'])
            return False
        self.new = True; A.r.add(r2); return True

    def addRes(self, i, r):
        if r not in self.res[i]:
            self.res[i].append(r); self.new = True

    def linSub(self, r2, i, A):
        """A run over a bound not the interface's, inside a run over a parameter's bound by the code's
        arithmetic: the parameter's word the bound's to the stride times more (`q^S r = n`), or the
        bound's times `g^k` (`n / g`). A residual (`Res.sub`) and the parameter's run a precondition."""
        f = self.f
        q, lo, hi, S, d = r2
        if self.shiftSub(r2, i, A): return True
        if not (q[2] and ifaceMono(f, q) and ifaceIdx(f, lo) and hi[0] == 'ex'): return False
        hb, t = hi[1], hi[2]
        if hb[0] == 'fr': mh = A.mono(hb[1])
        else:
            x = A.hvGet((0, hb[2], ((('fr', hb[1]), 1),)))
            mh = x[1] if x is not None and x[0] == 'm' else None
        cands = []
        if mh is not None and mh[0] == 0 and t == 0 and lo == ('num', 0):
            for p in sorted(params(f)):
                mp = A.mono(p)
                if mp is None or mp[0] != 0 or mp == root(p) or mp[1] < S * mh[1]: continue
                dm = dict(mp[2])
                if all(dm.get(b, 0) >= S * e for b, e in mh[2]):
                    cands.append((q, ('num', 0), ('ex', ('fr', p), 0), 1, 0))
        if hb[0] == 'fr':
            for op, a in f['ops']:
                if op == 'mul' and a[2] in params(f) and hb[1] in a[:2]:
                    mo = A.mono(a[1] if a[0] == hb[1] else a[0])
                    if mo is not None and mo[0] == 0 and not mo[2] and mo[1] >= t:
                        cands.append((q, lo, ('ex', ('fr', a[2]), 0), S, d))
        for b in cands:
            self.preR.add(b); self.new = True; A.r.add(b)
            self.addRes(i, ('sub', r2, [b])); A.r.add(r2)
            return True
        return False

    def copyPre(self, w):
        """A loop copying a word it loads from `k` to a cell over the interface at its counter: `k`'s cells a
        precondition, so the copy writes. `k = Q·x^S·g^c`, `x` the counter: `Q`'s run of stride `S` over the
        counter's range; `k = Q·[y]·g^c`, `y` another word: `Q`'s run up to the bound, the read inside it
        (`Res.sub`)."""
        f = self.f
        if f['name'] not in isloop: return False
        got = False
        for c, (k, i0) in sorted(w.lnk.items(), key=str):
            if k is None or k[0] != 0 or not k[2]: continue
            if not any(c in cs and k2 != k and k2[0] == 0 and ifaceMono(f, k2) and dict(k2[2]).get(('fr', 2))
                       for k2, cs in w.lnks.items()): continue
            dk = dict(k[2])
            Q = (0, 0, tuple(x for x in k[2] if x[0] != ('fr', 2)))
            if dk.get(('fr', 2)) and Q[2] and ifaceMono(f, Q):
                r = (Q, ('ex', ('fr', 2), 0), BOUND[f['name']], dk[('fr', 2)], k[1])
                if r not in self.preR: self.preR.add(r); got = True
                continue
            for y, e in k[2]:
                Q = (0, 0, tuple(x for x in k[2] if x[0] != y))
                if e != 1 or not Q[2] or not ifaceMono(f, Q) or ifaceBase(f, y): continue
                r = (Q, ('num', 0), BOUND[f['name']], 1, 0)
                if r not in self.preR: self.preR.add(r); got = True
                a = (k, ('num', 0), ('num', 1), 1, 0)
                if ('sub', a, [r]) not in self.res[i0]: self.res[i0].append(('sub', a, [r])); got = True
                break
        if got: self.new = True
        return got

    def splits(self, A):
        """The function's splits `[n] = [s]^K·[r]`, `K >= 2`: a write-once assertion `MUL` of cells whose
        words multiply to `[s]^K·[r]` into the cell `n`."""
        out = []; seen = set()
        for op, a in self.f['ops']:
            if op in ('xor', 'mul'): x = a[2]
            elif op == 'set': x = a[0]
            else: continue
            if op == 'mul' and x in seen:
                ma, mb = A.mono(a[0]), A.mono(a[1])
                if ma is not None and mb is not None:
                    m = mul(ma, mb)
                    if m[0] == 0 and m[1] == 0 and len(m[2]) == 2:
                        for (bs, K), (br, er) in (m[2], m[2][::-1]):
                            if K >= 2 and er == 1: out.append((bs, br, x, K))
            seen.add(x)
        return out

    def blkWhole(self, Q, i0, A):
        """`Q·[0, [n])`, `Q` written in the blocks of a split `[n] = [s]^K·[r]`: inside them (`Res.sub`)."""
        for s, r, n, K in self.splits(A):
            bs = [(Q, ('num', 0), ('ex', s, 0), K, t) for t in range(K)] + \
                [(mul(Q, (0, 0, ((s, K),))), ('num', 0), ('ex', r, 0), 1, 0)]
            if not all(A.coveredR(b) for b in bs): continue
            a = (Q, ('num', 0), ('ex', ('fr', n), 0), 1, 0)
            self.addRes(i0, ('sub', a, bs)); A.r.add(a)
            return a
        return None

    def blkRun(self, r2, i, A):
        """A run of stride 1 from `0` over a table written in the blocks of a split: inside the whole
        run (`blkWhole`, `Res.sub`)."""
        q, lo, hi, S, d = r2
        if q[0] != 0 or q[1] != 0 or lo != ('num', 0) or S != 1 or d != 0 or hi[0] != 'ex' or not q[2]: return False
        a = self.blkWhole(q, i, A)
        if a is None: return False
        self.addRes(i, ('sub', r2, [a])); A.r.add(r2)
        return True

    def blkPoint(self, k, i0, A):
        """A cell `Q·x·g^c` over a table written in the blocks of a split: the whole run inside them
        (`blkWhole`), then the cell inside it (`runPoint`)."""
        if k[0] != 0 or len(k[2]) < 2: return False
        for B, e in k[2]:
            Q = (0, 0, tuple(y for y in k[2] if y[0] != B))
            if e == 1 and Q[2] and self.blkWhole(Q, i0, A) is not None: return self.runPoint(k, i0, A)
        return False

    def invShift(self, v):
        """`t` when the immediate `v` is `g^-t`, `t <= 64`."""
        x = v
        for t in range(1, 65):
            x <<= 1
            if x >> 64: x ^= (1 << 64) | 0b11011
            if x == 1: return t
        return None

    def downSub(self, r2, i, A):
        """A run of stride 1 over `Q·g^c` up to `[h]`'s exponent, `[h] = [p]·g^-t` by the code, `p` a parameter,
        `c <= t`: inside `Q·[0, [p])` (`Res.sub`), that run a precondition."""
        f = self.f
        q, lo, hi, S, d = r2
        if q[0] != 0 or S != 1 or lo != ('num', 0) or hi[0] != 'ex' or hi[2] != 0 or hi[1][0] != 'fr': return False
        Q = (0, 0, q[2])
        if not q[2] or not ifaceMono(f, Q): return False
        h = hi[1][1]
        sets = {a[0]: a[1] for op, a in f['ops'] if op == 'set' and a[2] == 0}
        for op, a in f['ops']:
            if op != 'mul' or a[2] != h: continue
            for p, c in ((a[0], a[1]), (a[1], a[0])):
                t = self.invShift(sets[c]) if c in sets else None
                if p in params(f) and t is not None and q[1] + d <= t:
                    b = (Q, ('num', 0), ('ex', ('fr', p), 0), 1, 0)
                    if b not in self.preR: self.preR.add(b); self.new = True
                    A.r.add(b); self.addRes(i, ('sub', r2, [b])); A.r.add(r2)
                    return True
        return False

    def splitPre(self, r2, i, A):
        """A block of a split `[n] = [s]^K·[r]` (`splits`): the run of stride `K` from `d < K` up to `[s]`'s
        exponent, or of stride 1 past `[s]^K` up to `[r]`'s, over `Q`: inside `Q·[0, [n])` (`Res.sub`). That run
        known, or `[n] = [m]·g^c` and `Q·[0, [m])` known with the `c` cells past it (`Res.sub`)."""
        q, lo, hi, S, d = r2
        if q[0] != 0 or q[1] != 0 or lo != ('num', 0) or hi[0] != 'ex' or hi[2] != 0: return False
        for s, r, n, K in self.splits(A):
            Q = None
            if hi[1] == s and S == K and d < K: Q = q
            elif hi[1] == r and S == 1 and d == 0:
                Q = (0, 0, removeBs((s, K), q[2])) if removeBs((s, K), q[2]) is not None else None
            if Q is None or not Q[2]: continue
            b = (Q, ('num', 0), ('ex', ('fr', n), 0), 1, 0)
            if not A.coveredR(b):
                mn = A.mono(n)
                if mn is None or mn[0] != 0 or not (0 < mn[1] <= 64) or len(mn[2]) != 1 or mn[2][0][1] != 1: continue
                m = mn[2][0][0]
                b1 = (Q, ('num', 0), ('ex', m, 0), 1, 0)
                b2 = (mul(Q, (0, 0, ((m, 1),))), ('num', 0), ('num', mn[1]), 1, 0)
                if not (A.coveredR(b1) and A.coveredR(b2)): continue
                self.addRes(i, ('sub', b, [b1, b2])); A.r.add(b)
            self.addRes(i, ('sub', r2, [b])); A.r.add(r2)
            return True
        return False

    def shiftSub(self, r2, i, A):
        """A run `Q·x·[0, [c])` of stride 1, `x` a word `[b]` the code multiplies by `[c]` into `[p]`: inside
        `Q·[0, [p])` (`Res.sub`), that run known or, `Q` over the interface and `p` a parameter, a
        precondition."""
        f = self.f
        q, lo, hi, S, d = r2
        if q[0] != 0: return False
        # a part of `Q·x`'s cells inside a known run over `Q` from `0`, of stride 1
        for B, e in q[2]:
            Q = (0, q[1], tuple(x for x in q[2] if x[0] != B))
            if e != 1 or not Q[2] or lo[0] != 'num' or hi[0] != 'num': continue
            for b in sorted(A.r, key=str):
                if b[0] == Q and b[1] == ('num', 0) and b[3] == 1 and b[2][0] == 'ex' and b[4] == 0:
                    self.addRes(i, ('sub', r2, [b])); A.r.add(r2)
                    return True
        if lo != ('num', 0) or S != 1 or hi[0] != 'ex' or hi[2] != 0 or hi[1][0] != 'fr': return False
        c = hi[1][1]
        for B, e in q[2]:
            Q = (0, q[1], tuple(x for x in q[2] if x[0] != B))
            if e != 1 or not Q[2]: continue
            for op, a in f['ops']:
                if op != 'mul' or c not in a[:2]: continue
                o = a[1] if a[0] == c else a[0]
                if A.mono(o) != (0, 0, ((B, 1),)): continue
                b = (Q, ('num', 0), ('ex', ('fr', a[2]), 0), 1, d)
                if not A.coveredR(b):
                    if a[2] not in params(f) or not ifaceMono(f, Q): continue
                    self.preR.add(b); self.new = True; A.r.add(b)
                self.addRes(i, ('sub', r2, [b])); A.r.add(r2)
                return True
        return False

    def addP(self, r, os, A):
        old = self.preP.get(r, set())
        if not set(os) <= old:
            self.preP[r] = old | set(os); self.new = True
        A.p.add((r, tuple(sorted(self.preP[r]))))

    def pkey(self, k2, o, A):
        """A cell `o` past a pointer loaded from the heap cell `k2`: a run of such pointers."""
        f = self.f
        if k2[0] != 0: return False
        for (x, e) in k2[2]:
            if x[0] != 'fr': continue
            Q = tuple((b, ee) for b, ee in k2[2] if b != x)
            if not (Q and ifaceMono(f, (0, 0, Q))): continue
            if f['name'] in isloop and x == ('fr', 2):
                r = ((0, 0, Q), ('ex', x, 0), ('ex', x, 1), e, k2[1])
                for r0 in self.preP:
                    if r0[0] == r[0] and r0[3] == e and r0[4] == k2[1]: r = r0
                self.addP(r, (o,), A); return True
            for (p, hi) in sorted(A.lt, key=lambda t: (t[1][0] != 'num', t[1][1] if t[1][0] == 'num' else 0)):
                if p == ('ex', x, 0) and ifaceIdx(f, hi) and hi != ('num', MAXCELLS):
                    self.addP(((0, 0, Q), ('num', 0), hi, e, k2[1]), (o,), A); return True
        return False

    def key(self, k, i0, A, depth=0):
        f = self.f
        if k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and k[2][0][0][0] == 'fr' and self.w is not None:
            c = k[2][0][0][1]
            if c in self.w.ld:
                # in a loop the stream is passed to, a cursor loaded from the loop's record: inside the stream
                if f['name'] in isloop and f['name'] in STREAMS and depth == 0 and \
                        dict(self.w.ld[c][2]).get(('fr', 2)) and self.streamRead(k, i0, A):
                    return True
                if self.pkey(self.w.ld[c], k[1], A):
                    A.h.add(k); return True
        # a jump table load through an unbounded selector: residual bound
        if (i0 + 1) in f['tabs'] and k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and k[1] in REGION:
            x = k[2][0][0]
            r = ('lt', ('ex', x, 0), ('num', REGION[k[1]]))
            if r not in self.res[i0]:
                self.res[i0].append(r); self.new = True
            A.lt.add((r[1], r[2])); return True
        # the same, the key shifted into its region (an adjusted selector, `x·g^a`): the arms from the
        # shifted slot to the region's end
        if (i0 + 1) in f['tabs'] and k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and JT_LO <= k[1] < JT_HI:
            st = max(t for t in REGION if t <= k[1])
            # loaded at the region's start through a frame cell holding the product: that cell named
            # (`Res.name`), so the bound is on the product's own exponent, and walked again (the bound
            # then from the rule above)
            op, a = f['ops'][i0]
            if op == 'deref' and a[1] == st:
                for r in (('name', a[0]), ('lt', ('ex', ('fr', a[0]), 0), ('num', REGION[st]))):
                    if r not in self.res[i0]: self.res[i0].append(r)
                f['tabs'][i0 + 1] = REGION[st]; self.new = True; return False
            n = st + REGION[st] - k[1]
            x = k[2][0][0]
            r = ('lt', ('ex', x, 0), ('num', n))
            if f['tabs'][i0 + 1] != n: f['tabs'][i0 + 1] = n; self.new = True
            if r not in self.res[i0]:
                self.res[i0].append(r); self.new = True
            A.lt.add((r[1], r[2])); return True
        # a table read at an index of small known bound, over the interface, its callers holding the table but
        # not the index's bound (`runPre`): every cell the index can name
        if k[0] == 0 and depth == 0 and f['name'] in RUNPRE:
            for b, e in k[2]:
                Q = (0, 0, tuple(x for x in k[2] if x[0] != b))
                nb = A.bound(('ex', b, 1))
                if nb is not None and 0 < nb <= 64 and Q[2] and ifaceMono(f, Q):
                    r = (Q, ('num', 0), ('num', nb), e, k[1])
                    self.preR.add(r); self.new = True; A.r.add(r); return True
        if k[0] == 0 and k[2] and ifaceMono(f, k):
            self.pre.add(k); self.new = True; A.h.add(k); return True
        # a table read at a loaded offset, inside a table the caller holds
        tab = TABLES.get(tuple(sorted(m for m in calls if f['name'] in calls[m] and m != f['name'])))
        # an entry's cell: one pointer, the other bases' powers whole entries
        if tab is not None and k[0] == 0 and k[2] and depth == 0 and \
                sorted(e % tab[2] for b, e in k[2]) == [0] * (len(k[2]) - 1) + [1]:
            T, hi, S = tab
            bs = [((0, 0, ((T, 1),)), ('num', 0), hi, S, c) for c in range(S)]
            for b in bs: self.preR.add(b); A.r.add(b)
            # the entry's whole stride of cells, once
            a = ((0, k[1] - k[1] % S, k[2]), ('num', 0), ('num', S), 1, 0)
            if not any(('sub', a, bs) in rs for rs in self.res.values()): self.addRes(i0, ('sub', a, bs))
            A.r.add(a); return True
        # a table written at the loaded words of a permutation: every cell of a block, once the table is
        # written at the words of the hinted run's cells `[q]·[lo, hi)`, the permutation mapping each
        # block of its cells onto the same block (the read's offset in it)
        if k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and depth == 0:
            b = k[2][0][0]
            byq = collections.defaultdict(set)
            for m in A.h:
                if m[0] == 0 and m[1] == 0 and len(m[2]) == 2 and (b, 1) in m[2] and all(e == 1 for _, e in m[2]):
                    x = next(y for y, _ in m[2] if y != b)
                    if x[0] == 'hp': byq[x[1]].add(x[2])
            for q, js in sorted(byq.items()):
                if k[1] not in js: continue
                lo, hi = k[1], k[1] + 1
                while lo - 1 in js: lo -= 1
                while hi in js: hi += 1
                if hi - lo < 2 or not any(r[0] == root(q) and r[1][0] == 'num' and r[1][1] <= lo and
                                          r[2][0] == 'num' and r[2][1] >= hi and r[3:] == (1, 0) for r in A.r):
                    continue
                P = [(0, 0, tuple(sorted(((b, 1), (('hp', q, j), 1))))) for j in range(lo, hi)]
                a = ((0, 0, ((b, 1),)), ('num', lo), ('num', hi), 1, 0)
                r = ('sub', a, [(m, ('num', 0), ('num', 1), 1, 0) for m in P])
                self.addRes(i0, r); self.prunable.append((i0, r)); A.r.add(a); return True
        # a bounded table read: the loads its uncovered cells were linked to
        if self.w is not None and k[0] == 0 and depth < 4:
            got = False
            for b, e in k[2]:
                q = (0, 0, tuple(x for x in k[2] if x[0] != b))
                n = A.bound(('ex', b, 1))
                if n is None or n > 64: continue
                for j in range(n):
                    pt = shift(q, e * j + k[1])
                    if A.covered(pt): continue
                    for c in self.w.lnks.get(pt, []):
                        if c in self.w.lnk and self.key(self.w.lnk[c][0], self.w.lnk[c][1], A, depth + 1): got = True
            if got: A.h.add(k); return True
        if k[0] != 0 or not k[2]: return False
        for (x, e) in k[2]:
            if x[0] != 'fr': continue
            Q = tuple((b, ee) for b, ee in k[2] if b != x)
            if not (Q and ifaceMono(f, (0, 0, Q))): continue
            for (p, hi) in sorted(A.lt, key=lambda t: (t[1][0] != 'num', t[1][1] if t[1][0] == 'num' else 0)):
                if p == ('ex', x, 0) and ifaceIdx(f, hi) and hi != ('num', MAXCELLS):
                    r = ((0, 0, Q), ('num', 0), hi, e, k[1])
                    S = NARROW[f['name']].get(r)
                    if S:
                        # its callers hold every `S`-th cell: that part, the read inside it (`narrow`)
                        r = ((0, 0, Q), ('num', 0), ('num', hi[1] // S), e * S, k[1])
                        a = ((0, k[1], k[2]), ('num', 0), ('num', 1), 1, 0)
                        self.preR.add(r); A.r.add(r); self.addRes(i0, ('sub', a, [r])); A.r.add(a); return True
                    self.preR.add(r); self.new = True; A.r.add(r); return True
        return self.permBlock(k, i0, A) or self.runPoint(k, i0, A) or self.blkPoint(k, i0, A) or \
            self.streamRead(k, i0, A)

    def streamRead(self, k, i0, A):
        """A cell past one pointer, in a function the proof stream is passed to: inside the stream (`Res.sub`),
        the stream's run a precondition (held by a caller or, in a loop, by the function that runs it)."""
        st = STREAMS.get(self.f['name'])
        if st is None or k[0] != 0 or len(k[2]) != 1 or k[2][0][1] != 1 or k[2][0][0] == st: return False
        # a buffer this function allocates is not the stream
        if k[2][0][0][0] == 'fr' and k[2][0][0][1] in allocs(self.f): return False
        b = ((0, 0, ((st, 1),)), ('num', 0), ('num', STREAM_CAP), 1, 0)
        if st[0] == 'hp' or st[1] in params(self.f):
            if b not in self.preR: self.preR.add(b); self.new = True
            A.r.add(b)
        elif b not in A.r: return False
        a = ((0, k[1], k[2]), ('num', 0), ('num', 1), 1, 0)
        self.addRes(i0, ('sub', a, [b])); A.r.add(a); return True

    def runPoint(self, k, i0, A):
        """A cell `Q·x·g^c`, `x` one base, inside a known run over `Q` from `0` of stride 1 up to an exponent
        (`Res.sub`: `x`'s exponent plus `c` below the run's bound)."""
        if k[0] != 0 or len(k[2]) < 2: return False
        for B, e in k[2]:
            Q = (0, 0, tuple(y for y in k[2] if y[0] != B))
            if e != 1: continue
            for R in sorted(A.r, key=str):
                if R[0] == Q and R[1] == ('num', 0) and R[3] == 1 and R[4] == 0 and R[2][0] == 'ex':
                    a = ((0, k[1], k[2]), ('num', 0), ('num', 1), 1, 0)
                    self.addRes(i0, ('sub', a, [R])); A.r.add(a); return True
        return False

    def permBlock(self, k, i0, A):
        """A table `[T]` read at the word a permutation's cell `r` holds (`[q]·g^r`, loaded), `[T]·g^c` known
        written at the block of consecutive offsets `[lo, hi)` around `r`: the read inside it (`Res.sub`),
        the permutation mapping each block of its cells onto the same block of the table's."""
        if k[0] != 0 or len(k[2]) != 2 or any(e != 1 for _, e in k[2]): return False
        ts = [b for b, _ in k[2] if b[0] == 'fr']; ps = [b for b, _ in k[2] if b[0] == 'hp']
        if len(ts) != 1 or len(ps) != 1: return False
        T, r, c = ts[0], ps[0][2], k[1]
        q = (0, 0, ((T, 1),))
        if not A.covered(shift(q, c + r)): return False
        lo, hi = r, r + 1
        while lo > 0 and A.covered(shift(q, c + lo - 1)): lo -= 1
        while hi - lo < 4096 and A.covered(shift(q, c + hi)): hi += 1
        if hi - lo < 2: return False
        a = ((0, c, k[2]), ('num', 0), ('num', 1), 1, 0)
        r = ('sub', a, [(q, ('num', lo), ('num', hi), 1, c)])
        self.addRes(i0, r); self.prunable.append((i0, r)); A.r.add(a); return True


def allocs(f):
    """The frame cells whose words this function's allocation hints write."""
    if 'allocs' not in f:
        f['allocs'] = {h[1] for hs in f['hints'].values() for h in hs
                       if h[0] in ('al', 'ad', 'aa', 'af') or (h[0] == 'lt' and h[2] == 'e')}
    return f['allocs']


def statMono(f):
    """Each cell's word as a product, from the function's own `SET`s and `MUL`s, its named products
    (`names`) their cells' words."""
    m = {}
    named = {r[1] for rs in names(f).values() for r in rs}
    for op, a in f['ops']:
        if op == 'set':
            e = POWS.get(a[1]) if a[2] == 0 else None
            m[a[0]] = gp(e) if e is not None else None
        elif op == 'mul':
            x = m.get(a[0], root(a[0])); y = m.get(a[1], root(a[1]))
            m[a[2]] = None if x is None or y is None else root(a[2]) if a[2] in named else mul(x, y)
        elif op == 'xor': m[a[2]] = None
    return m


def callArgs(f):
    """At each call or tail call to a known entry: the callee and its frame cells' caller cells."""
    sets = {}; args = collections.defaultdict(dict); out = []
    for op, a in f['ops']:
        if op == 'set': sets[a[0]] = a[1] if a[2] == 0 else None
        if op == 'deref' and a[3] == '.cell': args[a[0]][a[1]] = a[2]
        if op == 'jump':
            g = byentry.get(POWS.get(sets.get(a[1]), -1))
            if g is not None and a[2] in args: out.append((g['name'], dict(args[a[2]])))
    return out


def tables():
    """The tables each function holds as a base cell and a length cell: an allocation whose size is a
    cell's word to a power (`L^S`, `S` cells an entry), and, at every call from another function, a
    pair of argument cells its caller holds as one."""
    T = collections.defaultdict(set)
    for f in fns.values():
        m = statMono(f)
        for hs in f['hints'].values():
            for h in hs:
                c = h[2] if h[0] == 'ad' else h[3] if h[0] == 'lt' and h[2] == 'e' else None
                sz = m.get(c, root(c)) if c is not None else None
                if sz and sz[0] == 0 and sz[1] == 0 and len(sz[2]) == 1 and sz[2][0][0][0] == 'fr':
                    T[f['name']].add((h[1], sz[2][0][0][1], sz[2][0][1]))
    into = collections.defaultdict(list)
    for f in fns.values():
        for g, args in callArgs(f):
            if g != f['name']: into[g].append((f['name'], args))
    changed = True
    while changed:
        changed = False
        for g, cl in into.items():
            cand = None
            for n, args in cl:
                inv = collections.defaultdict(list)
                for o, x in args.items(): inv[x].append(o)
                here = {(ob, ol, S) for pb, pl, S in T[n] for ob in inv[pb] for ol in inv[pl]}
                cand = here if cand is None else cand & here
            if cand and not cand <= T[g]: T[g] |= cand; changed = True
    return T



# consecutive heap cells over one product, at least this many, are a run in a signature
COMPACT = 8


def compact(ms, rs):
    """Points `ms` (products `q·g^k`), each `COMPACT` or more consecutive over one `q` made a run."""
    by = collections.defaultdict(list)
    for m in ms: by[(m[0], m[2])].append(m[1])
    pts = set(); runs = set(rs)
    for (fp, bs), ks in by.items():
        ks = sorted(set(ks)); i = 0
        while i < len(ks):
            j = i
            while j + 1 < len(ks) and ks[j + 1] == ks[j] + 1: j += 1
            if fp == 0 and bs and j + 1 - i >= COMPACT:
                runs.add(((0, 0, bs), ('num', ks[i]), ('num', ks[j] + 1), 1, 0))
            else:
                pts.update((fp, k, bs) for k in ks[i:j + 1])
            i = j + 1
    return pts, runs


def mkSig(f, pre, preR, ret=(), post=(), postR=(), postL=(), preP=None, postP=(), postLP=(), retV=()):
    if f['name'].startswith('verify_merkle_cap'): pre, preR = compact(pre, preR)
    post, postR = compact(post, postR)
    loop = f['name'] in isloop
    term = [(('ex', ('fr', 2), 0), BOUND[f['name']])] if loop else []
    preP = sorted((r, tuple(sorted(os))) for r, os in (preP or {}).items())
    return Sig(f['entry'], list(range(2 + f.get('nargs', 0))), selfc.get(f['entry']), sorted(pre), sorted(preR), term,
               ret, sorted(post), sorted(postR), sorted(postL), preP, sorted(postP), sorted(postLP), sorted(retV))


def renameRet(f, A, m, heap=False):
    """A product over the walk's bases in the function's own terms (parameters, return cells), and with
    `heap`, an own word stored at `[p]·g^d`, `p` a parameter, as that cell's (`hp p d`)."""
    rets = range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0))
    ren = {}
    for r in rets:
        x = A.v.get(r)
        if x and x[0] == 'm' and x[1][0] == 0 and x[1][1] == 0 and len(x[1][2]) == 1 and x[1][2][0][1] == 1:
            ren.setdefault(x[1][2][0][0], ('fr', r))
    if heap:
        ps = params(f)
        for k, x in sorted(A.hv.items(), key=str):
            if k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and k[2][0][0][0] == 'fr' and k[2][0][0][1] in ps and \
                    x[0] == 'm' and x[1][0] == 0 and x[1][1] == 0 and len(x[1][2]) == 1 and x[1][2][0][1] == 1 and \
                    x[1][2][0][0][0] == 'fr' and x[1][2][0][0][1] not in ps:
                ren.setdefault(x[1][2][0][0], ('hp', k[2][0][0][1], k[1]))
    bs = tuple(sorted((ren.get(b, b), e) for b, e in m[2]))
    return (m[0], m[1], bs)


def ptrRuns(f, A):
    """Runs of pointers the heap words show: consecutive cells over one interface product, each
    holding a word with the same leading cells past it written."""
    by = collections.defaultdict(dict)
    for k, x in A.hv.items():
        if x[0] != 'm': continue
        k2 = renameRet(f, A, k)
        if not okIface(f, (k2[0], 0, k2[2])): continue
        n = 0
        while n < 64 and A.covered(shift(x[1], n)): n += 1
        if n: by[(k2[0], k2[2])][k2[1]] = n
    out = set()
    for (fp, bs), d in by.items():
        ks = sorted(d); i = 0
        while i < len(ks):
            j = i
            while j + 1 < len(ks) and ks[j + 1] == ks[j] + 1: j += 1
            if j > i:
                n = min(d[k] for k in ks[i:j + 1])
                out.add((((0, 0, bs), ('num', ks[i]), ('num', ks[j] + 1), 1, 0), tuple(range(n))))
            i = j + 1
    return out


def okIface(f, m):
    rets = set(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0)))
    return m[0] == 0 and m[2] and all(b[1] in params(f) or (b[0] == 'fr' and b[1] in rets) for b, e in m[2])


def names(f):
    """The products the walk names by their cells (`Res.name`), at the next offset: a `MUL` of two or
    more words each once, itself never a pointer but to a jump table, each a sum, a word no arithmetic
    of the function writes (an argument, a load's, a hint's), a named product or a power of `g`."""
    c = f['ops']; num = {}; out = {}
    ptrs = {a[0] for i, (op, a) in enumerate(c) if op == 'deref' and (i + 1) not in f['tabs']}
    writes = {a[2] for op, a in c if op in ('xor', 'mul')} | {a[0] for op, a in c if op == 'set'}
    for o in {x for op, a in c if op == 'mul' for x in a[:2]} - writes: num[o] = {o: 1}
    for i, (op, a) in enumerate(c):
        if op == 'xor': num[a[2]] = {a[2]: 1}
        elif op == 'set': num.pop(a[0], None) if POWS.get(a[1]) is None or a[2] != 0 else num.__setitem__(a[0], {})
        elif op == 'mul' and a[0] in num and a[1] in num:
            m = dict(num[a[0]])
            for b, e in num[a[1]].items(): m[b] = m.get(b, 0) + e
            if len(m) >= 2 and all(e == 1 for e in m.values()) and a[2] not in ptrs and i + 1 < len(c):
                out.setdefault(i + 1, []).append(('name', a[2])); num[a[2]] = {a[2]: 1}
            else: num[a[2]] = m
        elif op == 'mul': num.pop(a[2], None)
    return out


# tables of entries a function reads at loaded offsets, by its callers: the one table of entries of
# several cells the caller holds, its base and length the caller's cells, as strided runs
TABLES = {(n,): (('hp', 1, b), ('ex', ('hp', 1, l), 0), S) for n, ts in tables().items()
          if len([t for t in ts if t[2] > 1]) == 1 for b, l, S in ts if S > 1}


# an exponent's bound for `smallIdx`, far above any the guest computes and below `2^62`
SMALL = 2 ** 32

# runs a function reads at a bounded index, of which its callers hold every `S`-th cell: function -> {run: S}
NARROW = collections.defaultdict(dict)
# the functions inferred so far
DONE = set()
# functions whose bounded table reads over the interface are runs, not points (`Infer.runPre`)
RUNPRE = set()
# arms storing copies of cells their siblings need, with those cells (`armStrides`)
COPYPRE = {}
# functions whose table calls' arms guarantee their blocks as strided runs (`armStrides`, `Infer.splitRes`)
STRIDES = set()
# functions that pass with residuals outside the families `Res/SelDefs.lean` and `Res/SubDefs.lean` accept,
# held as failing (their callees' narrowings undone) until those families take them; by stable name, a loop's
# its caller's and its rank, so a guest edit renumbering the loops leaves it unchanged
HELD_NS = {'claim_list_digest', 'log2_ceil_in_the_exponent__L0_L34', 'log2_ceil_in_the_exponent__L16_L34', 'main',
           'verify_bus_gkr', 'verify_bus_gkr_loop0', 'verify_bus_gkr_loop0_loop0', 'verify_keccak', 'verify_sub',
           'verify_tables'}
HELD = {f['name'] for f in fns.values() if f['ns'] in HELD_NS}
assert len(HELD) == len(HELD_NS), HELD_NS - {fns[n]['ns'] for n in HELD}


# each function's last inference, its signature and residuals (a narrowed callee's replaced)
LAST = {}


def streams():
    """The proof stream's base, per function: the cell `verify_sub`'s witness hint `stream` writes, passed
    down as an argument, and in a loop of a function that holds it, the caller's cell (`hp 1 o`)."""
    S = {}; cap = None
    for f in fns.values():
        for hs in f['hints'].values():
            for h in hs:
                if h[0] == 'wh' and h[1] == 'stream':
                    assert h[3] == 0 and cap is None, h
                    S[f['name']] = ('fr', h[2]); cap = h[4]
    changed = True
    while changed:
        changed = False
        for f in fns.values():
            st = S.get(f['name'])
            if st is None or st[0] != 'fr': continue
            for g, args in callArgs(f):
                if g == f['name']: continue
                for o, x in args.items():
                    if x == st[1] and g not in S: S[g] = ('fr', o); changed = True
    for n in list(S):
        if S[n][0] != 'fr': continue
        for m in calls[n]:
            if m in isloop and m not in S and m != n: S[m] = ('hp', 1, S[n][1])
    return S, cap


STREAMS, STREAM_CAP = streams()


def infer(n):
    DONE.add(n)
    LAST.pop(n, None)
    mark = {g: dict(v) for g, v in NARROW.items()}
    try:
        try: LAST[n] = infer1(n, False)
        except Fail as e:
            try: LAST[n] = infer1(n, True)
            except Fail: raise e
        if n in HELD:
            del LAST[n]
            raise Fail(('held', n))
        return LAST[n]
    except Fail:
        # a failing caller's narrowings undone, its callees inferred again
        for g in [g for g in NARROW if NARROW[g] != mark.get(g, {})]:
            NARROW[g] = dict(mark.get(g, {}))
            try: infer(g)
            except Fail: E.sigs[fns[g]['entry']] = mkSig(fns[g], [], [], list(range(
                2 + fns[g].get('nargs', 0), 2 + fns[g].get('nargs', 0) + fns[g].get('nret', 0))))
        raise


def tableArms(f):
    """Each table call's arms, in order, every slot a known function."""
    out = []
    for i in sorted(f['tabs']):
        op, a = f['ops'][i - 1]
        gs = [byentry.get(JT.get(a[1] + j)) for j in range(f['tabs'][i])]
        if gs and all(gs): out.append([g['name'] for g in gs])
    return out


def block(G, Q):
    """How many cells from `Q`'s start a signature guarantees, consecutively."""
    ks = {m[1] for m in G.post if (0, 0, m[2]) == Q}
    for q, lo, hi, S, d in G.postR:
        if q[1] == 0 and (0, 0, q[2]) == Q and S == 1 and lo[0] == 'num' and hi[0] == 'num':
            ks |= {d + j for j in range(lo[1], hi[1])}
    M = 0
    while M in ks: M += 1
    return M


def armStrides(f):
    """A table call's arms, arm `j` guaranteeing `S·j` cells from the start of one product over their
    parameters, `S ≥ 2` and three or more arms: each arm's block also as `S` runs of stride `S`, `j` points
    each, which the arms met take up to the selector (`armRuns`). An arm short of its block because it stores
    copies of cells its siblings need is inferred again needing those cells (`COPYPRE`). Asked for by
    `Infer.splitRes` (`STRIDES`)."""
    for arms in tableArms(f):
        if len(arms) < 3 or any(a in isloop for a in arms): continue
        sigs = lambda: [E.sigs.get(fns[a]['entry']) for a in arms]
        Gs = sigs()
        if not all(Gs): continue
        nn = len(arms) - 1
        for Q in sorted({(0, 0, m[2]) for m in Gs[-1].post if m[0] == 0 and m[2]} |
                        {(0, 0, q[2]) for q, lo, hi, S, d in Gs[-1].postR if q[0] == 0 and q[1] == 0 and q[2]}):
            S = block(Gs[-1], Q) // nn
            if S < 2: continue
            short = [a for j, (a, G) in enumerate(zip(arms, Gs)) if block(G, Q) < S * j]
            if short and not any(a in calls[y] for a in short for y in DONE if y != f['name']):
                need = set().union(*[set(G.pre) for G in Gs])
                for a in short:
                    if a in COPYPRE: continue
                    COPYPRE[a] = need
                    try: infer(a)
                    except Fail: del COPYPRE[a]; infer(a)
                Gs = sigs()
            if any(block(G, Q) < S * j for j, G in enumerate(Gs)): continue
            for j, G in enumerate(Gs):
                for d in range(S if j else 0):
                    r = (Q, ('num', 0), ('num', j), S, d)
                    if r not in G.postR: G.postR.append(r)


def infer1(n, named):
    f = fns[n]
    I = Infer(f)
    if named:
        for i, rs in names(f).items(): I.res[i] = list(rs)
    main = n == 'main'
    for it in range(200):
        if n in STRIDES: armStrides(f)
        sig = mkSig(f, I.pre, I.preR, preP=I.preP)
        E.sigs[f['entry']] = sig
        I.new = False
        w = Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main, demand=I.demand)
        I.w = w
        try:
            w.run(f['ops'])
        except Fail as e:
            if not I.new:
                # loop transport: a run of pointers at the counter's point, over the counter's range
                if n in isloop and e.args[0][0] == 'preP' and isinstance(e.args[0][2], tuple):
                    r = e.args[0][3]
                    if r in I.preP and r[1] == ('ex', ('fr', 2), 0) and r[2] == ('ex', ('fr', 2), 1):
                        I.preP[(r[0], r[1], BOUND[n], r[3], r[4])] = I.preP.pop(r)
                        continue
                # loop transport: generalize uncovered pre points over the counter
                if n in isloop and e.args[0][0] == 'pre' and isinstance(e.args[0][2], tuple):
                    m = e.args[0][3]
                    S = dict(m[2]).get(('fr', 2))
                    if S:
                        Q = tuple((b, x) for b, x in m[2] if b != ('fr', 2))
                        I.pre.discard(m)
                        I.preR.add(((0, 0, Q), ('ex', ('fr', 2), 0), BOUND[n], S, m[1]))
                        continue
                raise
            continue
        if not I.new and not I.splitRes(w) and not I.armCopies(w) and not I.copyPre(w): break
    else:
        raise Fail(('nofix',))
    # posts
    nr = f.get('nret', 0); na = f.get('nargs', 0)
    rets = list(range(2 + na, 2 + na + nr))
    ret = [o for o in rets if all(o in A.w for A in w.rets)] if w.rets else rets
    post = None; postR = None
    for A in w.rets:
        # an own buffer's cells and runs through the parameter cell it is stored at (`keccak_layer`'s point)
        ks = {renameRet(f, A, k, True) for k in A.h}
        ks = {k for k in ks if okIface(f, k)}
        post = ks if post is None else post & ks
        rs = set()
        for (q, lo, hi, S, d) in A.r:
            q2 = renameRet(f, A, q, True)
            if okIface(f, q2) and ifaceIdx(f, lo) and ifaceIdx(f, hi): rs.add((q2, lo, hi, S, d))
        postR = rs if postR is None else postR & rs
    post = post or set(); postR = postR or set()
    retV = set()
    if w.rets and n not in isloop:
        for o in ret:
            ms = {A.mono(o) for A in w.rets}
            if len(ms) == 1:
                m = ms.pop()
                if m is not None and m[0] == 0 and m[2] and all(b[0] == 'fr' and b[1] in params(f) for b, e in m[2]):
                    retV.add((o, m))
    postP = None
    for A in w.rets:
        ps = set()
        for (q, lo, hi, S, d), os in A.p:
            q2 = renameRet(f, A, q)
            if okIface(f, q2) and ifaceIdx(f, lo) and ifaceIdx(f, hi): ps.add(((q2, lo, hi, S, d), os))
        ps |= ptrRuns(f, A)
        postP = ps if postP is None else postP & ps
    postP = postP or set()
    postL = set(); postLP = set()
    if n in isloop:
        ends = w.rets + [t[0] for t in w.tails]
        cand = None
        for A in ends:
            ks = {k for k in A.h if k[0] == 0 and dict(k[2]).get(('fr', 2)) and ifaceMono(f, k)}
            # the points of a run over a product with the counter
            for (q, lo, hi, S, d) in A.r:
                if q[0] == 0 and dict(q[2]).get(('fr', 2)) and ifaceMono(f, q) and lo[0] == 'num' and hi[0] == 'num' and hi[1] - lo[1] <= 128:
                    ks |= {shift(q, S * j + d) for j in range(lo[1], hi[1])}
            cand = ks if cand is None else cand & ks
        cand = cand or set()
        for k in cand:
            S = dict(k[2])[('fr', 2)]
            Q = tuple((b, x) for b, x in k[2] if b != ('fr', 2))
            # an entry point the iteration writes a stride on: the caller has it from the next's run (`extR`)
            if k in I.pre and shift(k, S) in cand: continue
            if Q: postL.add(((0, 0, Q), ('ex', ('fr', 2), 0), BOUND[n], S, k[1]))
        pcand = None
        for A in ends:
            ks = {}
            for (q, lo, hi, S, d), os in A.p:
                if q[0] == 0 and dict(q[2]).get(('fr', 2)) and ifaceMono(f, q) and lo[0] == 'num' and hi[0] == 'num' and hi[1] - lo[1] <= 128:
                    for j in range(lo[1], hi[1]): ks[shift(q, S * j + d)] = set(os)
            for k, x in A.hv.items():
                if k[0] == 0 and dict(k[2]).get(('fr', 2)) and ifaceMono(f, k) and x[0] == 'm':
                    m = x[1]
                    os = {h[1] - m[1] for h in A.h if h[0] == m[0] and h[2] == m[2] and h[1] >= m[1]} | set(range(64))
                    os = {o for o in os if o < 2 ** 30 and A.covered(shift(m, o))}
                    if os: ks[k] = os
            pcand = ks if pcand is None else {k: pcand[k] & ks[k] for k in pcand if k in ks and pcand[k] & ks[k]}
        for A in ends:
            pass
        for k, os in (pcand or {}).items():
            S = dict(k[2])[('fr', 2)]
            Q = tuple((b, x) for b, x in k[2] if b != ('fr', 2))
            if Q: postLP.add((((0, 0, Q), ('ex', ('fr', 2), 0), BOUND[n], S, k[1]), tuple(sorted(os))))
        post = set(); postR = set(); postP = set()
    sig = mkSig(f, I.pre, I.preR, ret, post, postR, postL, I.preP, postP, postLP, retV)
    E.sigs[f['entry']] = sig
    # the final check: no demand; a guarantee that does not check dropped, one at a time
    for _ in range(64):
        w = Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main)
        try:
            w.run(f['ops']); break
        except Fail as e:
            kind, item = e.args[0][0], e.args[0][2] if len(e.args[0]) > 2 else None
            lists = {'post': sig.post, 'postR': sig.postR, 'postP': [q for q in sig.postP]}
            if kind not in lists: break
            if kind == 'postP': sig.postP = [q for q in sig.postP if q != (item, e.args[0][3])]
            else: lists[kind].remove(item)
            E.sigs[f['entry']] = sig
    else:
        raise Fail(('final',))
    try:
        Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main).run(f['ops'])
    except Fail:
        # drop what does not check
        sig = mkSig(f, I.pre, I.preR, ret, set(), set(), set(), I.preP, retV=retV)
        E.sigs[f['entry']] = sig
        Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main).run(f['ops'])
    # a block read off an earlier pass's state may be a part of the true one: dropped unless needed
    for i, r in sorted(I.prunable, key=str):
        if r not in I.res.get(i, []): continue
        j = I.res[i].index(r); I.res[i].remove(r)
        try: Walk(E, f['entry'], f['count'], sig, f['hints'], I.res, f['tabs'], main=main).run(f['ops'])
        except Fail: I.res[i].insert(j, r)
    return sig, dict(I.res)


__import__('rules_da').install(globals())
__import__('rules_fix').install(globals())

if __name__ == '__main__':
    sigs = {}; fails = {}; res = {}
    for n in order:
        f = fns[n]
        try:
            sigs[n], res[n] = infer(n)
        except Fail as e:
            fails[n] = e.args[0]
            sig = mkSig(f, [], [], list(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0))))
            E.sigs[f['entry']] = sig; sigs[n] = sig
    for n, (s, r) in LAST.items(): sigs[n], res[n] = s, r
    print('fail', len(fails), collections.Counter(v[0] for v in fails.values()).most_common())
    rk = collections.Counter(r[0] for n in res for rs in res[n].values() for r in rs)
    print('resid kinds', rk, 'fns with resid', sum(1 for n in res if any(res[n].values())))
    print('clean', sum(1 for n in sigs if n not in fails and not any(res.get(n, {}).values())))
    # passing with every callee passing, transitively (a failing callee's signature is empty)
    closed = set()
    for n in order:
        if n not in fails and all(m in closed for m in calls[n] if m != n): closed.add(n)
    print('closed', len(closed), 'of', len(fns))
    rootf = [n for n in fails if not any(m in fails for m in calls[n] if m != n)]
    print('root failures', len(rootf), collections.Counter(fails[n][0] for n in rootf))
    for n in sorted(rootf, key=lambda n: fns[n]["count"]):
        e = fails[n]
        print(n, fns[n]['count'], str(e[:4] if isinstance(e, tuple) else e)[:200])
