"""A mirror of `LeanVM/Guest/CoreMode/Frame.lean`, rule for rule: the frame walk (`frameOk`) over
the executor's instructions, with `ExecCore`'s symbolic step (`stepI`) for what is known of the
frame's words. Used by `frame_gen.py` to choose the data (the oracle, residual divisors, table targets,
windows) and to report which functions pass."""
import collections

ENV_DEPTH = 14          # `Exec.envDepth`: frame offsets below 2^13 kept
HQ_SHIFT = 2 ** 14      # `hqKey q o = q * 2^14 + o`
KECCAK_N = {'.one': 1, '.two': 2, '.all': 13}


class Fail(Exception):
    pass


def keccakIns(m0, m1, m2, m3, tail, b8, cap):
    return [m0, m1, m2, m3, tail, tail + 1, tail + 2, tail + 3, b8, cap, cap + 1, cap + 2, cap + 3]


# ------------------------------------------------------------------ ExecCore's step (a mirror)
# Sym: ('z',) | ('gp', e) | ('fpg', e)
Z = ('z',)


def okKey(o):
    """A key the tries of depth `ENV_DEPTH` keep (`Trie.set` drops deeper ones)."""
    return o < 2 ** ENV_DEPTH - 1


class XSt:
    __slots__ = ('env', 'mem', 'prev')

    def __init__(self, env, mem=(), prev=()):
        self.env = env; self.mem = list(mem); self.prev = list(prev)

    def copy(self):
        return XSt(dict(self.env), self.mem, self.prev)


def expo(s):
    return s[1] if s is not None and s[0] == 'gp' else None


def learn(env, o, v):
    if o not in env and okKey(o): env[o] = v


def memFind(mem, q, off):
    for (q2, o2, v) in mem:
        if q2 == q and o2 == off: return v
    return None


class Facts:
    def __init__(self, env, fpOne, arms, scaled, pows):
        self.env = env; self.fpOne = fpOne; self.arms = arms; self.scaled = scaled; self.pows = pows

    def symOf(self, k0, k1):
        if k1 != 0: return None
        if k0 == 0: return Z
        if k0 == 1: return ('gp', 0)
        e = self.pows.get(k0)
        return ('gp', e) if e is not None else None

    def self_(self, t):
        return t == ('fpg', 0) or (t == ('gp', 0) and self.fpOne)


def rangeFact(env, y, prev):
    if len(prev) == 2 and prev[0][1][0] == 'mul' and prev[1][1][0] == 'deref':
        x, y2, z = prev[0][1][1]
        x2, o2, _, mode = prev[1][1][1]
        if y2 == y and x2 == x and o2 == 0 and mode == '.cell':
            k = expo(env.get(z))
            if k is not None:
                return [('range', x, y, k + 1)] if k < 2 ** 63 else [('powPair', x, y, z)]
            return [('powPair', x, y, z)]
    return []


def neFacts(p, prev):
    if prev and prev[0][1][0] == 'mul':
        x, _, p2 = prev[0][1][1]
        if p2 == p:
            out = [('nz', x)]
            rest = prev[1:]
            if len(rest) == 1 and rest[0][1][0] == 'xor' and rest[0][1][1][2] == x:
                out.append(('ne',) + tuple(rest[0][1][1][:2]))
            return out
    return []


def nonJump(F, pc, st, op, a):
    """(facts, env, mem) after a non-`JUMP` (`Exec.nonJump`); `env` a new dict."""
    env = dict(st.env)
    mem = list(st.mem)
    facts = []
    if op == 'xor':
        if env.get(a[2]) == Z: facts.append(('eq', a[0], a[1]))
    elif op == 'mul':
        x, y, c = a
        if x == y == c: facts.append(('bool', c))
        if env.get(y) == ('gp', 0): facts.append(('copy', c, x))
        elif env.get(x) == ('gp', 0): facts.append(('copy', c, y))
        if x in F.scaled:
            s = env.get(x)
            if s is not None and s[0] == 'fpg':
                e2 = expo(env.get(y))
                if e2 is not None: learn(env, c, ('fpg', s[1] + e2))
    elif op == 'set':
        o, k0, k1 = a
        if k0 == 1 and k1 == 0: facts += neFacts(o, st.prev)
        v = F.symOf(k0, k1)
        if v is not None and okKey(o): env[o] = v
    elif op == 'deref':
        o1, o2, o3, mode = a
        if o2 == 0 and mode == '.cell': facts += rangeFact(env, o1, st.prev)
        if mode == '.fp': mem = ([(o1, o2, ('fpg', 0))] + mem)[:4]
        elif mode == '.pc': mem = ([(o1, o2, ('gp', pc + 2))] + mem)[:4]
        else:
            v = memFind(mem, o1, o2)
            if v is not None: learn(env, o3, v)
            elif o2 == 0 and env.get(o3) is not None: mem = ([(o1, 0, env[o3])] + mem)[:4]
    return facts, env, mem


def tgtOf(s, o):
    if s is not None and s[0] in ('fpg', 'gp'): return s
    return ('cell', o)


def jumpKind(F, entry, ln, i, st, od, of):
    if od == 0 and of == 1: return ('ret',), []
    pt, ft = tgtOf(st.env.get(od), od), tgtOf(st.env.get(of), of)
    if F.self_(ft):
        if pt[0] == 'gp':
            e = pt[1]
            if entry + i < e < entry + ln: return ('next', e - entry), [e - entry]
            return ('jump', pt, ft), []
        if pt[0] == 'cell': return ('jump', pt, ft), F.arms.get(i, [])
        return ('jump', pt, ft), []
    if ft[0] == 'cell':
        q = ft[1]
        r = expo(memFind(st.mem, q, 0))
        if r is not None and memFind(st.mem, q, 1) == ('fpg', 0):
            return ('call', pt, q, r), ([r - entry] if entry + i < r < entry + ln else [])
    return ('jump', pt, ft), []


# ------------------------------------------------------------------ the frame walk
class FS:
    """A path's state (`FSt`): ExecCore's state, written frame offsets `w`, frame cells nonzero in
    the reference `nz`, heap cells past frame cells' words written `hq` ((q, o)), self pointers
    `hs` ((q, o): the cell `[q]·g^o` holds `[q]`), and copies into the own frame `cp` (t -> c:
    frame cell t holds frame cell c's word)."""
    __slots__ = ('st', 'w', 'nz', 'hq', 'hs', 'cp', 'one')

    def __init__(self, st, w, nz, hq, hs, cp, one):
        self.st = st; self.w = w; self.nz = nz; self.hq = hq; self.hs = hs; self.cp = cp; self.one = one

    def copy(self):
        return FS(self.st.copy(), set(self.w), set(self.nz), set(self.hq), set(self.hs), dict(self.cp), dict(self.one))


def meet(A, B):
    env = {o: v for o, v in A.st.env.items() if B.st.env.get(o) == v}
    return FS(XSt(env), A.w & B.w, A.nz & B.nz, A.hq & B.hq, A.hs & B.hs,
              {t: c for t, c in A.cp.items() if B.cp.get(t) == c}, {t: c for t, c in A.one.items() if B.one.get(t) == c})


class Walk:
    """`frameOk`: `F` the executor's facts, `sigs` the callees' frame signatures by entry pc
    (`(entry, self, ret)`), `hints` by offset, `nzr` residual divisors by offset, `tgt` the targets
    of jumps through a cell by offset (pcs), `O` the oracle's offsets, `S` the stores' (a `DEREF` there
    must find its frame side written), `main` whether the frame is
    `main`'s. `need(kind, i, x)` is called where the Lean walk fails; True continues (inference)."""

    def __init__(self, F, entry, ln, sig, sigs, hints, nzr, tgt, O, halt, need=None, S=frozenset()):
        self.F = F; self.entry = entry; self.len = ln; self.sig = sig; self.sigs = sigs
        self.hints = hints; self.nzr = nzr; self.tgt = tgt; self.O = O; self.halt = halt; self.S = S
        self.need = need or (lambda *a: False)
        self.loads = collections.Counter()
        self.used = set()
        self.cutAt = set(); self.cutSt = {}; self.probe = None

    def fail(self, *why):
        raise Fail(why)

    def req(self, ok, *why):
        if not ok and not self.need(*why): self.fail(*why)

    def reqW(self, A, o, i):
        self.req(o in A.w, 'w', i, o)

    def nzOf(self, A, o):
        s = A.st.env.get(o)
        return o in A.nz or (s is not None and s[0] in ('gp', 'fpg'))

    def zImp(self, A, b, x):
        """`[b] = 0` makes `[x] = 0`: `b` is `x`, or the last instruction is `MUL [b] = [x]·[k]`, `k`
        nonzero (`zImp`)."""
        if b == x: return True
        if A.st.prev and A.st.prev[0][1][0] == 'mul':
            p, q, r = A.st.prev[0][1][1]
            return r == b and ((p == x and self.nzOf(A, q)) or (q == x and self.nzOf(A, p)))
        return False

    def divOk(self, A, b, c):
        """The divisor `b` of a back-solve of `[c] = …·[b]` is nonzero in the reference (`divOk`)."""
        if self.nzOf(A, b) or self.nzOf(A, c): return True
        x = A.one.get(c)
        return x is not None and self.zImp(A, b, x)

    def addW(self, A, o):
        if okKey(o): A.w.add(o)

    def addNz(self, A, o):
        if okKey(o): A.nz.add(o)

    def addHq(self, A, q, o):
        if o < HQ_SHIFT and q * HQ_SHIFT + o < 2 ** 28 - 1: A.hq.add((q, o))

    # -- hints
    def stepHints(self, i, A, hs):
        """`Mode.stepHints` on the written cells: heap runs a hint writes known to the later hints of
        the same offset only."""
        self.runs = set()
        for h in hs: self.stepHint(i, A, h)

    def stepHint(self, i, A, h):
        """A hint as the bridge reads it (`data.isa_hint`: its constructor's name and arguments, a run's start
        `('stack', base)` or `('heap', ptr)`)."""
        t = h[0]
        if t == 'frameAddress': return
        if t in ('alloc', 'allocDyn', 'allocArm', 'allocFrames'):
            if t in ('allocDyn', 'allocArm'): self.reqW(A, h[2], i)
            if t == 'allocFrames': self.reqW(A, h[3], i)
            self.addW(A, h[1]); return
        if t == 'cellAddress':
            self.addW(A, h[1]); return
        if t == 'witnessStack':
            for j in range(h[3]): self.addW(A, h[2] + j)
            return
        if t == 'witnessHeap':
            self.reqW(A, h[2], i); return
        if t == 'log2Ceil':
            d = h[1]
            if d[0] == 'stack':
                for j in range(h[3]): self.reqW(A, d[1] + j, i)
            else:
                self.reqW(A, d[1], i)
                self.req(all((d[1], j) in self.runs for j in range(h[3])), 'lcH', i, d[1])
            self.addW(A, h[2]); return
        if t in ('bitDecompose', 'bitDecomposeExp'):
            self.reqW(A, h[1], i)
            d = h[2]
            if d[0] == 'stack':
                for j in range(h[3]): self.addW(A, d[1] + j)
            else:
                self.reqW(A, d[1], i)
                for j in range(h[3]): self.runs.add((d[1], j))
            return
        if t == 'windowsExp':
            self.reqW(A, h[1], i)
            d = h[2]
            if d[0] == 'stack':
                for j in range(h[6]): self.addW(A, d[1] + h[3] + j)
            else: self.reqW(A, d[1], i)
            return
        if t == 'digitDecomposeExp':
            self.reqW(A, h[1], i)
            if h[7] is not None: self.reqW(A, h[7], i)
            d = h[2]
            if d[0] == 'stack':
                for j in range(h[4]): self.addW(A, d[1] + j)
            else: self.reqW(A, d[1], i)
            return
        if t == 'fieldLimbs':
            self.reqW(A, h[1], i)
            for j in range(h[3]): self.addW(A, h[2] + j)
            return
        if t == 'inverse':
            self.reqW(A, h[1], i)
            self.addW(A, h[2])
            return
        self.fail('hint', i, h)

    # -- one non-jump instruction: the frame rule, then ExecCore's step
    def stepOp(self, i, A, op, a):
        F = self.F
        env0 = A.st.env
        if op == 'xor':
            self.reqW(A, a[0], i); self.reqW(A, a[1], i); self.addW(A, a[2])
            if okKey(a[2]):
                if env0.get(a[0]) == ('gp', 0): A.one[a[2]] = a[1]
                elif env0.get(a[1]) == ('gp', 0): A.one[a[2]] = a[0]
        elif op == 'mul':
            x, y, c = a
            if x in A.w and y in A.w:
                self.addW(A, c)
                if self.nzOf(A, x) and self.nzOf(A, y): self.addNz(A, c)
            elif c in A.w and x in A.w and (self.divOk(A, x, c) or self.need('nz', i, x)):
                self.addW(A, y); self.addNz(A, x)
            elif c in A.w and y in A.w and (self.divOk(A, y, c) or self.need('nz', i, y)):
                self.addW(A, x); self.addNz(A, y)
            else:
                self.fail('mul', i, a)
        elif op == 'set':
            o, k0, k1 = a
            self.addW(A, o)
            if (0 < k0 < 2 ** 64) or (0 < k1 < 2 ** 64): self.addNz(A, o)
        elif op == 'deref':
            p, o, c, mode = a
            self.reqW(A, p, i)
            if i in self.S and c not in A.w:
                self.fail('store', i, a)
            self.addNz(A, p)
            if mode in ('.pc', '.fp'):
                self.addHq(A, p, o)
            elif c in A.w:
                self.addHq(A, p, o)
            elif (p, o) in A.hq:
                self.addW(A, c)
            elif i in self.O:
                self.addW(A, c); self.addHq(A, p, o); self.loads[i] += 1
            if mode == '.cell' and c == p and o < HQ_SHIFT and p * HQ_SHIFT + o < 2 ** 28 - 1: A.hs.add((p, o))
            ps = env0.get(p)
            if mode == '.cell' and ps is not None and ps[0] == 'fpg' and ps[1] + o < 2 ** 30:
                # through a next frame's pointer `fp·g^e`: own cell `e + o` holds `[c]`, written once `c` is (`nextF`)
                if okKey(ps[1] + o): A.cp[ps[1] + o] = c
                if c in A.w: self.addW(A, ps[1] + o)
        elif op == 'keccak':
            m0, m1, m2, m3, tail, b8, cap, out = a[:8]
            for o in keccakIns(m0, m1, m2, m3, tail, b8, cap): self.reqW(A, o, i)
            for j in range(KECCAK_N[a[10]]): self.addW(A, out + j)
        else:
            self.fail('op', i, op)
        facts, env, mem = nonJump(F, self.entry + i, A.st, op, a)
        A.st = XSt(env, mem, ([(self.entry + i, (op, a))] + A.st.prev[:1]))
        for f in facts:
            if f[0] == 'copy' and okKey(f[1]): A.cp[f[1]] = f[2]

    # -- a taken jump: where it goes, and the state at its successors
    def exit(self, i, A, kind, succ, od, of):
        """Returns [(t, state)] edges into later offsets."""
        F = self.F
        if kind[0] == 'next':
            return 0, succ, A
        if kind[0] == 'ret':
            for o in self.sig[2]: self.req(o in A.w, 'ret', i, o)
            return 0, [], A
        if kind[0] == 'call':
            _, pt, q, r = kind
            if pt[0] == 'gp': pcs = [pt[1]] if pt[1] < 2 ** 30 else None
            elif pt[0] == 'cell':
                k = self.tgt[0].get(i)
                pcs = self.tgt[2].get(k) if k is not None else None
            else: pcs = None
            if not pcs: self.fail('callee', i, pt)
            self.used.update(pcs)
            rets = None
            for pc in pcs:
                G = self.sigs.get(pc)
                if G is None: self.fail('sig', i, pc)
                for o in G[0]: self.req((q, o) in A.hq, 'entry', i, (q, o))
                if G[1] is not None: self.req((q, G[1]) in A.hs and (q, G[1]) in A.hq, 'self', i, (q, G[1]))
                rets = set(G[2]) if rets is None else rets & set(G[2])
            if not succ: self.fail('callret', i)
            B = A.copy()
            for o in sorted(rets): self.addHq(B, q, o)
            if len(succ) != 1: self.fail('callret', i)
            return 0, succ, B
        _, pt, ft = kind
        if F.self_(ft):
            if pt[0] == 'gp':
                if F.fpOne and pt[1] == self.halt and pt[1] < 2 ** 30: return 0, [], A
                self.fail('selfjump', i, pt)
            if pt[0] == 'cell':
                k = self.tgt[0].get(i)
                if k is None or k not in self.tgt[1]: self.fail('arms', i)
                ts = self.tgt[1][k]
                if not ts or ts != sorted(set(ts)) or ts[-1] >= self.len: self.fail('arms', i, ts[:4])
                return k + 1, ts, A
            self.fail('jumpfp', i)
        if ft[0] == 'fpg' and pt == ('gp', self.entry) and ft[1] < 2 ** 30:
            e = ft[1]
            G = self.sig
            for o in G[0]: self.req(e + o in A.w, 'tailentry', i, e + o)
            if G[1] is not None:
                c = A.cp.get(e + G[1])
                self.req(e + G[1] in A.w and (A.st.env.get(e + G[1]) == ('fpg', e) or
                                              (c is not None and A.st.env.get(c) == ('fpg', e))), 'tailself', i)
            self.req(A.cp.get(e) == 0 and A.cp.get(e + 1) == 1, 'header', i)
            self.req(not G[2], 'tailret', i)
            return 0, [], A
        self.fail('jump', i, pt, ft)

    def run(self, code):
        F = self.F
        cur = FS(XSt(dict(F.env)), set(self.sig[0]) | ({self.sig[1]} if self.sig[1] is not None else set()),
                 set(), set(), set(), {}, {})
        if F.fpOne: pass
        pend = []   # groups [ts, state]
        for i, (op, a) in enumerate(code):
            if self.probe is not None: self.probe(i, cur, pend)
            if i in self.cutAt:
                # past a cut the walk reads `hq`/`hs` only at a later `DEREF`'s pointer cell and offset or a later call's
                # frame cell: the rest (a table read's slot, say) is dropped, the cut a weakening of the state (`cutF`'s
                # `curSub`)
                live = {(a2[0], a2[1]) for op2, a2 in code[i:] if op2 == 'deref'}
                calls = {a2[2] for op2, a2 in code[i:] if op2 == 'jump'}
                for X in ([cur] if cur is not None else []) + [B for _, _, B in pend]:
                    X.hq = {p for p in X.hq if p in live or p[0] in calls}
                    X.hs = {p for p in X.hs if p in live or p[0] in calls}
                self.cutSt[i] = (cur.copy() if cur is not None else None, [(k, list(ts), B.copy()) for k, ts, B in pend])
                if cur is not None:
                    cur = cur.copy(); cur.st = XSt(cur.st.env)
                pend = [[k, list(ts), B.copy()] for k, ts, B in pend]
                for g in pend: g[2].st = XSt(g[2].st.env)
            P = None; ps = []
            for k, ts, B in pend:
                if ts and ts[0] == i:
                    P = B.copy() if P is None else meet(B, P)
                    if ts[1:]: ps.append([0, ts[1:], B])
                elif ts:
                    ps.append([k, ts, B])
            pend = ps
            if P is not None:
                cur = meet(cur, P) if cur is not None else P
                cur.st = XSt(cur.st.env)
            if cur is None: continue
            A = cur
            self.stepHints(i, A, self.hints.get(i, []))
            for o in self.nzr.get(i, []): self.addNz(A, o)
            if op != 'jump':
                self.stepOp(i, A, op, a)
                continue
            c, d, f = a
            for o in (c, d, f): self.reqW(A, o, i)
            cs = A.st.env.get(c)
            if cs == Z:
                continue
            kind, succ = jumpKind(F, self.entry, self.len, i, A.st, d, f)
            k, ts, B = self.exit(i, A, kind, succ, d, f)
            if ts:
                if k == 0 and (not all(t > i for t in ts) or ts != sorted(set(ts))): self.fail('back', i)
                if k != 0 and not ts[0] > i: self.fail('back', i)
                for g in pend:
                    if (k == 0 and g[1] == ts) or (k != 0 and g[0] == k):
                        g[2] = meet(g[2], B); break
                else:
                    pend.append([k, list(ts), B.copy()])
            if cs is not None and cs[0] == 'gp':
                cur = None
        if pend: self.fail('pend', sorted(pend)[:3])
        if cur is not None: self.fail('end')
