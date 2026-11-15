"""Census of the mode walk's failures on real runs (a dev tool: no proof, no certificate).

Every check a failing function's walk cannot meet is assumed and recorded instead (a forced fact), callee
first, so a caller walks against its callees' forced signatures. Each forced fact is then evaluated on real
runs, at every step its offset executes (a call's facts only where the call takes that callee), against the
step at which the run writes each cell:

  true         every demanded cell written before the step, at every instance (a value fact: it holds)
  later        some demanded cell written only after the step, each one eventually
  never        some demanded cell never written at some instance (a value fact: false)
  unexercised  no instance on these runs, or none where the demand can be evaluated

and printed as one table per (function, callee family), the family a callee's name without its `__L`
specialization. `--list` writes every fact with its label and, for one that is not true, its first bad
instance. `--res` evaluates every residual the inference emits (`Res.sub`, `Res.lt`, `Res.nz`) instead; with `--list`,
the forced functions' residuals are evaluated too (`OUT.txt.res`).

The runs: each a directory as `guest_diff`'s `LEANVM_GUEST_EXEC` export writes it (`memory.bin`, the final
image, write-once, so each cell's one value), plus `pcfp.bin`, the executor's (pc, fp) per step as u32 pairs.
The export writes no such dump; a debug option does (not in the tree: `execute.rs` records pc and fp per step
when `LEANVM_DBG_PCFP` names a file and writes them there, `guest_diff.rs`'s `export_execution` sets it to
`<dir>/pcfp.bin` around `execute`), then
  cd formal/lean_vm && LEANVM_GUEST_DIFF=/tmp/g LEANVM_GUEST_EXEC=RUNS cargo test --release \
    --manifest-path scripts/guest-export/Cargo.toml --lib guest_diff -- --ignored
gives RUNS/{left,right,node,pass}. The runs must be of this tree's guest (its bytecode and hints).

usage (from formal/lean_vm): python3 -I scripts/mode-cert/census.py RUNS [--save F.pkl | --load F.pkl]
  [--force FN,FN] [--only FN,FN] [--list OUT.txt] [--res OUT.txt]
(`--force`: force only these functions' failures, the others that fail left with empty signatures.)
"""
import sys, os, re, array, bisect, collections, pickle
sys.setrecursionlimit(100000)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import walk as W
import infer as I
from walk import Fail

# ---------------------------------------------------------------- forcing

FORCE = [False]
CUR = {'inf': None, 'walk': None}
# a final check's guarantees are dropped, not forced
NOFORCE_FINAL = {'post', 'postR', 'postP', 'loop', 'loopP', 'stride'}

_winit = W.Walk.__init__


def _walkInit(self, *a, **k):
    _winit(self, *a, **k)
    self.forced = []; self.fkeys = set()
    CUR['walk'] = self


W.Walk.__init__ = _walkInit
_iinit = I.Infer.__init__


def _inferInit(self, f):
    _iinit(self, f)
    CUR['inf'] = self


I.Infer.__init__ = _inferInit


def summ(A):
    return dict(r=frozenset(A.r), p=frozenset(A.p), h=frozenset(A.h))


def record(self, why, A):
    key = tuple(x for x in why if not isinstance(x, (W.Abs, dict, list)))
    if repr(key) in self.fkeys: return
    self.fkeys.add(repr(key))
    self.forced.append(dict(key=key, st=summ(A) if A is not None else None, cursel=self.cursel))


def transportable(self, why):
    """A loop's tail-call fact the inference's transport rule generalizes: left to it."""
    inf = CUR['inf']
    if inf is None or inf.f['name'] not in I.isloop: return False
    if why[0] == 'pre' and isinstance(why[2], tuple):
        return bool(dict(why[3][2]).get(('fr', 2)))
    if why[0] == 'preP' and isinstance(why[2], tuple):
        r = why[3]
        return r in inf.preP and r[1] == ('ex', ('fr', 2), 0) and r[2] == ('ex', ('fr', 2), 1)
    return False


def _need(self, ok, *why):
    if ok: return
    if self.demand(*why): return
    final = getattr(self.demand, '__name__', '') == '<lambda>'
    if FORCE[0] and not transportable(self, why) and not (final and why[0] in NOFORCE_FINAL):
        record(self, why, next((x for x in why if isinstance(x, W.Abs)), None)); return
    raise Fail(why)


def tabKey(self, k, i):
    return k is not None and k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and i in self.tabs and \
        self.E.jtLo <= k[1] < self.E.jtHi and k[1] not in I.REGION


def _needW(self, A, o, i):
    if o in A.w: return
    if o in self.lnk and self.demand('lnk', i, o, self.lnk[o], A):
        A.w.add(o)
        x = self.loadVal(A, self.lnk[o][0])
        if x is not None: A.addV(o, x)
        return
    if not FORCE[0]: raise Fail(('W', i, o))
    k = self.lnk[o][0] if o in self.lnk else None
    tk = tabKey(self, k, i)
    record(self, ('tabkey', i, o, k) if tk else ('W', i, o), A)
    A.w.add(o)
    if tk: A.addV(o, ('tab', k[2][0][0], k[1]))
    elif o in self.lnk:
        x = self.loadVal(A, self.lnk[o][0])
        if x is not None: A.addV(o, x)


def _addRes(self, A, i, rs):
    for r in rs:
        try:
            _addRes0(self, A, i, [r])
        except Fail:
            if not FORCE[0]: raise
            record(self, ('resW', i, r), A)
            if r[0] == 'lt': A.lt.add((r[1], r[2]))
            elif r[0] == 'nz': A.nz.add(r[1])
            elif r[0] == 'name': A.v[r[1]] = ('m', W.root(r[1]))
            elif r[0] == 'sub': A.r.add(r[1])


_addRes0 = W.Walk.addRes


def regionEnd(d):
    st = [r for r in I.REGION if r <= d]
    return max(st) + I.REGION[max(st)] if st else None


def shifted(orig):
    """A jump-table key shifted into its region (`COL_KAPPA_ADJ`): the arms to the region's end."""
    def g(self, A, i, t):
        v = A.v.get(t)
        if FORCE[0] and v is not None and v[0] == 'tab' and v[2] not in I.REGION and i in self.tabs:
            end = regionEnd(v[2])
            if end is not None:
                save = self.tabs[i]; self.tabs[i] = end - v[2]
                try: return orig(self, A, i, t)
                finally: self.tabs[i] = save
        return orig(self, A, i, t)
    return g


_jumpI = W.Walk.jumpI


def _jumpIF(self, i, A, d, f):
    if FORCE[0] and A.v.get(d) is None and (d in self.lnk or d in self.ld) and i in self.tabs:
        k = self.lnk[d][0] if d in self.lnk else self.ld[d]
        if k[0] == 0 and len(k[2]) == 1 and k[2][0][1] == 1 and self.E.jtLo <= k[1] < self.E.jtHi:
            record(self, ('tabkey', i, d, k), A)
            A.v[d] = ('tab', k[2][0][0], k[1])
    return _jumpI(self, i, A, d, f)


_narrow = I.Infer.narrow


def _narrowF(self, *a):
    """The callee inferred again unforced, the census's state kept."""
    save = (FORCE[0], CUR['inf'], CUR['walk']); FORCE[0] = False
    try: return _narrow(self, *a)
    finally: FORCE[0], CUR['inf'], CUR['walk'] = save


I.Infer.narrow = _narrowF
W.Walk.need = _need
W.Walk.needW = _needW
W.Walk.addRes = _addRes
W.Walk.jumpI = _jumpIF
W.Walk.calleesOf = shifted(W.Walk.calleesOf)
W.Walk.armsOf = shifted(W.Walk.armsOf)


def emptySig(f):
    na, nr = f.get('nargs', 0), f.get('nret', 0)
    return I.mkSig(f, [], [], list(range(2 + na, 2 + na + nr)))


def census(force=None, log=print):
    """Infer every function callee first; one that fails is inferred again with its failures forced (only
    those of `force`, when given; another that fails gets an empty signature)."""
    out = {}
    for n in I.order:
        f = I.fns[n]
        FORCE[0] = False
        try:
            I.infer(n); continue
        except Fail:
            pass
        if force is not None and n not in force:
            I.E.sigs[f['entry']] = emptySig(f); continue
        FORCE[0] = True
        tries = {}
        for named in (False, True):
            try:
                sig, res = I.infer1(n, named)
                tries[named] = (len(CUR['walk'].forced), CUR['walk'].forced, sig, res)
            except Fail as e:
                log('hard fail', n, named, str([x for x in e.args[0] if not isinstance(x, W.Abs)])[:300])
        FORCE[0] = False
        if not tries:
            I.E.sigs[f['entry']] = emptySig(f); continue
        best = min(tries, key=lambda k: tries[k][0])
        if best != max(tries):
            FORCE[0] = True; I.infer1(n, best); FORCE[0] = False
        cnt, forced, sig, res = tries[best]
        out[n] = dict(named=best, forced=forced, res=res, sig=sig)
        log('forced', n, cnt, flush=True)
    return out

# ---------------------------------------------------------------- the runs

MOD = (1 << 64) | 0b11011  # x^64 + x^4 + x^3 + x + 1
_LOG = {}
_LOGN = [0]


def logtab(n):
    """The table g^k -> k, for k below n at least."""
    if _LOGN[0] < n:
        a = 1
        for k in range(n):
            _LOG[a] = k
            a <<= 1
            if a >> 64: a ^= MOD
        _LOGN[0] = n
    return _LOG


def f0Sets():
    """`__jump_tables`: its `SET`s, one per instruction."""
    t = open(os.path.join(I.data.STATEMENT, 'Data', 'Bytecode00.lean')).read()
    blk = t[t.index('def f0c0'):]
    t0 = open(os.path.join(I.data.STATEMENT, 'Data', 'Bytecode.lean')).read()
    n0 = int(re.search(r'def f0 : CompiledFunction :=\s*⟨"[^"]*", \d+, (\d+)', t0).group(1))
    return [(int(a), int(b), int(c)) for a, b, c in re.findall(r'\.set (\d+) (\d+) (\d+)', blk)][:n0]


OPS = {}
for _f in I.fns.values():
    for _i, _x in enumerate(_f['ops']): OPS[_f['entry'] + _i] = _x
for _j, _x in enumerate(f0Sets()): OPS[_j] = ('set', _x)
NEVER = 1 << 62
# the order of `g`: exponents are read modulo it (`g^(2^64 - 2)` is `g^-1`)
ORDER = 2 ** 64 - 1


class Run:
    """A run: its final image and steps, and each cell's write time (`2s` by a hint at step `s`, `2s + 1`
    by its instruction), replayed from the steps and the executor's rules."""

    def __init__(self, d):
        self.dir = d; self.name = os.path.basename(d.rstrip('/'))
        self.mem = array.array('Q'); self.mem.frombytes(open(os.path.join(d, 'memory.bin'), 'rb').read())
        self.n = len(self.mem) // 2
        self.log = logtab(self.n + 64)
        t = array.array('I'); t.frombytes(open(os.path.join(d, 'pcfp.bin'), 'rb').read())
        self.pcs = t[0::2]; self.fps = t[1::2]
        self.byPc = collections.defaultdict(list)
        for s, pc in enumerate(self.pcs): self.byPc[pc].append(s)
        self.replay()

    def word(self, c): return (self.mem[2 * c], self.mem[2 * c + 1]) if 0 <= c < self.n else (0, 0)

    def lg(self, c):
        """The exponent of the power of `g` cell `c` holds, or None."""
        c0, c1 = self.word(c)
        return None if c1 else self.log.get(c0)

    def replay(self):
        wt = [NEVER] * self.n
        links = {}
        bad = collections.Counter()

        def put(c, t):
            if wt[c] != NEVER: return
            wt[c] = t
            todo = [c]
            while todo:
                x = todo.pop()
                for y in links.pop(x, ()):
                    if wt[y] == NEVER: wt[y] = t; todo.append(y)

        def run(c, n, t):
            for j in range(n): put(c + j, t)

        def heap(fp, o):
            b = self.lg(fp + o)
            if b is None: bad['ptr'] += 1
            return b

        def dest(fp, d):
            return fp + d[1] if d[0] == 's' else heap(fp, d[1])

        hints = I.HINTS
        for s in range(len(self.pcs)):
            pc, fp = self.pcs[s], self.fps[s]
            t = 2 * s
            for h in hints.get(pc, ()):
                k = h[0]
                if k in ('al', 'ad', 'aa', 'af', 'ca', 'lt', 'iv'):
                    put(fp + (h[2] if k == 'iv' else h[1]), t)
                elif k == 'av':
                    # nothing for an empty entry: then the allocation that follows writes it
                    if self.word(fp + h[1]) != (0, 0): put(fp + h[1], t)
                elif k == 'ws': run(fp + h[2], h[3], t)
                elif k == 'wh':
                    b = heap(fp, h[2])
                    if b is not None: run(b + h[3], h[4], t)
                elif k == 'lc': put(fp + h[2], t)
                elif k in ('bd', 'be'):
                    b = dest(fp, h[2])
                    if b is not None: run(b, h[3], t)
                elif k == 'we':
                    b = dest(fp, h[2])
                    if b is not None: run(b + h[3], h[6], t)
                elif k == 'dd':
                    b = dest(fp, h[2])
                    if b is not None: run(b, h[4], t)
                elif k == 'fl': run(fp + h[2], h[3], t)
            t += 1
            op, a = OPS[pc]
            if op == 'set': put(fp + a[0], t)
            elif op == 'xor':
                if wt[fp + a[0]] >= t or wt[fp + a[1]] >= t: bad['unwritten read'] += 1
                put(fp + a[2], t)
            elif op == 'jump':
                if any(wt[fp + o] >= t for o in a): bad['unwritten read'] += 1
            elif op == 'mul':
                x, y, z = fp + a[0], fp + a[1], fp + a[2]
                if wt[z] < t and (wt[x] < t) != (wt[y] < t): put(y if wt[x] < t else x, t)
                else: put(z, t)
            elif op == 'deref':
                p, o, c, mode = a
                b = heap(fp, p)
                if b is None: continue
                k = b + o
                if mode != '.cell': put(k, t)
                elif wt[k] < t or wt[fp + c] < t: put(k, t); put(fp + c, t)
                else:
                    links.setdefault(k, []).append(fp + c); links.setdefault(fp + c, []).append(k)
            elif op == 'keccak':
                run(fp + a[7], W.KECCAK_N[a[10]], t)
        self.wt = wt
        self.unwritten = sum(1 for c in range(self.n) if wt[c] == NEVER and self.word(c) != (0, 0))
        self.bad = bad

    def frames(self, pc):
        return sorted({self.fps[s] for s in self.byPc.get(pc, [])})

    # ----- the walk's terms at frame fp
    def base(self, fp, b):
        if b[0] == 'fr': return self.lg(fp + b[1])
        if b[0] != 'hp': return None
        p = self.lg(fp + b[1])
        return None if p is None else self.lg(p + b[2])

    def baseCells(self, fp, b):
        """The cells a base's word is read from."""
        if b[0] == 'fr': return [fp + b[1]]
        p = self.lg(fp + b[1])
        return [fp + b[1]] + ([p + b[2]] if p is not None else [])

    def mono(self, fp, m):
        e = m[0] * fp + m[1]
        for b, k in m[2]:
            x = self.base(fp, b)
            if x is None: return None
            e += k * x
        return e % ORDER

    def idx(self, fp, i):
        if i[0] == 'num': return i[1]
        x = self.base(fp, i[1])
        return None if x is None else x + i[2]

    def cells(self, fp, r):
        q, lo, hi, S, d = r
        eq, a, b = self.mono(fp, q), self.idx(fp, lo), self.idx(fp, hi)
        if None in (eq, a, b) or b - a > 1 << 20: return None
        return [(eq + S * j + d) % ORDER for j in range(a, b)]

    def runCells(self, fp, rs):
        U = set()
        for r in rs:
            c = self.cells(fp, r)
            if c is None: return None
            U.update(c)
        return U

# ---------------------------------------------------------------- facts on the runs

BYENTRY = {f['entry']: n for n, f in I.fns.items()}


def family(name):
    return re.sub(r'__L\d.*$', '', name)


def callee(key):
    """A call's fact: the callee's entry, its name and family."""
    if key[0] in ('pre', 'preR', 'preP', 'entry', 'self'):
        nm = key[2]
        pc = nm[1] if isinstance(nm, tuple) else nm
        if isinstance(pc, int) and pc in BYENTRY: return pc, BYENTRY[pc]
    return None, None


def demand(R, s, fp, x):
    """At step `s`, frame `fp`: ('cells', cells, deadline) for a mode fact, ('val', bool) for a value fact,
    None if it cannot be evaluated."""
    key = x['key']; k = key[0]; i = key[1]
    t = 2 * s + 1  # before the instruction at `s`
    nfp = R.fps[s + 1] if s + 1 < len(R.fps) else None
    if k == 'W':
        # a `MUL`'s input it back-solves is written by the instruction itself
        op, a = OPS[R.pcs[s]]
        return ('cells', [fp + key[2]], t + 1 if op == 'mul' and key[2] in a[:2] else t)
    if k in ('pre', 'preR', 'preP', 'entry', 'self'):
        if nfp is None: return None
        if k == 'entry': return ('cells', [nfp + key[3]], t)
        if k == 'self': return ('cells', [nfp], t)
        if k == 'pre':
            e = R.mono(nfp, key[3]); return None if e is None else ('cells', [e], t)
        c = R.cells(nfp, key[3])
        if c is None: return None
        if k == 'preR': return ('cells', c, t)
        out = list(c)
        for y in c:
            p = R.lg(y)
            if p is None: return None
            out += [p + o for o in key[4]]
        return ('cells', out, t)
    if k == 'H':
        e = R.mono(fp, key[2]); return None if e is None else ('cells', [e], 2 * s)
    if k == 'nz': return ('val', R.word(fp + key[2]) != (0, 0))
    if k == 'sel':
        e = R.base(fp, key[2]); return None if e is None else ('val', e < key[3])
    if k == 'tabkey':
        kk = key[3]; e = R.base(fp, kk[2][0][0]); n = regionEnd(kk[1]) - kk[1]
        return None if e is None else ('val', e < n)
    if k == 'resW':
        r = key[2]
        if r[0] in ('nz', 'name'): return ('cells', [fp + r[1]], 2 * s)
        if r[0] == 'sub':
            c = R.cells(fp, r[1]); return None if c is None else ('cells', c, 2 * s)
        if r[0] == 'lt':
            cs = [c for x in (r[1], r[2]) if x[0] == 'ex' for c in R.baseCells(fp, x[1])]
            return ('cells', cs, 2 * s)
    return None


LABELS = ('true', 'later', 'never', 'unexercised')


def label(runs, entry, x):
    """The fact's label on the runs, its instance count and its first bad instance."""
    key = x['key']; i = key[1]
    cpc, _ = callee(key)
    inst = 0; worst = 'true'; first = None
    for R in runs:
        for s in R.byPc.get(entry + i, ()):
            if cpc is not None and (s + 1 >= len(R.pcs) or R.pcs[s + 1] != cpc): continue
            d = demand(R, s, R.fps[s], x)
            if d is None: continue
            inst += 1
            if d[0] == 'val':
                if not d[1]:
                    worst = 'never'; first = first or (R.name, R.fps[s], 'false')
                continue
            late = [c for c in d[1] if R.wt[c] >= d[2]] if all(0 <= c < R.n for c in d[1]) else None
            if late is None:
                worst = 'never'; first = first or (R.name, R.fps[s], 'out of memory'); continue
            if not late: continue
            nev = [c for c in late if R.wt[c] == NEVER]
            lab = 'never' if nev else 'later'
            if LABELS.index(lab) > LABELS.index(worst) or first is None:
                rel = [(c - d[1][0]) for c in (nev or late)[:6]]
                first = (R.name, R.fps[s], '%d of %d cells %s, from the first: %s' % (
                    len(nev or late), len(d[1]), lab, rel))
            if LABELS.index(lab) > LABELS.index(worst): worst = lab
    if inst == 0: return 'unexercised', 0, None
    return worst, inst, first


def tables(D, runs, only=None, out=None):
    pat = collections.OrderedDict()
    tot = collections.Counter()
    for fn, d in D.items():
        if only and fn not in only: continue
        entry = I.fns[fn]['entry']
        for x in d['forced']:
            key = x['key']
            _, cn = callee(key)
            lab, inst, first = label(runs, entry, x)
            pat.setdefault((fn, family(cn) if cn else '-'), collections.Counter())[(key[0], lab)] += 1
            tot[(fn, lab)] += 1
            if out is not None:
                out.write('%s %s @%d %s [%s] inst %d: %s\n' % (fn, key[0], key[1], cn or '', lab, inst,
                                                             str(key[2:])[:400]))
                if first: out.write('    first bad: %s\n' % (first,))
    for (fn, fam), cnt in pat.items():
        kinds = sorted({k for k, _ in cnt})
        print('\n%s -> %s' % (fn, fam))
        print('    %-8s %s' % ('kind', ' '.join('%11s' % l for l in LABELS)))
        for k in kinds: print('    %-8s %s' % (k, ' '.join('%11d' % cnt[(k, l)] for l in LABELS)))
    print('\nby function')
    print('    %-26s %s' % ('function', ' '.join('%11s' % l for l in LABELS)))
    for fn in D:
        if only and fn not in only: continue
        print('    %-26s %s' % (fn, ' '.join('%11d' % tot[(fn, l)] for l in LABELS)))


def residuals(runs, res, out):
    """Every residual the inference emits, evaluated at every frame its offset runs in."""
    tally = collections.Counter()
    for n, rs in sorted(res.items()):
        e = I.fns[n]['entry']
        for i, lst in sorted(rs.items()):
            for r in lst:
                if r[0] == 'name': continue
                inst = 0; bad = []
                for R in runs:
                    for fp in R.frames(e + i):
                        if r[0] == 'lt':
                            a, b = R.idx(fp, r[1]), R.idx(fp, r[2])
                            ok = None if a is None or b is None else a < b
                        elif r[0] == 'nz': ok = R.word(fp + r[1]) != (0, 0)
                        else:
                            A = R.cells(fp, r[1]); U = R.runCells(fp, r[2])
                            ok = None if A is None or U is None else set(A) <= U
                        if ok is None: continue
                        inst += 1
                        if not ok: bad.append((R.name, fp))
                v = 'unexercised' if inst == 0 else 'false' if bad else 'true'
                tally[(r[0], v)] += 1
                if v != 'true': out.write('%s %s @%d: %s inst %d %s\n' % (v, n, i, str(r)[:300], inst, bad[:2]))
    print(sorted(tally.items()))


if __name__ == '__main__':
    av = sys.argv[1:]
    runsDir = av[0]
    opt = lambda f: av[av.index(f) + 1] if f in av else None
    only = set(opt('--only').split(',')) if opt('--only') else None
    if opt('--res'):
        res = {}
        for n in I.order:
            try: res[n] = I.infer(n)[1]
            except Fail: I.E.sigs[I.fns[n]['entry']] = emptySig(I.fns[n])
        runs = [Run(os.path.join(runsDir, c)) for c in sorted(os.listdir(runsDir))]
        residuals(runs, res, open(opt('--res'), 'w'))
        sys.exit(0)
    if opt('--load'): D = pickle.load(open(opt('--load'), 'rb'))
    else:
        D = census(set(opt('--force').split(',')) if opt('--force') else None)
        if opt('--save'): pickle.dump(D, open(opt('--save'), 'wb'))
    runs = [Run(os.path.join(runsDir, c)) for c in sorted(os.listdir(runsDir))]
    for R in runs:
        print('run %s: %d steps, %d nonzero cells never written%s' % (
            R.name, len(R.pcs), R.unwritten, ', ' + str(dict(R.bad)) if R.bad else ''))
    tables(D, runs, only, open(opt('--list'), 'w') if opt('--list') else None)
    if opt('--list'):
        print('\nthe forced functions\' residuals:', end=' ')
        residuals(runs, {n: d['res'] for n, d in D.items()}, open(opt('--list') + '.res', 'w'))
