"""Core-level modedness census (`formal/notes/core-mode.md`): a measurement, not a proof.

For every core function, a forward walk of its body in statement order (both sides of an `ite`, every
arm of a `match`, met by intersection at the join) over two facts:
  (a) values: a value is defined before it is used, by the solving rules of the executor (an atom
      whose output and all but one input are known solves the last one, as `Interp` does);
  (b) heap: a cell `(pointer, offset)` a defining `load` reads was written before, by a store (a
      `load` whose word is already defined), a hint's heap destination, a frame run's address
      (`frameAddr`), or a callee's guarantee; pointers are monomials over base values with a power
      of `g` folded into the offset.
Signatures are inferred callee first: `pre` the cells over parameters a function reads unwritten,
`post` those it writes on every path to its return. A loop helper (its body ends in `callIf` to itself)
gets no point facts over its counter: those reads and writes are runs, reported as such.
Each uncovered read is classified by the origin of its pointer's bases.

usage (from formal/lean_vm): python3 -I scripts/core-mode/census.py [--fn NAME] [--list]
(`coreir.py` caches the parsed data at `$CORE_MODE_CACHE`, default `/tmp/core-mode-cache.pkl`; delete it after a regen.)
"""
import sys, os, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import coreir

D = coreir.load()
CORE, STABLE, POWS = D['core'], D['stable'], dict(D['pows'])
POWS[1] = 0


def mono_add(a, b, sgn=1):
    if a is None or b is None:
        return None
    ba, sa = a
    bb, sb = b
    m = dict(ba)
    for k, e in bb:
        m[k] = m.get(k, 0) + sgn * e
    return (tuple(sorted((k, e) for k, e in m.items() if e)), sa + sgn * sb)


def opaque(kind, v):
    return (((kind, v), 1),), 0


def callee_of(name):
    return STABLE.get(name, name)


def is_loop(key):
    p, b = CORE[key]
    return any(s[0] == 'callIf' and callee_of(s[2]) == key for s in b)


class St:
    __slots__ = ('D', 'W', 'R')

    def __init__(self, D, W, R):
        self.D, self.W, self.R = D, W, R

    def copy(self):
        return St(set(self.D), set(self.W), set(self.R))


def meet(sts):
    sts = [s for s in sts if s is not None]
    if not sts:
        return None
    s0 = sts[0].copy()
    for s in sts[1:]:
        s0.D &= s.D
        s0.W &= s.W
        s0.R &= s.R
    return s0


class Fn:
    def __init__(self, key, sigs):
        self.key = key
        self.params, self.body = CORE[key]
        self.sigs = sigs
        self.mono = {}
        self.origin = {}
        self.alias = collections.defaultdict(list)
        self.uses = collections.Counter()      # (a) failures by kind
        self.reads = 0
        self.covered = 0
        self.unc = []                          # (b) uncovered reads: (class, detail)
        self.pre = set()
        self.preR = set()
        self.side = collections.Counter()
        self.loopReads = []
        self.retvals = []
        self.step = {}
        self.loopWrites = set()
        self.posts = []
        self.loop = is_loop(key)
        self.counter = self.find_counter() if self.loop else set()
        for i, v in enumerate(self.params):
            self.mono[v] = ((((('p', i)), 1),), 0)
            self.origin[('p', i)] = 'param'

    def find_counter(self):
        tail = [s for s in self.body if s[0] == 'callIf' and callee_of(s[2]) == self.key]
        self.tail = tail
        return {i for s in tail for i, a in enumerate(s[3])
                if i < len(self.params) and a != self.params[i]}

    # ---- values
    def need(self, st, vs, kind):
        ok = True
        for v in vs:
            if v not in st.D:
                self.uses[kind] += 1
                ok = False
        return ok

    def define(self, st, v, mono=None, kind='val'):
        st.D.add(v)
        if v not in self.mono:
            if mono is None:
                mono = opaque(kind, v)
                self.origin[(kind, v)] = kind
            self.mono[v] = mono
        for c in self.alias.get(v, ()):
            st.W.add(c)

    def cell(self, p, off):
        m = self.mono.get(p)
        if m is None:
            return None
        return (m[0], m[1] + off)

    def read(self, st, p, off):
        self.reads += 1
        c = self.cell(p, off)
        if c is not None and c in st.W:
            self.covered += 1
            return
        if c is not None and self.run_covers(st, c):
            self.covered += 1
            return
        self.classify(c)

    def run_covers(self, st, c):
        """A run `base·j^S·g^ro`, `j` over the loop's range, holds the cell: the index's bound is a side
        condition (a value fact), counted."""
        bases, off = c
        m = dict(bases)
        for (rb, rv, S, ro) in st.R:
            if rb is None or not S:
                continue
            r = dict(rb)
            if any(m.get(k, 0) != e for k, e in r.items()):
                continue
            rest = {k: e for k, e in m.items() if r.get(k, 0) != e}
            if not rest and (off - ro) % S == 0 and off >= ro:
                self.side['run-point'] += 1
                return True
            if len(rest) == 1 and list(rest.values())[0] == S and (off - ro) % S == 0:
                self.side['run-index'] += 1
                return True
        return False

    def classify(self, c):
        if c is None:
            self.unc.append(('unknown-pointer', None))
            return
        bases, off = c
        kinds = set()
        for b, e in bases:
            if b[0] == 'p':
                kinds.add('counter' if b[1] in self.counter else 'param')
            else:
                kinds.add(b[0])
        if not bases:
            self.unc.append(('absolute', None))
            return
        if kinds <= {'param'}:
            self.pre.add(c)
            self.unc.append(('pre-point', None))
        elif kinds <= {'param', 'counter'}:
            self.preR.add(c)
            self.unc.append(('pre-loop-run', None))
            self.loopReads.append(c)
        elif kinds & {'load'}:
            self.unc.append(('pointer-from-memory', None))
        elif kinds & {'hint', 'witness', 'add', 'keccak', 'digits'}:
            self.unc.append(('data-index', tuple(sorted(kinds))))
        elif kinds & {'ret'}:
            self.unc.append(('callee-returned', None))
        elif kinds & {'alloc', 'fa'}:
            self.unc.append(('own-buffer-unwritten', tuple(sorted(kinds))))
        else:
            self.unc.append(('other', tuple(sorted(kinds))))

    def write(self, st, p, off, n=1):
        for k in range(n):
            c = self.cell(p, off + k)
            if c is not None:
                st.W.add(c)
                if self.counter:
                    self.loopWrites.add(c)

    # ---- atoms
    def atom(self, st, a):
        k = a[0]
        if k == 'const':
            d, (l0, l1) = a[1], a[2]
            m = ((), POWS[l0]) if l1 == 0 and l0 in POWS else None
            self.define(st, d, m, 'const')
        elif k == 'add':
            d, x, y = a[1:]
            known = [v in st.D for v in (d, x, y)]
            if known[1] and known[2]:
                self.define(st, d, None, 'add')
            elif sum(known) == 2:
                u = [d, x, y][known.index(False)]
                self.define(st, u, None, 'add')
            elif not all(known):
                self.need(st, [v for v in (x, y) if v not in st.D], 'add')
                self.define(st, d, None, 'add')
        elif k == 'mul':
            d, x, y = a[1:]
            if x in st.D and y in st.D:
                self.define(st, d, mono_add(self.mono.get(x), self.mono.get(y)), 'mul')
            elif d in st.D and x in st.D:
                self.define(st, y, mono_add(self.mono.get(d), self.mono.get(x), -1), 'mul')
            elif d in st.D and y in st.D:
                self.define(st, x, mono_add(self.mono.get(d), self.mono.get(y), -1), 'mul')
            else:
                self.need(st, [v for v in (x, y) if v not in st.D], 'mul')
                self.define(st, d, None, 'mul')
        elif k == 'copy':
            d, s = a[1:]
            if s in st.D:
                self.define(st, d, self.mono.get(s))
            elif d in st.D:
                self.define(st, s, self.mono.get(d))
            else:
                self.need(st, [s], 'copy')
                self.define(st, d)
        elif k == 'load':
            d, p, off = a[1:]
            self.need(st, [p], 'load-pointer')
            if d in st.D:
                self.write(st, p, off)
            else:
                self.read(st, p, off)
                self.define(st, d, None, 'load')
        elif k == 'assertEq':
            x, y = a[1:]
            if x in st.D and y not in st.D:
                self.define(st, y, self.mono.get(x))
            elif y in st.D and x not in st.D:
                self.define(st, x, self.mono.get(y))
            else:
                self.need(st, [x, y], 'assertEq')
        elif k == 'assertNe':
            x, inv, p = a[1:]
            self.need(st, [x, inv], 'assertNe')
            self.define(st, p)
        elif k == 'rangeCheck':
            x, y, t1, t2, kk = a[1:]
            self.need(st, [x, kk], 'rangeCheck')
            self.define(st, y, mono_add(self.mono.get(kk), self.mono.get(x), -1))
        elif k == 'assertInK':
            self.need(st, a[1:], 'assertInK')
        elif k == 'keccak':
            self.need(st, a[1], 'keccak')
            for v in a[2]:
                self.define(st, v, None, 'keccak')
        elif k == 'frameAddr':
            p, run = a[1], a[2]
            self.define(st, p, None, 'fa')
            for i, v in enumerate(run):
                c = self.cell(p, i)
                self.alias[v].append(c)
                if v in st.D:
                    st.W.add(c)
        elif k == 'touch':
            self.need(st, [a[2]], 'touch')
        elif k == 'hint':
            self.hint(st, a[1])
        else:
            raise ValueError(k)

    def dest(self, st, dst, kind):
        if dst[0] == 'stack':
            for v in dst[1]:
                self.define(st, v, None, kind)
        else:
            _, p, off, n = dst
            self.need(st, [p], 'hint-heap-pointer')
            self.write(st, p, off, n)

    def hint(self, st, h):
        k = h[0]
        if k == 'witness':
            self.dest(st, h[2], 'witness')
        elif k in ('bits', 'bitsExp', 'windowsExp'):
            self.need(st, [h[1]], 'hint-input')
            self.dest(st, h[-1], 'hint')
        elif k == 'digitsExp':
            self.need(st, [h[1]] + ([h[6]] if h[6] is not None else []), 'hint-input')
            self.dest(st, h[7], 'digits')
        elif k == 'limbs':
            self.need(st, [h[1]], 'hint-input')
            for v in h[2]:
                self.define(st, v, None, 'hint')
        elif k == 'log2Ceil':
            bd = h[1]
            if bd[0] == 'heap':
                self.need(st, [bd[1]], 'hint-input')
                for i in range(h[2]):
                    self.read(st, bd[1], bd[2] + i)
            else:
                self.need(st, bd[1], 'hint-input')
            self.define(st, h[4], None, 'hint')
        elif k == 'inverse':
            self.need(st, [h[1]], 'hint-input')
            self.define(st, h[2], None, 'hint')
        elif k == 'alloc':
            self.define(st, h[1], None, 'alloc')
        elif k == 'allocDyn':
            self.need(st, [h[2]], 'hint-input')
            self.define(st, h[1], None, 'alloc')
        else:
            raise ValueError(k)

    # ---- calls
    def trans(self, cell, args, rets=()):
        bases, off = cell
        m = ((), off)
        for (b, e) in bases:
            src = args if b[0] == 'p' else rets if b[0] == 'r' else None
            if src is None or b[1] >= len(src):
                return None
            if b[0] == 'r' and src[b[1]] not in self.mono:
                self.mono[src[b[1]]] = opaque('ret', src[b[1]])
            am = self.mono.get(src[b[1]])
            if am is None:
                return None
            for _ in range(abs(e)):
                m = mono_add(m, am, 1 if e > 0 else -1)
        return m

    def call(self, st, f, args, rets, apply_post=True):
        g = callee_of(f)
        sig = self.sigs.get(g)
        self.need(st, args, 'call-arg')
        if sig is not None:
            for c in sig['pre']:
                t = self.trans(c, args)
                if t is not None and t in st.W:
                    continue
                if t is not None and self.run_covers(st, t):
                    continue
                self.reads += 1
                self.classify(t)
            for (cb, S, o) in sig['preR']:
                self.reads += 1
                t = self.trans((cb, o), args)
                if t is not None and any(r[0] == t[0] and r[2] == S and r[3] == t[1] for r in st.R):
                    self.side['run-sub'] += 1
                    self.covered += 1
                    continue
                if t is not None and all((t[0], t[1] + S * j) in st.W for j in range(4)):
                    self.side['run-by-points'] += 1
                    self.covered += 1
                    continue
                self.unc.append(('callee-loop-run-pre', g))
            if apply_post:
                for c in sig['post']:
                    t = self.trans(c, args, rets)
                    if t is not None:
                        st.W.add(t)
            # a run is empty when a conditional call is not taken: runs cross either way
            if sig['postR']:
                for (rb, ri, S, ro) in sig['postR']:
                    t = self.trans((rb, 0), args, rets)
                    if t is not None:
                        st.R.add((t[0], ri, S, ro + t[1]))
        for v in rets:
            self.define(st, v, None, 'ret')
        if sig is not None and apply_post:
            for c in sig['post']:
                if any(b[0] == 'r' for b, e in c[0]):
                    t = self.trans(c, args, rets)
                    if t is not None:
                        st.W.add(t)

    # ---- statements
    def block(self, st, ss):
        for s in ss:
            if st is None:
                return None
            k = s[0]
            if k == 'a':
                self.atom(st, s[1])
            elif k == 'ite':
                self.need(st, [s[1]], 'branch')
                st = meet([self.block(st.copy(), s[2]), self.block(st.copy(), s[3])])
            elif k == 'match':
                self.need(st, [s[1]], 'match')
                st = meet([self.block(st.copy(), arm) for arm in s[2]])
            elif k == 'call':
                self.call(st, s[1], s[2], s[3])
            elif k == 'dispatch':
                self.need(st, [s[1]], 'dispatch')
                posts = []
                for f in s[2]:
                    t = st.copy()
                    self.call(t, f, s[3], [])
                    posts.append(t)
                m = meet(posts)
                st.W, st.R = m.W, m.R
                for v in s[4]:
                    self.define(st, v, None, 'ret')
            elif k == 'callIf':
                self.need(st, [s[1]], 'branch')
                if callee_of(s[2]) == self.key:
                    self.need(st, s[3], 'call-arg')
                else:
                    self.call(st, s[2], s[3], [], apply_post=False)
            elif k == 'ret':
                self.need(st, s[1], 'ret')
                if s[1]:
                    self.retvals = s[1]
                self.posts.append(st.copy())
                return None
        return st

    def run(self):
        st = St(set(self.params), set(), set())
        self.block(st, self.body)
        for t in getattr(self, 'tail', []):
            for i in self.counter:
                am = self.mono.get(t[3][i])
                if am is not None and am[0] == ((('p', i), 1),):
                    self.step[i] = am[1]
        m = meet(self.posts)
        post, postR = set(), set()
        if m is not None:
            for c in m.W:
                ks = [b for b, e in c[0]]
                if all(b[0] == 'p' for b in ks):
                    if any(b[1] in self.counter for b in ks):
                        cb = tuple((b, e) for b, e in c[0] if b[1] not in self.counter)
                        ce = [e for b, e in c[0] if b[1] in self.counter]
                        if len(ce) == 1:
                            postR.add((cb, None, ce[0], c[1]))
                    else:
                        post.add(c)
            for r in m.R:
                if all(b[0] == 'p' for b, e in r[0]):
                    postR.add(r)
        if self.loop:
            # a loop returns through its last iteration: only runs over its counter cross its return
            post = set()
            # a read the same iteration's write `t` steps on covers is chained: no precondition
            preR = set()
            for c in self.preR:
                ch = False
                for (b, e) in c[0]:
                    if b[0] == 'p' and b[1] in self.counter:
                        t = self.step.get(b[1])
                        if t is not None and (c[0], c[1] + e * t) in self.loopWrites:
                            ch = True
                if ch:
                    self.side['chained'] += 1
                    self.unc.remove(('pre-loop-run', None))
                    self.covered += 1
                else:
                    cb = tuple((b, e) for b, e in c[0] if not (b[0] == 'p' and b[1] in self.counter))
                    S = sum(e for b, e in c[0] if b[0] == 'p' and b[1] in self.counter)
                    preR.add((cb, S, c[1]))
            self.preR = preR
        else:
            self.preR = set()
        # guarantees over returned words: their bases renamed to the return index
        postRet = set()
        if m is not None and self.retvals:
            names = {}
            for i, v in enumerate(self.retvals):
                mv = self.mono.get(v)
                if mv and len(mv[0]) == 1 and mv[0][0][1] == 1 and mv[0][0][0][0] != 'p':
                    names[mv[0][0][0]] = ('r', i)
            for c in m.W:
                if c[0] and all(b in names or b[0] == 'p' for b, e in c[0]):
                    postRet.add((tuple((names.get(b, b), e) for b, e in c[0]), c[1]))
            for r in m.R:
                if r[0] and all(b in names or b[0] == 'p' for b, e in r[0]):
                    postR.add((tuple((names.get(b, b), e) for b, e in r[0]), r[1], r[2], r[3]))
        return dict(pre=self.pre, preR=self.preR, post=post | postRet, postR=postR)


def order():
    """Callees first: a DFS over the call graph (loops call themselves)."""
    seen, out = set(), []

    def calls(b):
        for s in b:
            if s[0] in ('call', 'callIf'):
                yield callee_of(s[1] if s[0] == 'call' else s[2])
            elif s[0] == 'dispatch':
                for f in s[2]:
                    yield callee_of(f)
            elif s[0] == 'ite':
                yield from calls(s[2]); yield from calls(s[3])
            elif s[0] == 'match':
                for a in s[2]:
                    yield from calls(a)

    def go(k):
        if k in seen:
            return
        seen.add(k)
        for c in calls(CORE[k][1]):
            if c in CORE and c != k:
                go(c)
        out.append(k)
    for k in CORE:
        go(k)
    return out


def main():
    only = sys.argv[sys.argv.index('--fn') + 1] if '--fn' in sys.argv else None
    sigs, res = {}, {}
    for k in order():
        f = Fn(k, sigs)
        sigs[k] = f.run()
        res[k] = f
    fa = [k for k, f in res.items() if f.uses]
    print(f'(a) values defined before use: {len(res) - len(fa)} of {len(res)} functions pass')
    tot = collections.Counter()
    for f in res.values():
        tot.update(f.uses)
    print('    failures by site:', dict(tot.most_common()))
    reads = sum(f.reads for f in res.values())
    cov = sum(f.covered for f in res.values())
    cls = collections.Counter(c for f in res.values() for c, _ in f.unc)
    print(f'(b) heap reads (defining loads, log2Ceil bit reads, callee preconditions at calls): {reads}; '
          f'covered in the function: {cov}')
    print('    uncovered by class:', dict(cls.most_common()))
    hard = {'pointer-from-memory', 'data-index', 'callee-returned', 'own-buffer-unwritten', 'other',
            'unknown-pointer', 'callee-loop-run-pre', 'pre-loop-run'}
    main_pre = {c for c, _ in res['main'].unc if c == 'pre-point'}
    clean = [k for k, f in res.items() if not f.uses and not any(c in hard for c, _ in f.unc)
             and not (k == 'main' and main_pre)]
    print(f'    functions with no read outside points (covered, or a point precondition on a parameter): '
          f'{len(clean)} of {len(res)}')
    nohard = [k for k, f in res.items() if not any(c in hard - {'pre-loop-run', 'callee-loop-run-pre'} for c, _ in f.unc)]
    print(f'    functions whose uncovered reads are only points or loop runs over parameters: {len(nohard)}')
    soft = {'pre-loop-run', 'callee-loop-run-pre'}
    ok = {k for k in nohard}
    calls = {}
    for k in res:
        cs = set()
        def sc(b):
            for st in b:
                if st[0] == 'call': cs.add(callee_of(st[1]))
                elif st[0] == 'callIf': cs.add(callee_of(st[2]))
                elif st[0] == 'dispatch': cs.update(callee_of(x) for x in st[2])
                elif st[0] == 'ite': sc(st[2]); sc(st[3])
                elif st[0] == 'match':
                    for a in st[2]: sc(a)
        sc(CORE[k][1]); calls[k] = cs - {k}
    closed = {}
    for k in order():
        closed[k] = k in ok and all(closed.get(c, False) for c in calls[k])
    print(f'    closed (accepted, every callee closed, transitively; loop runs allowed): {sum(closed.values())}')
    straight = [k for k in res if not calls[k] and not res[k].loop]
    print(f'    leaves (no call, no loop): {len(straight)}; accepted strictly: {sum(1 for k in straight if k in clean)}')
    def kind(k):
        if res[k].loop:
            return 'loop helper'
        if not calls[k]:
            return 'no call, no loop'
        if any(res[c].loop for c in calls[k] if c in res):
            return 'calls a loop'
        return 'calls, no loop'
    print('    by shape: functions, strict (covered or point preconditions), closed (loop runs allowed, callees closed):')
    for sh in ('no call, no loop', 'calls, no loop', 'calls a loop', 'loop helper'):
        ks = [k for k in res if kind(k) == sh]
        print(f'      {sh:18s} {len(ks):5d} {sum(1 for k in ks if k in clean):5d} {sum(1 for k in ks if closed[k]):5d}')
    side = collections.Counter()
    for f in res.values():
        side.update(f.side)
    print('    covered with a side condition or a loop rule:', dict(side))
    fnc = collections.Counter()
    for k, f in res.items():
        for c in set(c for c, _ in f.unc):
            fnc[c] += 1
    print('    functions per class:', dict(fnc.most_common()))
    fam = collections.Counter()
    for k, f in res.items():
        for c, _ in f.unc:
            if c in hard:
                fam[(c, k.split('__L')[0])] += 1
    print('    hard reads by class and family (top 40):')
    for (c, k), n in fam.most_common(40):
        print(f'      {c:24s} {k:40s} {n}')
    if '--list' in sys.argv:
        for k, f in sorted(res.items()):
            if f.uses or any(c in hard for c, _ in f.unc):
                print(k, dict(f.uses), collections.Counter(c for c, _ in f.unc))
    if only:
        f = res[only]
        print(only, 'reads', f.reads, 'covered', f.covered, dict(f.uses), collections.Counter(f.unc).most_common(20))


if __name__ == '__main__':
    main()
