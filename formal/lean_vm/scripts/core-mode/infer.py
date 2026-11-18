"""Heap certificates of the core IR for every function (`formal/notes/core-mode.md`, milestones 2 to 4): the
bytecode walk's inference (`scripts/mode-cert/infer.py`) ported to core names. A measurement and the certificates'
source, not a proof: `heapOk` (`LeanVM/Guest/CoreMode/Heap.lean`) checks what is emitted.

Bottom-up over the call graph, each function's body is walked in statement order (`Pass`), its signature (`Sig`)
re-inferred until stable. The pass's state (`St`):

* `env`: a value's monomial over core value numbers and a power of `g` (`heap.py`'s: constants, products, copies),
  plus a callee's returned words (`retM`) and a heap word read back (`hv`);
* `pts`: the written cells, each with its witness (the serial of its write event: a `load`, a heap hint's cell, a
  frame run's defined cell, a callee's guaranteed cell);
* `hv`: cells whose word is known (a store of a known value, a callee's `postV`), so that reading one back names the
  word (write-once memory: two `load`s of one address read one word);
* `pf`: cells holding a pointer whose cells at some offsets are written (a callee's `postP`, the caller's `preP`);
  `src`: the cell a loaded word came from;
* `runs`: runs of written cells `Q·g^(S·j)`, `lo <= j < hi`, with their witness (the function's `preR`, a callee's
  `postR`);
* `lts`: exponent facts `e(a) < e(b)` (the function's `term`, a range check, a `match` or dispatch selector);
* `cond`: facts known under a selector's value (a dispatch's arm), for a later dispatch or `match` on it;
* `D`: the defined values (`heap.reads_of`'s def-use, calls defining their returned words): a `load` of a defined word
  is a store, of an undefined one a read.

Each read gets a witness (`ev n`, `pre k`, `run r res`, `pf n o`, `preP k o`, `res ks`); a call meets its callee's
`pre`, `preR`, `preP`, `term` (each with a witness, in `calls`) and gains its `post`, `postR`, `postV`, `postP`,
`retM`. A loop helper (`callIf c self args; ret []`, one counter stepping by `g`, `loop_params`) is checked at its tail
call: its preconditions over the counter chained (the next one written by this iteration) or runs over the counter's
range, its term by the exit test, its guarantees by `retStay`. What no rule witnesses is a residual (`rules.py`) or
stays uncovered (reported by class).

usage (from formal/lean_vm): python3 -I scripts/core-mode/infer.py [--fn NAME] [--no-rules] [--json OUT]
  [--emit DIR [--check]]
"""
import sys, os, collections, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)
import coreir

D = coreir.load()
CORE, STABLE, POWS = D['core'], D['stable'], dict(D['pows'])
POWS[1] = 0
ORD = 2 ** 64 - 1

# The inference's rules beyond `heapOkC`'s format (`m2-format.md`), each switchable to measure what it buys:
FEATURES = {
    'join': 'facts of both sides of an `ite`/`match` kept after it (their meet)',
    'hv': 'a read of a cell whose word is known (a store, a callee\'s `postV`) names that word',
    'cond': 'facts kept under a selector\'s value (a dispatch arm), used by a later dispatch or `match` on it; an arm '
            'checked under `x = g^j`',
    'retM': 'a returned word\'s monomial over the arguments',
    'ptr': 'pointer facts: `preP`/`postP` (a cell holds a pointer with these cells past it written), `postV`',
    'callIfR': 'a loop\'s runs pushed at its conditional entry (empty when not entered: `lo = hi`)',
    'idx': 'a read at any index of a run (`b·j^S·g^(S·k)`, facts `lo <= j + k < hi`), bounds as residuals',
    'ptsrun': 'a run covered by its points (constant bounds, at most 64)',
    'armblock': 'arms writing a growing block `Q·[0, j + d)`: the run `Q·[0, e(x) + d)` after the dispatch',
    'hintrun': 'a heap hint\'s destination also a run',
    'div': 'a division\'s quotient gets the monomial `d / o`',
    'fa': 'a frame run\'s cells written when their values are defined (`frameAddr`)',
    'lts': 'range checks and selectors give exponent facts without a residual',
    'rules': 'residual rules (`rules.py`: `tabIdx`, `linSub`, ...)',
}
F = set(FEATURES)


def callee(name):
    return STABLE.get(name, name)


# ---- monomials `(bases, off)`, bases a sorted tuple of `(value, exponent)`, `off` modulo `g`'s order; an index is
# a monomial read as its word's exponent, `Σ e·e(b) + off`

def mk(bs, off):
    m = collections.defaultdict(int)
    for b, e in bs:
        m[b] += e
    return (tuple(sorted((b, e) for b, e in m.items() if e)), off % ORD)


def mmul(a, b):
    return mk(a[0] + b[0], a[1] + b[1])


def mpow(a, e):
    return mk(tuple((b, x * e) for b, x in a[0]), a[1] * e)


def mdiv(a, b):
    """`a / b` when `b`'s bases divide `a`'s, else `None`."""
    da = dict(a[0])
    for k, e in b[0]:
        if da.get(k, 0) < e:
            return None
        da[k] -= e
    return mk(tuple(da.items()), a[1] - b[1])


def shift(a, o):
    return (a[0], (a[1] + o) % ORD)


def base(v):
    return (((v, 1),), 0)


def num(k):
    return ((), k % ORD)


def ioff(a, b):
    """`b - a` when the two differ by a constant (same bases), else `None`."""
    if a[0] != b[0]:
        return None
    d = (b[1] - a[1]) % ORD
    return d if d < 2 ** 63 else d - ORD


def hint_stack_dests(h):
    k = h[0]
    dst = {'witness': 2, 'bits': 4, 'bitsExp': 3, 'digitsExp': 7, 'windowsExp': 5}.get(k)
    if dst is not None:
        d = h[dst]
        return list(d[1]) if d[0] == 'stack' else []
    if k == 'limbs':
        return list(h[2])
    if k == 'log2Ceil':
        return [h[4]]
    if k == 'inverse':
        return [h[2]]
    if k in ('alloc', 'allocDyn'):
        return [h[1]]
    return []


def hint_heap_dest(h):
    idx = {'witness': 2, 'bits': 4, 'bitsExp': 3, 'digitsExp': 7, 'windowsExp': 5}.get(h[0])
    if idx is None:
        return None
    d = h[idx]
    return (d[1], d[2], d[3]) if d[0] == 'heap' else None


# ---- the call graph

def stmts(ss):
    for s in ss:
        yield s
        if s[0] == 'ite':
            yield from stmts(s[2]); yield from stmts(s[3])
        elif s[0] == 'match':
            for a in s[2]:
                yield from stmts(a)


def callees(key):
    out = set()
    for s in stmts(CORE[key][1]):
        if s[0] == 'call':
            out.add(callee(s[1]))
        elif s[0] == 'callIf':
            out.add(callee(s[2]))
        elif s[0] == 'dispatch':
            out.update(callee(f) for f in s[2])
    return out


CALLS = {k: callees(k) for k in CORE}
IS_LOOP = {k for k in CORE if k in CALLS[k]}
CALLERS = collections.defaultdict(set)
for _k, _cs in CALLS.items():
    for _c in _cs:
        if _c != _k:
            CALLERS[_c].add(_k)


def topo():
    seen, out = set(), []

    def go(k):
        seen.add(k)
        for c in sorted(CALLS[k]):
            if c in CORE and c not in seen and c != k:
                go(c)
        out.append(k)
    for k in sorted(CORE):
        if k not in seen:
            go(k)
    return out


ORDER = topo()


def shape(k):
    if k in IS_LOOP:
        return 'loop'
    cs = CALLS[k] - {k}
    if not cs:
        return 'leaf'
    if any(c in IS_LOOP for c in cs):
        return 'calls-loop'
    return 'calls'


# ---- signatures: monomials over parameter numbers `0..m-1` and returned words `m + j`

class Sig:
    FIELDS = ('pre', 'post', 'preR', 'postR', 'term', 'postV', 'preP', 'postP')

    def __init__(self, m):
        self.m = m
        self.pre = []        # cells a caller guarantees written
        self.post = []       # cells written at return
        self.preR = []       # runs (Q, S, lo, hi)
        self.postR = []
        self.term = []       # (a, b): e(a) < e(b) at entry
        self.postV = []      # (cell, word): the cell holds the word at return
        self.preP = []       # (cell, offsets): the cell's word is a pointer, these cells past it written
        self.postP = []
        self.retM = {}       # returned word j -> its monomial over the parameters
        self.ctr = None      # a loop's counter and bound parameters
        self.bnd = None

    def key(self):
        return tuple(tuple(getattr(self, f)) for f in self.FIELDS) + (tuple(sorted(self.retM.items())),)

    def clone(self):
        G = Sig(self.m)
        for f in self.FIELDS:
            setattr(G, f, list(getattr(self, f)))
        G.retM, G.ctr, G.bnd = dict(self.retM), self.ctr, self.bnd
        return G

    def size(self):
        return sum(len(getattr(self, f)) for f in self.FIELDS) + len(self.retM)


SIGS = {}


# ---- the pass

class St:
    __slots__ = ('env', 'pts', 'hv', 'pf', 'src', 'runs', 'lts', 'D', 'alias', 'cond')

    def __init__(self):
        self.env, self.pts, self.hv, self.pf, self.src = {}, {}, {}, {}, {}
        self.runs, self.lts, self.D, self.alias, self.cond = [], set(), set(), {}, {}

    def copy(self):
        s = St()
        s.env, s.pts, s.hv, s.pf, s.src = dict(self.env), dict(self.pts), dict(self.hv), dict(self.pf), dict(self.src)
        s.runs, s.lts, s.D, s.alias, s.cond = list(self.runs), set(self.lts), set(self.D), dict(self.alias), \
            dict(self.cond)
        return s


def meet(sts, sel=None):
    """The facts every state has; with `sel = (x, js)`, each state's others kept under `x = g^j`."""
    live = [(j, s) for j, s in enumerate(sts) if s is not None]
    if not live:
        return None
    s = live[0][1].copy()
    for _, t in live[1:]:
        s.env = {v: m for v, m in s.env.items() if t.env.get(v) == m}
        s.pts = {c: w for c, w in s.pts.items() if c in t.pts}
        s.hv = {c: w for c, w in s.hv.items() if t.hv.get(c) == w}
        s.pf = {c: (o & t.pf[c][0], w) for c, (o, w) in s.pf.items() if c in t.pf and o & t.pf[c][0]}
        s.src = {v: c for v, c in s.src.items() if t.src.get(v) == c}
        tr = {r for r, _ in t.runs}
        s.runs = [(r, w) for r, w in s.runs if r in tr]
        s.lts &= t.lts
        s.D &= t.D
        s.cond = {k: v for k, v in s.cond.items() if t.cond.get(k) is v}
    if sel is not None:
        x, js = sel
        for j, t in live:
            pts = {c: w for c, w in t.pts.items() if c not in s.pts}
            runs = [(r, w) for r, w in t.runs if (r, w) not in s.runs]
            hv = {c: w for c, w in t.hv.items() if c not in s.hv}
            if pts or runs or hv:
                old = s.cond.get((x, js[j]), ({}, [], {}))
                s.cond[(x, js[j])] = ({**old[0], **pts}, old[1] + runs, {**old[2], **hv})
    return s


class Pass:
    def __init__(self, key, sig, rules=True):
        self.key = key
        self.params, self.body = CORE[key]
        self.m = len(self.params)
        self.sig = sig
        self.loop = key in IS_LOOP
        self.rules = rules
        self.n = 0                       # point serial
        self.nr = 0                      # run serial
        self.reads = {}                  # (d, p, off) -> witness
        self.calls = []                  # per call statement, in order: (callee, [(what, witness)])
        self.res = []                    # residuals
        self.unc = []                    # uncovered reads: (class, cell, site)
        self.rets = []                   # (state, returned values) at each `ret`
        self.tails = []                  # (state, args, cond) at the loop's tail call
        self.ret_wits = []               # per `ret`, the witnesses of the own guarantees
        self.at_tail = False
        self.stats = collections.Counter()
        self.defkind = {}
        self.retvals = None
        self.adds = {}
        self.ltprov = {}
        self.ltkey = {}
        self.eqs = []
        self.defs = {}
        for s in stmts(self.body):
            if s[0] == 'a' and s[1][0] in ('add', 'mul', 'const', 'copy'):
                self.defs.setdefault(s[1][1], s[1])

    # -- monomials
    subst = {}

    def mono(self, st, v):
        m = st.env.get(v)
        if m is None:
            m = base(v)
        if self.subst and any(b in self.subst for b, _ in m[0]):
            m = self.sub(m)
        return m

    def sub(self, m):
        """`m` under the arm's assumptions: a base `b` is `g^k` (`b = x·g^-t` for the selector `x = g^j`)."""
        bs, off = [], m[1]
        for b, e in m[0]:
            if b in self.subst:
                off += e * self.subst[b]
            else:
                bs.append((b, e))
        return mk(tuple(bs), off)

    def assume(self, st, x, j):
        """Arm `j` of a selector `x`: its monomial `b·g^t` gives `b = g^(j - t)`, if `j >= t`."""
        m = self.mono(st, x)
        if len(m[0]) == 1 and m[0][0][1] == 1:
            t = m[1] if m[1] < 2 ** 40 else m[1] - ORD
            if j - t >= 0:
                return {**self.subst, m[0][0][0]: j - t}
        return self.subst

    def iface(self, c):
        return all(b < self.m for b, _ in c[0])

    def addres(self, r):
        """A residual's index; `e(a·g^k) < e(b)` for the largest `k` asked of one `a`, `b` (the reads of one run at
        several offsets ask one bound)."""
        if r in self.res:
            return self.res.index(r)
        if r[0] == 'lt' and r[1][1] < 2 ** 40:
            key = (r[1][0], r[2], r[3:])
            i = self.ltkey.get(key)
            if i is not None:
                if self.res[i][1][1] < r[1][1]:
                    self.res[i] = r
                return i
            self.ltkey[key] = len(self.res)
        self.res.append(r)
        self.stats['res-' + r[0]] += 1
        return len(self.res) - 1

    # -- exponent facts
    def lt(self, st, a, b, used=None):
        """`e(a) < e(b)` from the facts in scope (constants, the same bases, a fact shifted); a fact that is a
        residual (a hint's range, `ltprov`) appends its index to `used`."""
        d = ioff(a, b)
        if d is not None:
            return d > 0
        if not a[0] and a[1] == 0 and b[0] and b[1] > 0 and b[1] < 2 ** 32:
            return True
        for x, y in st.lts:
            da, db = ioff(x, a), ioff(y, b)
            if da is not None and db is not None and da <= db:
                k = self.ltprov.get((x, y))
                if k is not None:
                    if used is None:
                        continue
                    if isinstance(k, tuple):
                        k = self.ltprov[(x, y)] = self.addres(('lt', x, y, k[1], k[2]))
                    used.append(k)
                return True
        return False

    def le(self, st, a, b, used=None):
        if not a[0] and a[1] == 0:
            return True
        return self.lt(st, a, shift(b, 1), used)

    def hint_bound(self, st, v, n):
        """A hint's word `v = g^w` with `w < n` by the hint's kind (a window, a digit): a fact, a residual of the
        hint family when used."""
        self.fact(st, base(v), num(n), 'hint', free=False, cidx=(('val', v), ('num', n)))

    def fact(self, st, a, b, fam, free=None, cidx=None):
        """The exponent fact `e(a) < e(b)`: free (`lts`), or a residual of the family `fam`, listed where used;
        `cidx`, the fact over value numbers (`CIdx`), when it has that form."""
        st.lts.add((a, b))
        if free is None:
            free = 'lts' in F
        if not free and (a, b) not in self.ltprov:
            self.ltprov[(a, b)] = ('fam', fam, cidx)

    # -- coverage
    def idx_in(self, c, r):
        """The index of the cell `c` in the run `r = (Q, S, lo, hi)`: `c = Q·g^(S·j)`, `j` an index, or `None`."""
        Q, S = r[0], r[1]
        rest = dict(c[0])
        for b, e in Q[0]:
            if rest.get(b, 0) < e:
                return None
            rest[b] -= e
        rest = {b: e for b, e in rest.items() if e}
        if any(e % S for e in rest.values()):
            return None
        do = (c[1] - Q[1]) % ORD
        if do < 2 ** 40:
            if do % S:
                return None
            k = do // S
        else:
            neg = ORD - do
            if neg % S or not rest:
                # a constant index below the run's base: not one of its cells
                return None
            k = -(neg // S)
        return mk(tuple((b, e // S) for b, e in rest.items()), k)

    def lt_fact(self, st, a, b, used):
        """`(a, b)` is a fact (the own term, or a residual, listed in `used`)."""
        if (a, b) not in st.lts:
            return False
        k = self.ltprov.get((a, b))
        if k is not None:
            if isinstance(k, tuple):
                k = self.ltprov[(a, b)] = self.addres(('lt', a, b, k[1], k[2]))
            used.append(k)
        return True

    def lean_in(self, st, j, r, u):
        """`heapOkC`'s point rule for a run: the counter form (`j = lo`, `(lo, hi)` a fact) or the constant form."""
        lo, hi = r[2], r[3]
        if j == lo:
            return self.lt_fact(st, lo, hi, u)
        if j[0] or j[1] >= 2 ** 62 or lo[0] or lo[1] > j[1]:
            return False
        if not hi[0]:
            return j[1] < hi[1]
        for k2 in range(j[1], j[1] + 65):
            if self.lt_fact(st, num(k2), hi, u):
                return True
        return False

    def find_run(self, st, c, runs, used=None):
        """A run holding `c` with its bounds known (the residuals used appended to `used`), else the first holding it
        by shape, with which bounds fail."""
        best = None
        for r, rw in reversed(runs):
            j = self.idx_in(c, r)
            if j is None:
                continue
            u = []
            if 'idx' not in F:
                if self.lean_in(st, j, r, u):
                    if used is not None:
                        used.extend(u)
                    return r, rw, j, True, True
                continue
            okl, okh = self.le(st, r[2], j, u), self.lt(st, j, r[3], u)
            if okl and okh:
                if used is not None:
                    used.extend(u)
                return r, rw, j, True, True
            if best is None and not (not okl and not j[0] and not r[2][0]) and not (not okh and not j[0] and not r[3][0]):
                best = (r, rw, j, okl, okh)
        return best

    def cover(self, st, c, site, allow_pre=True, conds=None):
        """A witness that the cell `c` is written, or `None`."""
        w = st.pts.get(c)
        if w is not None:
            self.stats['w-ev'] += 1
            return w
        if conds:
            for pts, runs, hv in conds:
                if c in pts:
                    self.stats['w-cond'] += 1
                    return pts[c]
        runs = st.runs + [x for cd in (conds or ()) for x in cd[1]]
        used = []
        best = self.find_run(st, c, runs, used)
        if best is not None and best[3] and best[4]:
            self.stats['w-run'] += 1
            return ('run', best[1], used)
        # through a pointer loaded from a cell with a pointer fact
        if 'ptr' in F and len(c[0]) == 1 and c[0][0][1] == 1:
            d = c[0][0][0]
            s = st.src.get(d)
            if s is not None:
                f = st.pf.get(s[0])
                if f is not None and c[1] in f[0]:
                    self.stats['w-pf'] += 1
                    return ('pf', f[1], c[1])
                if allow_pre and self.iface(s[0]) and c[1] < 2 ** 20 and not (
                        self.loop and any(b == self.sig.ctr for b, _ in s[0][0])):
                    return self.add_preP(s[0], c[1])
        if allow_pre and not self.at_tail and self.iface(c) and c[0]:
            if self.loop and any(b == self.sig.ctr for b, _ in c[0]):
                if c not in self.sig.pre:
                    self.sig.pre.append(c)
                self.stats['w-pre-ctr'] += 1
                return ('pre', self.sig.pre.index(c))
            if c not in self.sig.pre:
                self.sig.pre.append(c)
            self.stats['w-pre'] += 1
            return ('pre', self.sig.pre.index(c))
        if best is not None and 'idx' in F:
            r, rw, j, okl, okh = best
            res = []
            if not okl:
                res.append(self.addres(('lt', r[2], shift(j, 1), 'idx')))
            if not okh:
                res.append(self.addres(('lt', j, r[3], 'idx')))
            self.stats['w-run-res'] += 1
            return ('run', rw, res)
        if 'rules' in F:
            import rules
            w = rules.read(self, st, c, site)
            if w is not None:
                return w
        return None

    def add_preP(self, cell, o):
        for k, (c, offs) in enumerate(self.sig.preP):
            if c == cell:
                if o not in offs:
                    self.sig.preP[k] = (c, tuple(sorted(set(offs) | {o})))
                self.stats['w-preP'] += 1
                return ('preP', k, o)
        self.sig.preP.append((cell, (o,)))
        self.stats['w-preP'] += 1
        return ('preP', len(self.sig.preP) - 1, o)

    def classify(self, st, c):
        if c is None:
            return 'unknown'
        if not c[0]:
            return 'absolute'
        kinds = set()
        for b, _ in c[0]:
            if b < self.m:
                kinds.add('counter' if self.loop and b == self.sig.ctr else 'param')
            else:
                kinds.add(self.defkind.get(b, 'other'))
        if 'load' in kinds:
            return 'pointer-from-memory'
        if 'ret' in kinds:
            return 'callee-returned'
        if kinds & {'hint', 'add', 'keccak', 'witness'}:
            return 'data-index'
        if kinds & {'alloc', 'frameAddr'}:
            return 'own-buffer-unwritten'
        return 'other:' + ','.join(sorted(kinds))

    def unc_read(self, st, c, site, kind=''):
        self.unc.append((kind + self.classify(st, c), c, site))
        self.stats['uncovered'] += 1
        return ('unc',)

    def read(self, st, c, site):
        w = self.cover(st, c, site, conds=self.armconds)
        return w if w is not None else self.unc_read(st, c, site)

    # -- writes
    def push(self, st, c):
        st.pts[c] = ('ev', self.n)
        self.n += 1

    def pushR(self, st, r):
        st.runs.append((r, self.nr))
        self.nr += 1

    def define(self, st, v, m=None, kind=None):
        st.D.add(v)
        if m is not None and v not in st.env:
            st.env[v] = m
        if kind is not None:
            self.defkind.setdefault(v, kind)
        for c in st.alias.pop(v, ()):
            self.push(st, c)

    # -- atoms
    def atom(self, st, a):
        k = a[0]
        if k == 'const':
            d, (l0, l1) = a[1], a[2]
            e = POWS.get(l0) if l1 == 0 else None
            self.define(st, d, ((), e) if e is not None else None, 'const')
        elif k == 'mul':
            d, x, y = a[1:]
            if x in st.D and y in st.D or d not in st.D:
                self.define(st, d, mmul(self.mono(st, x), self.mono(st, y)), 'mul')
            else:
                # a division `u = d / o`: its monomial when `o`'s divides `d`'s
                for u, o in ((x, y), (y, x)):
                    if u not in st.D:
                        self.define(st, u, mdiv(self.mono(st, d), self.mono(st, o)) if 'div' in F else None, 'mul')
        elif k == 'add':
            d, x, y = a[1:]
            self.adds[d] = (x, y)
            kn = [v in st.D for v in (d, x, y)]
            if kn[1] and kn[2] or sum(kn) != 2:
                self.define(st, d, None, 'add')
            else:
                self.define(st, [d, x, y][kn.index(False)], None, 'add')
        elif k in ('copy', 'assertEq'):
            x, y = a[1:]
            mx, my = st.env.get(x), st.env.get(y)
            if mx is not None and my is not None and mx != my:
                self.eqs.append((mx, my))
            if mx is None and my is not None:
                st.env[x] = my
            elif my is None and mx is not None:
                st.env[y] = mx
            elif mx is None and my is None and (y in st.D or k == 'copy'):
                st.env[x] = base(y)
            elif mx is None and my is None and x in st.D:
                st.env[y] = base(x)
            for u, o in ((x, y), (y, x)):
                if o in st.src and u not in st.src:
                    st.src[u] = st.src[o]
            if x in st.D or y in st.D or k == 'copy':
                for v in (x, y):
                    if v not in st.D:
                        self.define(st, v, None, self.defkind.get(y if v == x else x, 'copy'))
        elif k == 'load':
            d, p, off = a[1:]
            c = shift(self.mono(st, p), off)
            if d in st.D:
                self.stats['store'] += 1
                if 'hv' in F:
                    st.hv.setdefault(c, self.mono(st, d))
            else:
                w = self.read(st, c, ('load', d, p, off))
                old = self.reads.get((d, p, off))
                if old is not None and old != w:
                    self.stats['read-twice'] += 1
                self.reads[(d, p, off)] = w
                if 'hv' in F:
                    w = st.hv.get(c)
                    if w is None and self.armconds:
                        for _, _, hv in self.armconds:
                            w = w or hv.get(c)
                    if w is not None and d not in st.env:
                        st.env[d] = w
                        self.stats['hv-read'] += 1
                self.define(st, d, None, 'load')
                if 'ptr' in F:
                    st.src[d] = (c, self.n)
                if 'hv' in F:
                    st.hv.setdefault(c, self.mono(st, d))
            self.push(st, c)
        elif k == 'assertNe':
            self.define(st, a[3], None, 'assertNe')
        elif k == 'rangeCheck':
            x, y, t1, t2, kk = a[1:]
            if y not in st.D:
                self.define(st, y, None, 'rangeCheck')
            self.fact(st, self.mono(st, x), shift(self.mono(st, kk), 1), 'rangeCheck')
        elif k == 'keccak':
            for v in a[2]:
                self.define(st, v, None, 'keccak')
        elif k == 'frameAddr':
            p, run = a[1], a[2]
            self.define(st, p, None, 'frameAddr')
            mp = self.mono(st, p)
            for i, v in enumerate(run):
                c = shift(mp, i)
                if 'fa' not in F:
                    continue
                if v in st.D:
                    self.push(st, c)
                    if 'hv' in F:
                        st.hv.setdefault(c, self.mono(st, v))
                else:
                    st.alias.setdefault(v, []).append(c)
        elif k == 'hint':
            h = a[1]
            hd = hint_heap_dest(h)
            if hd is not None:
                p, off, n = hd
                mp = self.mono(st, p)
                for j in range(n):
                    self.push(st, shift(mp, off + j))
                if n > 1 and 'hintrun' in F:
                    self.pushR(st, (shift(mp, off), 1, num(0), num(n)))
            if h[0] == 'log2Ceil' and h[1][0] == 'heap':
                _, p, off, ln = h[1]
                mp = self.mono(st, p)
                for j in range(min(h[2], ln)):
                    self.read(st, shift(mp, off + j), ('log2Ceil', j))
            for v in hint_stack_dests(h):
                self.define(st, v, None, 'alloc' if h[0] in ('alloc', 'allocDyn') else 'hint')
            bnd = {'windowsExp': lambda: 2 ** h[3], 'digitsExp': lambda: 2 ** h[4],
                   'log2Ceil': lambda: max(h[2], h[3]) + 1}.get(h[0])
            if bnd is not None:
                for v in hint_stack_dests(h):
                    self.hint_bound(st, v, bnd())

    # -- calls
    def tr(self, st, c, args, rets):
        """A callee's monomial, over its parameters (`b < m`) and returned words (`m + j`), in this function."""
        out = ((), c[1])
        for b, e in c[0]:
            if b < len(args):
                mb = self.mono(st, args[b])
            elif rets is not None and b - len(args) < len(rets):
                mb = self.mono(st, rets[b - len(args)])
            else:
                return None
            out = mmul(out, mpow(mb, e))
        return out

    def trR(self, st, r, args, rets):
        Q, S, lo, hi = r
        t = [self.tr(st, x, args, rets) for x in (Q, lo, hi)]
        return None if None in t else (t[0], S, t[1], t[2])

    def cover_run(self, st, r, site, conds=None):
        """A witness that every cell of the run `r` is written: a known run holding it, its points (constant bounds,
        at most 64), the function's own precondition; with residual bounds; else `None`."""
        Q, S, lo, hi = r
        n = ioff(lo, hi)
        if n is not None and n <= 0:
            self.stats['wr-empty'] += 1
            return ('empty',)
        best = None
        for R, rw in reversed(st.runs + [x for cd in (conds or ()) for x in cd[1]]):
            if R[1] != S:
                continue
            if 'idx' not in F:
                u = []
                if R[0] == Q and self.lean_lower(st, lo, R, u) and self.lean_upper(st, hi, R, u):
                    self.stats['wr-run'] += 1
                    return ('run', rw, u)
                continue
            j = self.idx_in(Q, R)
            if j is None:
                continue
            jl, jh = mmul(j, lo), mmul(j, hi)
            okl, okh = self.le(st, R[2], jl), self.le(st, jh, R[3])
            if okl and okh:
                self.stats['wr-run'] += 1
                return ('run', rw, [])
            false = (not okl and not jl[0] and not R[2][0]) or (not okh and not jh[0] and not R[3][0])
            if not false and (best is None or (okl or okh) and not (best[2] or best[3])):
                best = (R, rw, okl, okh, jl, jh)
        if n is not None and n <= 64 and not lo[0] and 'ptsrun' in F:
            ws = []
            for i in range(n):
                c = shift(Q, S * (lo[1] + i))
                w = self.cover(st, c, site, allow_pre=False, conds=conds)
                if w is None or w[0] == 'run' and w[2]:
                    break
                ws.append(w)
            else:
                self.stats['wr-pts'] += 1
                return ('pts', ws)
        if not self.at_tail and self.iface(Q) and self.iface(lo) and self.iface(hi) and Q[0] and not (
                self.loop and any(b == self.sig.ctr for b, _ in Q[0])):
            if r not in self.sig.preR:
                self.sig.preR.append(r)
            self.stats['wr-preR'] += 1
            return ('run', ('preR', self.sig.preR.index(r)), [])
        if best is not None and 'idx' in F:
            R, rw, okl, okh, jl, jh = best
            res = []
            if not okl:
                res.append(self.addres(('lt', R[2], shift(jl, 1), 'idx')))
            if not okh:
                res.append(self.addres(('lt', jh, shift(R[3], 1), 'idx')))
            self.stats['wr-run-res'] += 1
            return ('run', rw, res)
        if 'rules' in F:
            import rules
            return rules.run(self, st, r, site, conds)
        return None

    def lean_lower(self, st, lo, R, u):
        lo2 = R[2]
        if lo == lo2:
            return True
        if not lo[0] and not lo2[0]:
            return lo2[1] <= lo[1] < 2 ** 62
        return lo == shift(lo2, 1) and self.lt_fact(st, lo2, R[3], u)

    def lean_upper(self, st, hi, R, u):
        hi2 = R[3]
        if hi == hi2:
            return True
        if not hi[0] and not hi2[0]:
            return hi[1] <= hi2[1] and hi[1] < 2 ** 62
        if not hi[0] and hi[1] < 2 ** 62:
            return any(self.lt_fact(st, num(k), hi2, u) for k in range(max(0, hi[1] - 1), hi[1] + 64))
        return False

    def cover_ptr(self, st, c, offs, site, conds=None):
        """The word at `c` is a pointer whose cells at `offs` are written: a pointer fact, or the word known and
        its cells covered."""
        f = st.pf.get(c)
        if f is not None and set(offs) <= f[0]:
            self.stats['wp-pf'] += 1
            return ('pf', f[1])
        w = st.hv.get(c)
        if w is None and conds:
            for _, _, hv in conds:
                w = w or hv.get(c)
        if w is not None:
            ws = []
            for o in offs:
                x = self.cover(st, shift(w, o), site, conds=conds)
                if x is None:
                    return None
                ws.append(x)
            self.stats['wp-word'] += 1
            return ('word', ws)
        if self.iface(c) and not (self.loop and any(b == self.sig.ctr for b, _ in c[0])):
            for o in offs:
                w = self.add_preP(c, o)
            return ('preP', w[1])
        return None

    def call(self, st, f, args, rets, cond=None, conditional=False, conds=None, record=True):
        G = SIGS.get(f)
        ws = []
        site = ('call', f)
        if G is not None:
            for c in G.pre:
                t = self.tr(st, c, args, None)
                w = self.cover(st, t, site, conds=conds) if t is not None else None
                ws.append(('pre', w if w is not None else self.unc_read(st, t, site)))
            for r in G.preR:
                t = self.trR(st, r, args, None)
                w = self.cover_run(st, t, site, conds) if t is not None else None
                ws.append(('preR', w if w is not None else self.unc_read(st, t[0] if t else None, site, 'run:')))
            for c, offs in G.preP:
                t = self.tr(st, c, args, None)
                w = self.cover_ptr(st, t, offs, site, conds) if t is not None else None
                ws.append(('preP', w if w is not None else self.unc_read(st, t, site, 'ptr:')))
            # a callee's `term` is not met at the call: the composition proves it of every honest instance
        self.lastws = ws
        if record:
            self.calls.append((f, ws))
        if G is None:
            for v in rets or ():
                self.define(st, v, None, 'ret')
            return
        if 'retM' in F:
            for j, m in G.retM.items():
                if rets and j < len(rets):
                    t = self.tr(st, m, args, None)
                    if t is not None and rets[j] not in st.env:
                        st.env[rets[j]] = t
        for v in rets or ():
            self.define(st, v, None, 'ret')
        if not conditional:
            for c in G.post:
                t = self.tr(st, c, args, rets)
                if t is not None:
                    self.push(st, t)
            for c, w in (G.postV if 'ptr' in F or 'hv' in F else ()):
                t, tw = self.tr(st, c, args, rets), self.tr(st, w, args, rets)
                if t is not None and tw is not None:
                    st.hv.setdefault(t, tw)
            for c, offs in (G.postP if 'ptr' in F else ()):
                t = self.tr(st, c, args, rets)
                if t is not None:
                    st.pf[t] = (frozenset(offs) | st.pf.get(t, (frozenset(), None))[0], ('ev', self.n))
                    self.n += 1
        for r in G.postR:
            t = self.trR(st, r, args, rets)
            if t is None:
                continue
            # a loop's run over `[lo, hi)` is empty when the loop is not entered (`lo = hi`)
            if conditional and not ('callIfR' in F and cond is not None and self.cond_is(st, cond, t[2], t[3])):
                continue
            self.pushR(st, t)

    def cond_is(self, st, c, a, b):
        """The condition `c` is `x + y`, the words of the indices `a`, `b` (so `c ≠ 0` iff `a ≠ b`)."""
        d = self.adds.get(c)
        if d is None:
            return False
        return {self.mono(st, d[0]), self.mono(st, d[1])} == {a, b}

    # -- statements
    armconds = None

    def conds_of(self, st, x, j):
        """The facts known under `x = g^j`: kept under `y = g^i` with `y = x·g^d`, `i = j + d`."""
        xm = self.mono(st, x)
        out = []
        for (y, i), cd in st.cond.items():
            d = ioff(xm, y)
            if d is not None and i == j + d:
                out.append(cd)
        return out

    def block(self, st, ss):
        for s in ss:
            if st is None:
                return None
            k = s[0]
            if k == 'a':
                self.atom(st, s[1])
            elif k == 'ite':
                st = self.join(st, [self.block(st.copy(), s[2]), self.block(st.copy(), s[3])])
            elif k == 'match':
                outs = []
                x = self.mono(st, s[1])
                for j, arm in enumerate(s[2]):
                    t = st.copy()
                    old = self.subst
                    if 'cond' in F:
                        for pts, runs, hv in self.conds_of(st, s[1], j):
                            t.pts.update({c: w for c, w in pts.items() if c not in t.pts})
                            t.runs += runs
                            t.hv.update({c: w for c, w in hv.items() if c not in t.hv})
                        self.subst = self.assume(st, s[1], j)
                    outs.append(self.block(t, arm))
                    self.subst = old
                st0 = st
                st = self.join(st, outs, (x, list(range(len(s[2])))))
                if st is not None:
                    self.fact(st, x, num(len(s[2])), 'selector', cidx=(('val', s[1]), ('num', len(s[2]))))
                    if 'armblock' in F and 'join' in F:
                        self.arm_blocks(st, x, outs)
            elif k == 'call':
                self.call(st, callee(s[1]), s[2], s[3])
            elif k == 'callIf':
                f = callee(s[2])
                if f == self.key:
                    self.tails.append((st.copy(), s[3], s[1]))
                    self.calls.append((f, self.tail_wits(st, s[3])))
                else:
                    self.call(st, f, s[3], [], cond=s[1], conditional=True)
            elif k == 'dispatch':
                self.dispatch(st, s)
            elif k == 'ret':
                if 'rules' in F:
                    import rules
                    rules.derive(self, st)
                if self.retvals is None:
                    self.retvals = s[1]
                self.rets.append((st, s[1]))
                self.ret_wits.append(self.ret_wit(st, s[1]))
                return None
        return st

    def tail_wits(self, st, args):
        """The loop's tail call: its own `pre` and `preR` at the next iteration's words (chained: written by this
        one; the own precondition; the own run by the shifted-lower rule). Misses are the next round's runs."""
        G, ws = self.sig, []
        self.at_tail = True
        for c in G.pre:
            t = self.tr(st, c, args, None)
            if t in G.pre:
                w = ('pre', G.pre.index(t))
            else:
                w = self.cover(st, t, ('tail',), allow_pre=False)
            ws.append(('pre', w if w is not None else ('miss', t)))
        for r in G.preR:
            t = self.trR(st, r, args, None)
            w = self.cover_run(st, t, ('tail',)) if t is not None else None
            ws.append(('preR', w if w is not None else ('miss', t)))
        self.at_tail = False
        return ws

    def ret_wit(self, st, vs):
        """At a `ret`: a witness of each own `post` cell and `postR` run at the parameters and the returned words (a
        loop's run over its counter by the counter's point: accumulation)."""
        G, ws = self.sig, []
        self.at_tail = True
        ps = list(range(self.m))
        sts = [t for t, *_ in self.tails] if self.loop and self.tails else [st]
        for c in G.post:
            t = self.tr(st, c, ps, vs)
            w = self.cover(sts[0], t, ('ret',), allow_pre=False) if t is not None else None
            ws.append(('post', w if w is not None else ('miss', t)))
        for r in G.postR:
            if self.loop and r[2] == base(G.ctr) and G.term and r[3] == G.term[0][1]:
                t = mmul(r[0], mpow(base(G.ctr), r[1]))
                w = self.cover(sts[0], t, ('ret',), allow_pre=False)
            else:
                t = self.trR(st, r, ps, vs)
                w = self.cover_run(sts[0], t, ('ret',)) if t is not None else None
            ws.append(('postR', w if w is not None else ('miss', r)))
        self.at_tail = False
        return ws

    def join(self, st, outs, sel=None):
        """After a branch: the meet of the blocks that fall through (`join`), or the state before it with the
        defined values met (`heapOkC`: what a block learns stays in it)."""
        if 'join' in F:
            return meet(outs, sel if 'cond' in F else None)
        live = [t for t in outs if t is not None]
        if not live:
            return None
        t = st.copy()
        t.D = set.intersection(*[x.D for x in live])
        return t

    def dispatch(self, st, s):
        x, fs, args, rets = s[1], [callee(f) for f in s[2]], s[3], s[4]
        xm = self.mono(st, x)
        outs = []
        ws = []
        n0, nr0 = self.n, self.nr
        for j, f in enumerate(fs):
            self.n, self.nr = n0, nr0
            t = st.copy()
            cd = self.conds_of(st, x, j) if 'cond' in F else []
            self.armconds = cd
            old = self.subst
            if 'cond' in F:
                self.subst = self.assume(st, x, j)
            self.call(t, f, args, rets, conds=cd, record=False)
            ws.extend(self.lastws)
            self.subst = old
            self.armconds = None
            outs.append(t)
        self.calls.append((tuple(fs), ws))
        m = meet(outs, (xm, list(range(len(fs)))) if 'cond' in F else None)
        # `heapOkC`'s numbering: the arms' common guarantees, in the first arm's order, one serial each
        self.n, self.nr = n0, nr0
        pts, runs = dict(st.pts), list(st.runs)
        sigs = [SIGS.get(f) for f in fs]
        if all(sigs):
            posts = [[self.tr(st, c, args, rets) for c in G.post] for G in sigs]
            others = [set(p) for p in posts[1:]]
            for t in posts[0]:
                if t is not None and all(t in o for o in others):
                    pts[t] = ('ev', self.n)
                    self.n += 1
            postRs = [[self.trR(st, r, args, rets) for r in G.postR] for G in sigs]
            othersR = [set(p) for p in postRs[1:]]
            for t in postRs[0]:
                if t is not None and all(t in o for o in othersR):
                    runs.append((t, self.nr))
                    self.nr += 1
        for a in St.__slots__:
            setattr(st, a, getattr(m, a))
        if 'join' not in F or 'cond' not in F:
            st.pts, st.runs = pts, runs
        else:
            st.pts.update({c: w for c, w in pts.items() if c in st.pts})
            st.runs = runs + [x for x in st.runs if x[0] not in {r for r, _ in runs}]
        self.fact(st, xm, num(len(fs)), 'selector', cidx=(('val', x), ('num', len(fs))))
        if 'armblock' in F:
            self.arm_blocks(st, xm, outs)

    def arm_blocks(self, st, xm, outs):
        """Arms of a selector `x` each writing a growing block `Q·g^(c..j+c)`, `c <= 0`: the run `Q·[0, e(x) + d)`
        (`armBlocks`), `d` the least block's excess over its arm index."""
        if len(outs) < 3 or any(t is None for t in outs) or not xm[0]:
            return
        by = collections.defaultdict(set)
        for c in outs[-1].pts:
            if c[1] < 2 ** 20 and c[0] and c not in st.pts:
                by[c[0]].add(c[1])
        for Q, offs in by.items():
            ns = []
            for j, t in enumerate(outs):
                n = 0
                while (Q, n) in t.pts:
                    n += 1
                ns.append(n)
            K = (ns[-1] - ns[0]) // (len(outs) - 1)
            if K < 1:
                continue
            d = min(n - K * j for j, n in enumerate(ns))
            if d < 0 or K * (len(outs) - 1) + d < 2:
                continue
            r = ((Q, 0), 1, num(0), shift(mpow(xm, K), d))
            self.stats['arm-block'] += 1
            self.pushR(st, r)

    def run(self):
        st = St()
        for v in self.params:
            st.D.add(v)
            # a parameter is its own base: an `assert ==` relating it to a product is an equation (`eqs`)
            st.env[v] = base(v)
        G = self.sig
        for i, r in enumerate(G.preR):
            st.runs.append((r, ('preR', i)))
        for a, b in G.term:
            st.lts.add((a, b))
        for k, (c, offs) in enumerate(G.preP):
            st.pf[c] = (frozenset(offs), ('preP', k))
        self.block(st, self.body)
        return self


# ---- inference of one function

def loop_params(key):
    """A loop's counter (the one argument its tail call changes) and bound (the exit test's other side)."""
    params, body = CORE[key]
    t = [s for s in body if s[0] == 'callIf' and callee(s[2]) == key][-1]
    ctr = [i for i, a in enumerate(t[3]) if a != params[i]][0]
    defs = {s[1][1]: s[1] for s in stmts(body) if s[0] == 'a' and s[1][0] in ('add', 'mul', 'const', 'copy')}
    c = defs.get(t[1])
    bnd = None
    if c and c[0] == 'add':
        for x in c[2:]:
            if x in params and x != ctr:
                bnd = x
        if bnd is None:
            for x in c[2:]:
                d = defs.get(x)
                if d and d[0] == 'const' and d[2][1] == 0 and d[2][0] in POWS:
                    bnd = ('num', POWS[d[2][0]])
    return ctr, bnd


MAXPTS = 4096


def retsig(P, G):
    """Guarantees at return: cells, runs, heap words, pointer facts over the parameters and returned words, on every
    path; returned words' monomials over the parameters."""
    if not P.rets:
        return
    m = P.m
    names = {}
    alias = []
    G.retM = {}
    for j, v in enumerate(P.retvals or ()):
        ms = {P.mono(st, v) for st, vs in P.rets}
        if len(ms) == 1:
            mv = ms.pop()
            if P.iface(mv) and mv[0]:
                G.retM[j] = mv
                if len(mv[0]) == 1 and mv[0][0][1] == 1:
                    alias.append((mv[0][0][0], m + j, mv[1]))
            elif len(mv[0]) == 1 and mv[0][0][1] == 1:
                # the returned word is `b·g^k`: `b` is the word `m + j` times `g^-k`
                names.setdefault(mv[0][0][0], (m + j, mv[1]))

    def rename(c):
        bs, off = [], c[1]
        for b, e in c[0]:
            if b < m:
                bs.append((b, e))
            elif b in names:
                bs.append((names[b][0], e))
                off -= e * names[b][1]
            else:
                return None
        return mk(tuple(bs), off)

    post = postR = postV = postP = None
    for st, vs in P.rets:
        cs = {rename(c) for c in st.pts}
        cs.discard(None)
        cs = {c for c in cs if c[0]}
        post = cs if post is None else post & cs
        rs = set()
        for r, _ in st.runs:
            t = tuple(rename(x) if x[0] else x for x in (r[0], r[2], r[3]))
            if None not in t and t[0][0]:
                rs.add((t[0], r[1], t[1], t[2]))
        postR = rs if postR is None else postR & rs
        hv = set()
        pp = {}
        for c, w in st.hv.items():
            rc = rename(c)
            if rc is None or not rc[0]:
                continue
            rw = rename(w) if w[0] else w
            if rw is not None and rw[0]:
                hv.add((rc, rw))
            elif len(w[0]) == 1 and w[0][0][1] == 1 and w[0][0][0] >= m:
                # a pointer to an own buffer: the cells past it written
                offs = frozenset(c2[1] - w[1] for c2 in st.pts if c2[0] == w[0] and 0 <= (c2[1] - w[1]) % ORD < 2 ** 20)
                offs = frozenset(o % ORD for o in offs)
                if offs:
                    pp[rc] = offs
        for c, (offs, _) in st.pf.items():
            rc = rename(c)
            if rc is not None and rc[0]:
                pp[rc] = pp.get(rc, frozenset()) | offs
        postV = hv if postV is None else postV & hv
        postP = pp if postP is None else {c: o & pp[c] for c, o in postP.items() if c in pp and o & pp[c]}
    pre = set(G.pre)
    if 'retM' not in F:
        # a returned word `p·g^k` over a parameter: the cells past `p` also over the returned word's slot
        G.retM = {}
        for p_, slot, k in alias:
            post |= {mk(((slot, 1),), c[1] - k) for c in post if c[0] == ((p_, 1),)}
            postR |= {((((slot, 1),), r[0][1] - k), r[1], r[2], r[3]) for r in postR if r[0][0] == ((p_, 1),)}
    G.post = sorted(c for c in post if c not in pre)[:MAXPTS]
    G.postR = sorted(r for r in postR if r not in set(G.preR))
    G.postV = sorted(postV)[:MAXPTS]
    G.postP = sorted((c, tuple(sorted(o))) for c, o in postP.items())


def infer(key, rules=True):
    """The function's signature and pass, iterated until its signature is stable."""
    G = Sig(len(CORE[key][0]))
    loop = key in IS_LOOP
    if loop:
        G.ctr, G.bnd = loop_params(key)
        if G.bnd is not None:
            G.term = [(base(G.ctr), num(G.bnd[1]) if isinstance(G.bnd, tuple) else base(G.bnd))]
    SIGS[key] = G
    prev = None
    for it in range(12):
        P = Pass(key, G, rules).run()
        if loop:
            loop_finish(P, G)
        else:
            retsig(P, G)
        k = G.key()
        if k == prev:
            break
        prev = k
        G = G.clone()
        SIGS[key] = G
    P.iters = it + 1
    return P


def loop_finish(P, G):
    """At the tail call: the next iteration's preconditions, its term, and the loop's guarantees.

    * a point precondition over the counter `Q·i^S·g^o`: chained if the next iteration's `Q·i^S·g^(o+S)` is written
      by this one; else replaced by the run `Q·g^o`, stride `S`, over `[e(i), e(n))`;
    * guarantees (`retStay`): a cell over the counter written on every path to the tail call, as the run over
      `[e(i), e(n))` (the exit gives `e(i) + 1 = e(n)`, the next iteration the rest); cells over the other
      parameters written on every path, as points.
    """
    i = G.ctr
    if not G.term:
        P.stats['loop-no-bound'] += 1
        return
    end = G.term[0][1]
    newpre, newR = [], list(G.preR)
    tails = [st for st, *_ in P.tails]
    for c in G.pre:
        S = dict(c[0]).get(i)
        if not S:
            newpre.append(c)
            continue
        nxt = shift(c, S)
        if tails and all(nxt in st.pts or (P.find_run(st, nxt, st.runs) or (0, 0, 0, 0, 0))[3:] == (True, True)
                         for st in tails):
            newpre.append(c)
            P.stats['chained'] += 1
        else:
            Q = mk(tuple((b, e) for b, e in c[0] if b != i), c[1])
            r = (Q, S, base(i), end)
            if r not in newR:
                newR.append(r)
    G.pre, G.preR = newpre, newR
    cand = None
    for st in tails or [st for st, _ in P.rets]:
        cs = set(st.pts)
        cand = cs if cand is None else cand & cs
    post, postR = [], []
    for c in sorted(cand or ()):
        if not c[0] or not P.iface(c):
            continue
        S = dict(c[0]).get(i)
        if S:
            Q = mk(tuple((b, e) for b, e in c[0] if b != i), c[1])
            if Q[0]:
                postR.append((Q, S, base(i), end))
        elif c not in G.pre:
            post.append(c)
    G.post, G.postR = post[:MAXPTS], [r for r in postR if r not in G.preR]


# ---- reporting

def run_all(rules=True):
    SIGS.clear()
    out = {}
    t = time.time()
    for k in ORDER:
        out[k] = infer(k, rules)
    return out, time.time() - t


def used_res(P):
    """The residuals the witnesses use (a derived run's, transitively)."""
    out = set()

    def w_(w):
        if not isinstance(w, tuple) or not w:
            return
        k = w[0]
        if k == 'run':
            rw = w[1]
            if isinstance(rw, tuple) and rw[0] == 'derived':
                add(rw[1])
            for i in w[2]:
                add(i)
        elif k == 'sub':
            w_(w[1])
            for i in w[2]:
                add(i)
        elif k == 'pts':
            for x in w[1]:
                w_(x)

    def add(i):
        if i in out:
            return
        out.add(i)
        r = P.res[i]
        if r[0] == 'sub' and len(r) > 3:
            for part in r[2]:
                pass

    for w in P.reads.values():
        w_(w)
    for f, ws in P.calls:
        for _, w in ws or ():
            w_(w)
    for ws in P.ret_wits:
        for _, w in ws:
            w_(w)
    return out


GENERIC = {'hint': 'a hint\'s range (windowsExp, digitsExp, log2Ceil): one lemma per hint kind',
           'selector': 'a match or dispatch selector below its arms (the statement\'s semantics)',
           'rangeCheck': 'a range check (the atom\'s semantics)',
           'merge': 'S residues of stride S are a contiguous run', 'concat': 'two adjacent runs are one',
           'rename': 'a bound rewritten by an assert =='}


def res_family(P, r):
    """A residual's family: `(generic or instance, name)`."""
    tag = r[3] if len(r) > 3 and isinstance(r[3], str) else ('linSub' if r[0] == 'sub' else r[0])
    if tag in GENERIC:
        return 'generic', tag
    return 'instance', {'idx': 'index bound'}.get(tag, tag)


def misses(P):
    """Guarantees and tail preconditions without a witness at the fixpoint."""
    n = 0
    for f, ws in P.calls:
        if f == P.key and ws:
            n += sum(1 for _, w in ws if w[0] == 'miss')
    for ws in P.ret_wits:
        n += sum(1 for _, w in ws if w[0] == 'miss')
    return n


def ok(P):
    return not P.unc and not misses(P)


def closure(res):
    clean = {k for k, P in res.items() if ok(P)}
    closed = set()
    for k in ORDER:
        if k in clean and all(c in closed for c in CALLS[k] if c != k and c in CORE):
            closed.add(k)
    return clean, closed


def report(res):
    tot = collections.Counter()
    for P in res.values():
        tot.update(P.stats)
    clean, closed = closure(res)
    print('functions', len(res), 'every read witnessed', len(clean), 'closed (callees too)', len(closed))
    by = collections.defaultdict(lambda: [0, 0, 0, 0])
    for k, P in res.items():
        s = shape(k)
        by[s][0] += 1
        by[s][1] += k in clean
        by[s][2] += k in clean and not P.res
        by[s][3] += k in closed
    print('  by shape: functions, witnessed, witnessed without residual, closed')
    for s in ('leaf', 'calls', 'calls-loop', 'loop'):
        print(f'    {s:12s}', *by[s])
    unc = collections.Counter(c for P in res.values() for c, _, _ in P.unc)
    ms = sum(misses(P) for P in res.values())
    if ms:
        unc['miss (a guarantee or tail precondition)'] = ms
    print('  uncovered', sum(unc.values()), 'in', len(res) - len(clean), 'functions:', dict(unc.most_common()))
    U = {k: used_res(P) for k, P in res.items()}
    fams = collections.Counter(res_family(res[k], res[k].res[i]) for k, u in U.items() for i in u)
    for g in ('instance', 'generic'):
        ks = [k for k, u in U.items() if any(res_family(res[k], res[k].res[i])[0] == g for i in u)]
        print(f'  residuals used, {g}:', sum(n for (gg, _), n in fams.items() if gg == g), 'in', len(ks), 'functions',
              {f: n for (gg, f), n in fams.most_common() if gg == g})
    print('  stats', dict(sorted(tot.items())))
    fam = collections.Counter()
    for k, P in res.items():
        for c, _, _ in P.unc:
            fam[(c, k.split('__L')[0])] += 1
    print('  uncovered by class and family (top 30):')
    for (c, k), n in fam.most_common(30):
        print(f'    {c:30s} {k:40s} {n}')
    rf = collections.Counter()
    for k, P in res.items():
        for i in U[k]:
            r = P.res[i]
            rf[(res_family(P, r)[1], k.split('__L')[0])] += 1
    print('  residuals by kind and family (top 30):', rf.most_common(30))
    return clean, closed


def set_features(argv):
    if '--lean' in argv:
        F.clear()
    if '--with' in argv:
        F.update(argv[argv.index('--with') + 1].split(','))
    if '--without' in argv:
        F.difference_update(argv[argv.index('--without') + 1].split(','))
    assert F <= set(FEATURES), F - set(FEATURES)


def main():
    set_features(sys.argv)
    print('features:', ','.join(sorted(F)) or '(none: heapOkC\'s format)')
    rules = True
    res, dt = run_all(rules)
    print(f'inferred {len(res)} functions in {dt:.1f} s')
    report(res)
    if '--fn' in sys.argv:
        k = sys.argv[sys.argv.index('--fn') + 1]
        P, G = res[k], SIGS[k]
        cut = lambda x, n=600: (str(x)[:n] + ' ...') if len(str(x)) > n else str(x)
        print(k, shape(k), 'iters', P.iters)
        for f in Sig.FIELDS:
            print(f'  {f}', len(getattr(G, f)), cut(getattr(G, f)))
        print('  retM', G.retM)
        print('  unc', len(P.unc), cut(P.unc, 1500))
        print('  res', len(P.res), cut(P.res))


if __name__ == '__main__':
    main()
