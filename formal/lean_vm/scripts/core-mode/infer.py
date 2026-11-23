"""Heap certificates of the core IR for every function (`formal/notes/core-mode.md`): the
former bytecode walk's inference ported to core names. A measurement and the certificates'
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
import sys, os, collections, contextlib, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.setrecursionlimit(100000)
import coreir
from heapc import stmts  # noqa: E402
if __name__ == '__main__':
    # `rules.py` and `objs.py` import this module by name: one instance, one `SIGS`
    sys.modules.setdefault('infer', sys.modules[__name__])

D = coreir.load()
CORE, STABLE, POWS = D['core'], D['stable'], dict(D['pows'])
POWS[1] = 0
ORD = 2 ** 64 - 1

# The inference's rules beyond `heapOkC`'s format (`CoreMode/Defs.lean`), each switchable to measure what it buys:
FEATURES = {
    'dup': 'a top-level `ite` on `p == k` (`p` a parameter, `k` a constant) followed by atoms and its `ret` takes the '
           'continuation into each branch (`HCert.dups`); a guarantee empty where the zero branch\'s equation holds',
    'postQ': 'a run at the word a callee stores at a cell (its own buffer), guaranteed at return (`postQ`); the '
             'caller reads the cell to name the word',
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
    'chain': 'a run needed covered by up to three pieces in scope from its base (residue runs, points), joined at '
             'symbolic indices (`drv` of `catM`s), its upper bound below their end a residual',
    'armsub': 'an own guarantee over a dispatch\'s selector `x` that each arm `j` writes at `x = g^j`: after the '
              'dispatch, the guarantee (`abx`, a block whose base moves with the arm)',
    'hintrun': 'a heap hint\'s destination also a run',
    'div': 'a division\'s quotient gets the monomial `d / o`',
    'fa': 'a frame run\'s cells written when their values are defined (`frameAddr`)',
    'lts': 'range checks and selectors give exponent facts without a residual',
    'rules': 'residual rules (`rules.py`: `tabIdx`, `linSub`, ...)',
    'obj': 'objects: a read through a pointer (a stream cursor, a word loaded from a record, a returned word) inside '
           'the run of the object it points into, a residual `subR`; ghost slots name a caller\'s object (`objs.py`)',
    'narrow': 'a table precondition its callers write only at a stride: narrowed to that stride, the read a residual '
              '`sub` (`objs.py`)',
    'pfr': 'pointer runs: the words at a run of cells (a table filled in a loop) are pointers whose given cells are '
           'written (`prePR`/`postPR`, `ptrrun.py`)',
    'armx': 'a dispatch arm `j` excluded by a fact `e(x) < j` on its selector: its preconditions not met, its '
            'guarantees not in the meet',
    'retP': 'a dispatch\'s returned pointer whose cells each arm writes (`vpf`, `retP`), and a run with its point '
            'before it (`prepend`)',
    'ptsread': 'a read at a bounded index of a run formed by points (at most 64)',
    'perm': 'a constant cell of an own buffer written at hinted indices: one of those cells, a residual `perm`',
    'ptsrun-long': 'a run met by its points up to 4096 cells (not 64), and long blocks of guaranteed points also '
                   'guaranteed as runs',
    'asm': 'a guarantee assembled at return: a run whose bound carries a constant `g^-k`, restated from `k` cells '
           'earlier, joined with the points before and after it',
    'wrap': 'offsets modulo `g`\'s order (`g^-k` named `g^(ORD - k)` and folded); without it offsets add as naturals, '
            'as `CCell.mul` does',
    'der': 'a run in scope made up for a read (`ptOkD`), and runs shifted back by a constant at a negative offset',
    'jt': 'the jump table\'s cells, which every frame\'s entry has written, as a precondition run (`entryAbs`)',
    'lastres': 'a bound no fact gives stated under the site\'s path, for a residual family to prove',
    'nohs': 'no read of a run\'s bound shifted by one (`fact` at `hi + 1`)',
    'rcpts': 'an index a top-level range check bounds among the points it can be (`CoreMode.rcPts`)',
    'vthi': 'a run up to a bound over bases before one up to a constant',
}
# the features the core route turns on per function (`callc.py`, `callcres.py`): off by default
PER_FN = {'der', 'jt', 'lastres', 'nohs', 'rcpts', 'vthi'}
F = set(FEATURES) - PER_FN
WRAP = [True]
# `arm_blocks` reads the arms' runs too (set by `callc.py` only, so `emitc.py`'s certificates do not move)
ARMRUN = [False]


def callee(name):
    return STABLE.get(name, name)


# ---- monomials `(bases, off)`, bases a sorted tuple of `(value, exponent)`, `off` modulo `g`'s order; an index is
# a monomial read as its word's exponent, `Σ e·e(b) + off`

def mk(bs, off):
    m = collections.defaultdict(int)
    for b, e in bs:
        m[b] += e
    return (tuple(sorted((b, e) for b, e in m.items() if e)), off % ORD if WRAP[0] else off)


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


def negidx(j):
    """An index with a negative constant offset (it wraps below 0 unless its bases make up for it)."""
    return bool(j[0]) and (j[1] >= 2 ** 63 if WRAP[0] else j[1] < 0)


def shift(a, o):
    return (a[0], (a[1] + o) % ORD if WRAP[0] else a[1] + o)


def base(v):
    return (((v, 1),), 0)


def num(k):
    return ((), k % ORD if WRAP[0] else k)


def ioff(a, b):
    """`b - a` when the two differ by a constant (same bases), else `None`."""
    if a[0] != b[0]:
        return None
    if not WRAP[0]:
        return b[1] - a[1]
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
    FIELDS = ('pre', 'post', 'preR', 'postR', 'term', 'postV', 'preP', 'postP', 'ghosts', 'postIn', 'prePR', 'postPR',
              'retEq', 'postQ')

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
        self.ghosts = []     # ghost slot j (value `GB + j`): its anchor (`objs.py`), an inference device only
        self.postIn = []     # (cell pattern run, anchor): the cells' words point into the anchor's object
        self.prePR = []      # (run, offsets): each cell of the run holds a pointer with these cells past it written
        self.postPR = []
        self.retIn = {}      # returned word j -> the anchor of the object it points into
        self.retEq = []      # (x, y): monomials over the parameters and returned words (`m + j`), equal at return
        self.postQ = []      # (cell, (b, S, lo, hi)): the run `w·b·g^(S·j)`, `lo <= j < hi`, `w` the word at the cell
        self.retP = {}       # returned word j -> offsets `o` with `ret_j·g^o` written at return
        self.narrow = {}     # preR index -> stride its callers write it at (`narrow`)
        self.noptr = set()   # a loop's record cells over its counter whose next one the iteration stores: no pointer
                             # facts over them (a caller cannot have written the table), reads through them by `obj`
        self.ctr = None      # a loop's counter and bound parameters
        self.bnd = None

    def key(self):
        return tuple(tuple(getattr(self, f)) for f in self.FIELDS) + (tuple(sorted(self.retP.items())),
                                                                      tuple(sorted(self.retM.items())),
                                                                      tuple(sorted(self.retIn.items())),
                                                                      tuple(sorted(self.narrow.items())))

    def clone(self):
        G = Sig(self.m)
        for f in self.FIELDS:
            setattr(G, f, list(getattr(self, f)))
        G.retM, G.ctr, G.bnd = dict(self.retM), self.ctr, self.bnd
        G.retIn, G.narrow = dict(self.retIn), dict(self.narrow)
        G.retP = dict(self.retP)
        G.noptr = set(self.noptr)
        return G

    def size(self):
        return sum(len(getattr(self, f)) for f in self.FIELDS) + len(self.retM)


SIGS = {}
PFR = ('__pfr__',)   # the key of a selector arm's pointer runs among its kept heap words (`cond`)
PF = ('__pf__',)     # and of its pointer facts
GB = 1 << 20   # ghost slot j is the value `GB + j`


# ---- the pass

class St:
    __slots__ = ('env', 'pts', 'hv', 'pf', 'src', 'runs', 'lts', 'D', 'alias', 'cond', 'pfr', 'vpf', 'dq')

    def __init__(self):
        self.env, self.pts, self.hv, self.pf, self.src = {}, {}, {}, {}, {}
        self.runs, self.lts, self.D, self.alias, self.cond = [], set(), set(), {}, {}
        self.pfr = []
        self.vpf = {}        # value -> offsets `o` with `v·g^o` written (`retP`: a dispatch's returned pointer)
        self.dq = ()         # (cell, (b, S, lo, hi)): a callee's `postQ`, the run at the word the cell holds

    def copy(self):
        s = St()
        s.env, s.pts, s.hv, s.pf, s.src = dict(self.env), dict(self.pts), dict(self.hv), dict(self.pf), dict(self.src)
        s.pfr = list(self.pfr)
        s.vpf = dict(self.vpf)
        s.dq = self.dq
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
        s.pfr = [x for x in s.pfr if x in t.pfr]
        s.vpf = {v: (o & t.vpf[v][0], w) for v, (o, w) in s.vpf.items() if v in t.vpf and o & t.vpf[v][0]}
    if sel is not None:
        x, js = sel
        for j, t in live:
            pts = {c: w for c, w in t.pts.items() if c not in s.pts}
            runs = [(r, w) for r, w in t.runs if (r, w) not in s.runs]
            hv = {c: w for c, w in t.hv.items() if c not in s.hv}
            pfr = [x for x in t.pfr if x not in s.pfr]
            pf = {c: f for c, f in t.pf.items() if c not in s.pf}
            if pts or runs or hv or pfr or pf:
                old = s.cond.get((x, js[j]), ({}, [], {}))
                hv2 = {**old[2], **hv}
                if pfr:
                    hv2[PFR] = old[2].get(PFR, []) + pfr
                if pf:
                    hv2[PF] = {**old[2].get(PF, {}), **pf}
                s.cond[(x, js[j])] = ({**old[0], **pts}, old[1] + runs, hv2)
    return s


# a certificate split at a selector (`CoreMode.heapOkC`, `HCert.arms`): the function whose pass reads its body at arm `r`
# of the selector `V.n x`, `(x, r)`
ARM = {}


def sel_body(ss, x, r):
    """`CoreMode.selL`: a block at arm `r` of the selector `x`, each `match` on it its arm `r`'s block inline, each
    `dispatch` on it the call of its callee `r`, where there is one."""
    out = []
    for s in ss:
        if s[0] == 'match':
            arms = [sel_body(a, x, r) for a in s[2]]
            if s[1] == x and r < len(arms):
                out.extend(arms[r])
            else:
                out.append(('match', s[1], arms))
        elif s[0] == 'ite':
            out.append(('ite', s[1], sel_body(s[2], x, r), sel_body(s[3], x, r)))
        elif s[0] == 'dispatch' and s[1] == x and r < len(s[2]):
            out.append(('call', s[2][r], s[3], s[4]))
        else:
            out.append(s)
    return out


@contextlib.contextmanager
def at_arm(key, sel):
    """Passes over `key` read its body at the arm `sel = (x, r)` (`ARM`), none if `sel` is `None`."""
    if sel is not None:
        ARM[key] = sel
    try:
        yield
    finally:
        ARM.pop(key, None)


def arm_body(key):
    """The body a pass reads: the function's, at its arm (`ARM`)."""
    body = CORE[key][1]
    return sel_body(body, *ARM[key]) if key in ARM else body


class Pass:
    def __init__(self, key, sig, rules=True):
        self.key = key
        self.params, self.body = CORE[key][0], arm_body(key)
        self.dups = dup_guards(key) if 'dup' in F else []
        if self.dups:
            self.body = dup_body(self.dups, self.body)
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
        self.retpaths = []               # the branch path at each `ret`
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
        self.eqpath = []                 # the branch path of each equation
        self.allocsz = {}                # an allocation's constant size in cells
        self.defs = {}
        self.ginst = None                # the ghost instantiation of the call being met
        self.gforce = {}                 # callee -> its ghost instantiation in every arm of the dispatch being met
        self.vpoffs = {}                 # a dispatch's returned value -> the offsets its arms write past it (`retP`)
        self.retsite = {}                # returned value -> (callee, args, j, ginst)
        self.contents = []               # (cell pattern run, object): words stored by callees
        self.objres = {}                 # residual merging (`objs.py`)
        self.stores = []                 # (cell root, offset, stride, object of the stored word) (`objs.py`)
        self.path = []                   # the branch conditions in scope: ('ite', c, zero?) or ('arm', x, j)
        self.rpath = collections.defaultdict(list)   # residual -> the paths it was asked under
        self.sites = []                  # (callee, args, ghost instantiation, path), every call met (`emitc.py`)
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
            i = self.res.index(r)
            self.rpath[i].append(tuple(self.path))
            return i
        if r[0] == 'lt' and r[1][1] < 2 ** 40:
            # merged only under one branch path: an arm's bound need not hold in another arm
            key = (r[1][0], r[2], r[3:], tuple(self.path))
            i = self.ltkey.get(key)
            if i is not None:
                if self.res[i][1][1] < r[1][1]:
                    self.res[i] = r
                self.rpath[i].append(tuple(self.path))
                return i
            self.ltkey[key] = len(self.res)
        self.rpath[len(self.res)].append(tuple(self.path))
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
    def bases_in(self, cb, r):
        """The cells over the bases `cb` can be cells of the run `r`: `idx_in`'s test on the bases alone."""
        Q, S = r[0], r[1]
        rest = dict(cb)
        for b, e in Q[0]:
            if rest.get(b, 0) < e:
                return False
            rest[b] -= e
        return not any(e % S for e in rest.values())

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
        do = (c[1] - Q[1]) % ORD if WRAP[0] else c[1] - Q[1]
        if not WRAP[0] and do < 0:
            return None
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
            # a bound over the same bases is decided: one that fails is false, not a residual
            dl, dh = ioff(r[2], j), ioff(j, r[3])
            if not (not okl and dl is not None) and not (not okh and dh is not None) and (
                    best is None or negidx(best[2]) and not negidx(j) or
                    # an index over bases is no residual's below a constant bound when a run up to a bound over
                    # bases holds it
                    'vthi' in F and not best[4] and not best[0][3][0] and best[2][0] and r[3][0] and
                    not negidx(j)):
                # a run the cell has a negative constant offset in is a last resort: its index wraps below 0
                best = (r, rw, j, okl, okh)
        return best

    def cover(self, st, c, site, allow_pre=True, conds=None):
        """A witness that the cell `c` is written, or `None`."""
        w = st.pts.get(c)
        if w is not None:
            self.stats['w-ev'] += 1
            return w
        if st.vpf and len(c[0]) == 1 and c[0][0][1] == 1 and c[0][0][0] in st.vpf and c[1] in st.vpf[c[0][0][0]][0]:
            self.stats['w-vpf'] += 1
            return ('vpf', st.vpf[c[0][0][0]][1], c[1])
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
        if 'retP' in F and c[0] and c[1] < 2 ** 20 and getattr(self, 'in_pre', 0) < 2:
            w = self.prepend(st, c, site, allow_pre, conds)
            if w is not None:
                return w
        if 'ptsread' in F and c[0] and c[1] < 2 ** 20:
            w = self.pts_read(st, c, conds)
            if w is not None:
                return w
        # through a pointer loaded from a cell with a pointer fact
        if 'ptr' in F and len(c[0]) == 1 and c[0][0][1] == 1:
            d = c[0][0][0]
            s = st.src.get(d)
            if s is not None and s[0] in self.sig.noptr:
                s = None
            if s is not None:
                f = st.pf.get(s[0])
                if f is not None and c[1] in f[0]:
                    self.stats['w-pf'] += 1
                    return ('pf', f[1], c[1])
                if 'pfr' in F and c[1] < 2 ** 20:
                    import ptrrun
                    w = ptrrun.read(self, st, s[0], (c[1],), conds)
                    if w is not None:
                        return w
                if allow_pre and not self.at_tail and self.iface(s[0]) and c[1] < 2 ** 20 and (
                        'pfr' in F or not (self.loop and any(b == self.sig.ctr for b, _ in s[0][0]))):
                    return self.add_preP(s[0], c[1])
        def pre_point(arm_only=False):
            if allow_pre and not self.at_tail and self.iface(c) and c[0] and self.subst and 'cond' in F:
                # a constant cell `Q·g^k` read in arm `j` of a match on a parameter `x` with `k < j`: inside the run
                # `⟨Q, 1, 0, x⟩` (by the arm, `e(x) = j`), a precondition every caller can meet, where the cell alone
                # would be one only the callers taking that arm write
                if len(c[0]) == 1 and c[0][0][1] == 1 and c[1] < 2 ** 20:
                    for b, j in self.subst.items():
                        if b < self.m and 0 <= c[1] < j and not (self.loop and b == self.sig.ctr):
                            r = (mk(c[0], 0), 1, num(0), base(b))
                            if r not in self.sig.preR:
                                self.sig.preR.append(r)
                            self.stats['w-arm-run'] += 1
                            return ('run', ('preR', self.sig.preR.index(r)), [])
            if arm_only:
                return None
            if allow_pre and not self.at_tail and self.iface(c) and (c[0] or self.key == 'main' and 0 <= c[1] < 2 ** 20):
                # (an absolute cell only for the root: its preconditions are the public input's cells, `preSet_const`)
                if self.loop and any(b == self.sig.ctr for b, _ in c[0]):
                    if c not in self.sig.pre:
                        self.sig.pre.append(c)
                    self.stats['w-pre-ctr'] += 1
                    return ('pre', self.sig.pre.index(c))
                if c not in self.sig.pre:
                    self.sig.pre.append(c)
                self.stats['w-pre'] += 1
                return ('pre', self.sig.pre.index(c))
            return None

        # under a selector's arm, a point precondition binds every caller to what only that arm reads: the object's
        # run with a residual (asked under the arm's path) goes first
        late = 'obj' in F and any(p[0] == 'arm' for p in self.path) and len(c[0]) == 1 and c[0][0][1] == 1 \
            and c[0][0][0] < self.m and c[1] < 2 ** 20 and c not in self.sig.pre
        w = pre_point(arm_only=late)
        if w is not None:
            return w
        if best is not None and 'idx' in F:
            r, rw, j, okl, okh = best
            if okl and not okh:
                # the index one past the run, where a point is written: the run and the point (`concat`)
                pt, u = mmul(r[0], mpow(r[3], r[1])), []
                if pt in st.pts and self.lt(st, j, shift(r[3], 1), u) and self.le(st, r[2], j, u):
                    R2 = (r[0], r[1], r[2], shift(r[3], 1))
                    k = self.addres(('sub', R2, (r, pt), 'concat'))
                    st.runs.append((R2, ('derived', k)))
                    self.stats['w-run-pt'] += 1
                    return ('run', ('derived', k), u)
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
        if 'obj' in F or 'narrow' in F:
            import objs
            w = objs.read(self, st, c, site, conds)
            if w is not None:
                return w
        if late:
            return pre_point()
        if 'perm' in F:
            return self.perm_read(st, c, conds)
        return None

    def pts_read(self, st, c, conds):
        """A read `Q·j^S` at an index with a known bound `e(j) < n`, the points `Q·g^(S·i)`, `i < n`, written: the run
        they form (at most 64 points), the read inside it."""
        import math
        pts = dict(st.pts)
        for cd in conds or ():
            for x, w in cd[0].items():
                pts.setdefault(x, w)
        for b, e in c[0]:
            if e != 1:
                continue
            Q = (((b, 1),), 0)
            rest = [y for x, y in c[0] if x != b]
            if not rest:
                continue
            S = 0
            for y in rest:
                S = math.gcd(S, y)
            j = self.idx_in(c, (Q, S, num(0), num(0)))
            if j is None or negidx(j):
                continue
            n = 0
            while n < 64 and shift(Q, S * n) in pts:
                n += 1
            u = []
            if n == 0 or not self.lt(st, j, num(n), u):
                continue
            ws = tuple(pts[shift(Q, S * i)] for i in range(n))
            if any(w[0] == 'run' and w[2] for w in ws):
                continue
            self.stats['w-ptsread'] += 1
            return ('run', ('ptsR', ws), u)
        return None

    def perm_read(self, st, c, conds):
        """A constant cell of an own buffer whose cells were written at hinted indices (`b·x_r`, a hinted order): the
        cell is one of them, a residual (`perm`: the hinted indices are a permutation of the read ones)."""
        if c[1] >= 2 ** 20 or not all(v >= self.m and e == 1 for v, e in c[0]) or len(c[0]) > 2:
            return None
        cand = set(st.pts)
        for cd in conds or ():
            cand |= set(cd[0])
        if len(c[0]) == 1:
            # a constant cell: among the cells written at a hinted index
            b = c[0][0][0]
            cand = sorted(x for x in cand if len(x[0]) == 2 and (b, 1) in x[0] and all(y == 1 for _, y in x[0]) and
                          x[1] < 2 ** 20 and all(v >= self.m for v, _ in x[0]))
        else:
            # a cell at a hinted index: among the buffer's constant cells (the index pinned elsewhere)
            bs = [v for v, _ in c[0] if self.defkind.get(v) == 'alloc']
            if len(bs) != 1:
                return None
            cand = sorted(x for x in cand if x[0] == ((bs[0], 1),) and x[1] < 2 ** 20)
        if not cand:
            return None
        k = self.addres(('subP', c, tuple(cand), 'perm'))
        self.stats['w-perm'] += 1
        return ('perm', [st.pts.get(x) for x in cand], [k])

    def prepend(self, st, c, site, allow_pre, conds):
        """A run `⟨Q·g^S, S, 0, h⟩` and its point `Q` before it are `⟨Q, S, 0, h·g⟩` (`concat`): the cell is in that run
        at an index `j` with `e(j) < e(h) + 1` decided (a table's first row a precondition, the rest a loop's)."""
        for r, rw in reversed(st.runs):
            Q1, S, lo, hi = r
            if lo != num(0) or not hi[0] or Q1[1] < S or Q1[1] >= 2 ** 40:
                continue
            Q = shift(Q1, -S)
            R2 = (Q, S, num(0), shift(hi, 1))
            j = self.idx_in(c, R2)
            if j is None or negidx(j) or ioff(j, shift(hi, 1)) is None or ioff(j, shift(hi, 1)) <= 0:
                continue
            # the point itself possibly before another run (one level: a chain's record after two loops)
            self.in_pre = getattr(self, 'in_pre', 0) + 1
            try:
                w = self.cover(st, Q, site, allow_pre=allow_pre, conds=conds)
            finally:
                self.in_pre -= 1
            if w is None or w[0] == 'run' and w[2]:
                continue
            k = self.addres(('sub', R2, (r, Q), 'concat'))
            st.runs.append((R2, ('derived', k)))
            self.stats['w-prepend'] += 1
            return ('run', ('derived', k), [])
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
                        q = mdiv(self.mono(st, d), self.mono(st, o)) if 'div' in F else None
                        self.define(st, u, q, 'mul')
                        if q is None and 'div' in F:
                            # no monomial for the quotient: the equation `u·o = d` instead (`retEq`, `rename`)
                            self.eqs.append((mmul(self.mono(st, u), self.mono(st, o)), self.mono(st, d)))
                            self.eqpath.append(tuple(self.path))
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
                self.eqpath.append(tuple(self.path))
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
                if 'obj' in F:
                    import objs
                    objs.on_store(self, st, c, d)
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
                for c2, r in st.dq:
                    if c2 == c:
                        self.pushR(st, (mmul(self.mono(st, d), r[0]), r[1], r[2], r[3]))
                if 'hv' in F:
                    st.hv.setdefault(c, self.mono(st, d))
            self.push(st, c)
        elif k == 'assertNe':
            self.define(st, a[3], None, 'assertNe')
        elif k == 'rangeCheck':
            x, y, t1, t2, kk = a[1:]
            if y not in st.D:
                self.define(st, y, None, 'rangeCheck')
            mk_ = self.mono(st, kk)
            # over value numbers when the bound is a constant (the checked word itself, whatever its monomial)
            ci = (('val', x), ('num', mk_[1] + 1)) if mk_ is not None and not mk_[0] and 0 <= mk_[1] < 2 ** 40 else None
            self.fact(st, self.mono(st, x), shift(mk_, 1), 'rangeCheck', cidx=ci)
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
            if h[0] == 'alloc' and isinstance(h[2], int):
                self.allocsz[h[1]] = h[2]
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
            if b >= GB:
                mb = self.ginst[b - GB] if self.ginst is not None and b - GB < len(self.ginst) else None
                if mb is None:
                    return None
            elif b < len(args):
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
            false = (not okl and ioff(R[2], jl) is not None) or (not okh and ioff(jh, R[3]) is not None)
            if not false and (best is None or (okl or okh) and not (best[2] or best[3])):
                best = (R, rw, okl, okh, jl, jh)
        if self.key in CTR_PRE and lo == num(0) and hi[0]:
            # a run in scope with points before and after it: `Q·g^(S·i)`, `i < t`, then `⟨Q·g^(S·t), S, 0, h⟩`, then
            # its next `u` points, `hi = h·g^(t+u)` (`catM g^t (h·g^u)`, `catM h g^u`)
            for R, rw in reversed(st.runs):
                t, rem = divmod(R[0][1] - Q[1], S) if S else (0, 1)
                if R[1] != S or R[2] != num(0) or R[0][0] != Q[0] or t < 0 or rem or R[3][0] != hi[0]:
                    continue
                u = hi[1] - R[3][1] - t
                end = mmul(R[0], mpow(R[3], S))
                if u >= 0 and t + u > 0 and all(shift(Q, S * i) in st.pts for i in range(t)) and \
                        all(shift(end, S * j) in st.pts for j in range(u)):
                    self.stats['wr-run-around'] += 1
                    return ('sub', ('run', rw, []), [])
        if 'chain' in F and lo == num(0) and S and hi[0]:
            # the run made up of the pieces in scope from its base (`reach`), reaching past the upper bound:
            # `e(hi) < e(k·g)`, a residual (`drv` of `catM`s)
            k = reach(Q, S, [R for R, _ in st.runs], st.pts)
            if k is not None and k != hi:
                kr = self.addres(('lt', hi, shift(k, 1), 'chain'))
                self.stats['wr-chain'] += 1
                return ('sub', ('run', 0, []), [kr])
        if self.key in CTR_CALLERS and lo == num(0) and S and hi[0]:
            # residue runs `⟨Q·g^(S·d), S·K, 0, h⟩`, `d < K`, reaching past the upper bound: `e(hi) < e(h^K·g)`, a residual
            for K in (2, 4):
                hs = {R[3] for R, _ in st.runs if R[1] == S * K and R[2] == num(0) and R[0] == shift(Q, 0)}
                for h in sorted(hs, key=lambda h: -h[1]):
                    if h[0] and all(any(R == (shift(Q, S * d), S * K, num(0), h) for R, _ in st.runs) for d in range(K)):
                        k = self.addres(('lt', hi, shift(mpow(h, K), 1), 'mrg-le'))
                        self.stats['wr-mrg-le'] += 1
                        return ('sub', ('run', 0, []), [k])
        if n is not None and n <= (MAXPTS if 'ptsrun-long' in F else 64) and not lo[0] and 'ptsrun' in F:
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
                self.loop and any(b == self.sig.ctr for b, _ in Q[0]) and self.key not in CTR_PRE):
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
            w = rules.run(self, st, r, site, conds)
            if w is not None:
                return w
        if 'obj' in F:
            import objs
            return objs.run(self, st, r, site, conds)
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
            return hi[1] <= hi2[1] < 2 ** 62
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
        if 'pfr' in F:
            import ptrrun
            w = ptrrun.read(self, st, c, tuple(offs), conds)
            if w is not None:
                return w
        if not self.at_tail and self.iface(c) and ('pfr' in F or not (self.loop and any(b == self.sig.ctr for b, _ in c[0]))):
            for o in offs:
                w = self.add_preP(c, o)
            return ('preP', w[1])
        return None

    def argword(self, st, args, a):
        """The word at cell `d` past argument `q - 2`'s word: the value a top-level `load` names there
        (`CoreMode.hpValS`), as its monomial."""
        import callc
        n = callc.hp_val_s(self.body, args[a[1] - 2], a[2])
        return self.mono(st, n) if n is not None else None

    def call(self, st, f, args, rets, cond=None, conditional=False, conds=None, record=True):
        G = SIGS.get(f)
        ws = []
        site = ('call', f)
        self.ginst = None
        if G is not None and G.ghosts and all(a[0] in ('hp1', 'hpw') for a in G.ghosts):
            # a callee's caller cells, the caller's own parameters' words; the words at its arguments' cells, the values
            # a top-level `load` names (`CoreMode.hpArgOk`)
            self.ginst = [mk(((a[1] - 2, 1),), 0) if a[0] == 'hp1' else self.argword(st, args, a) for a in G.ghosts]
            if None in self.ginst:
                self.ginst = None
        elif G is not None and G.ghosts and 'obj' in F:
            import objs
            self.ginst = self.gforce.get(f) if f in self.gforce else objs.inst(self, st, G, args, conds)
        ginst = self.ginst
        self.sites.append((f, tuple(args), ginst, tuple(self.path)))
        if G is not None:
            for c in G.pre:
                t = self.tr(st, c, args, None)
                w = self.cover(st, t, site, conds=conds) if t is not None else None
                ws.append(('pre', w if w is not None else self.unc_read(st, t, site)))
            for r in G.preR:
                t = self.trR(st, r, args, None)
                w = self.cover_run(st, t, site, conds) if t is not None else None
                if w is None and t is not None and 'narrow' in F:
                    import objs
                    objs.narrow_site(self, st, f, r, t, conds)
                ws.append(('preR', w if w is not None else self.unc_read(st, t[0] if t else None, site, 'run:')))
            for c, offs in G.preP:
                t = self.tr(st, c, args, None)
                w = self.cover_ptr(st, t, offs, site, conds) if t is not None else None
                ws.append(('preP', w if w is not None else self.unc_read(st, t, site, 'ptr:')))
            if 'pfr' in F:
                import ptrrun
                for r, offs in G.prePR:
                    t = self.trR(st, r, args, None)
                    w = ptrrun.cover(self, st, t, offs, conds) if t is not None else None
                    ws.append(('prePR', w if w is not None else self.unc_read(st, t[0] if t else None, site, 'ptrrun:')))
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
        if 'obj' in F:
            import objs
            objs.after_call(self, st, f, G, args, rets, ginst)
        for j, offs in (G.retP.items() if 'retP' in F else ()):
            if rets and j < len(rets):
                st.vpf[rets[j]] = (offs, ('ev', self.n))
                self.n += 1
        if not conditional and 'div' in F:
            for x, y in G.retEq:
                tx, ty = self.tr(st, x, args, rets), self.tr(st, y, args, rets)
                if tx is not None and ty is not None and tx != ty:
                    self.eqs.append((tx, ty))
                    self.eqpath.append(tuple(self.path))
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
                if not (f in CTR_PRE and cond is not None and self.kept_if_not_entered(st, cond, t)):
                    continue
            self.pushR(st, t)
        for c, r in (G.postQ if 'postQ' in F and not conditional else ()):
            tc, t = self.tr(st, c, args, rets), self.trR(st, r, args, rets)
            if tc is not None and t is not None:
                st.dq += ((tc, t),)
        for r, offs in (G.postPR if 'pfr' in F else ()):
            t = self.trR(st, r, args, rets)
            if t is None or conditional and not ('callIfR' in F and cond is not None and
                                                 self.cond_is(st, cond, t[2], t[3])):
                continue
            st.pfr.append((t, frozenset(offs), ('evR', self.n)))
            self.n += 1

    def kept_if_not_entered(self, st, c, t):
        """A `callIf` guarantee written where the call is not entered: `c = a + b`, the run with `a` (one base)
        replaced by `b` covered in scope (`keep`)."""
        d = self.adds.get(c)
        if d is None:
            return False
        ms = [self.mono(st, d[0]), self.mono(st, d[1])]
        for a, b in (ms, ms[::-1]):
            if a is None or b is None or len(a[0]) != 1 or a[0][0][1] != 1 or a[1]:
                continue
            x = a[0][0][0]

            def sub(m):
                e = dict(m[0]).get(x, 0)
                return mmul(mk(tuple((k, f) for k, f in m[0] if k != x), m[1]), mpow(b, e))
            r = (sub(t[0]), t[1], sub(t[2]), sub(t[3]))
            old = self.at_tail
            self.at_tail = True
            try:
                w = self.cover_run(st, r, ('keep',))
            finally:
                self.at_tail = old
            if w is not None:
                self.stats['kept'] += 1
                return True
        return False

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
                outs = []
                for z, b in ((True, s[2]), (False, s[3])):
                    self.path.append(('ite', s[1], z))
                    outs.append(self.block(st.copy(), b))
                    self.path.pop()
                st = self.join(st, outs)
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
                            t.hv.update({c: w for c, w in hv.items() if c not in t.hv and c not in (PFR, PF)})
                            t.pfr += hv.get(PFR, [])
                            t.pf.update({c: f for c, f in hv.get(PF, {}).items() if c not in t.pf})
                        self.subst = self.assume(st, s[1], j)
                    self.path.append(('arm', s[1], j))
                    outs.append(self.block(t, arm))
                    self.path.pop()
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
                    self.path.append(('ite', s[1], False))
                    self.calls.append((f, self.tail_wits(st, s[3])))
                    self.sites.append((f, tuple(s[3]), self.ginst, tuple(self.path)))
                    self.path.pop()
                else:
                    self.path.append(('ite', s[1], False))
                    self.call(st, f, s[3], [], cond=s[1], conditional=True)
                    self.path.pop()
            elif k == 'dispatch':
                self.dispatch(st, s)
            elif k == 'ret':
                if 'rules' in F:
                    import rules
                    rules.derive(self, st)
                if self.retvals is None:
                    self.retvals = s[1]
                self.rets.append((st, s[1]))
                self.retpaths.append(tuple(self.path))
                self.ret_wits.append(self.ret_wit(st, s[1]))
                return None
        return st

    def tail_wits(self, st, args):
        """The loop's tail call: its own `pre` and `preR` at the next iteration's words (chained: written by this
        one; the own precondition; the own run by the shifted-lower rule). Misses are the next round's runs."""
        G, ws = self.sig, []
        self.at_tail = True
        self.ginst = None
        if G.ghosts and 'obj' in F:
            import objs
            self.ginst = objs.inst(self, st, G, args, None, tail=True)
        elif G.ghosts and all(a[0] in ('link', 'fp') for a in G.ghosts):
            # a loop's caller's cells and frame (`CoreMode.loopGl`): its tail call names its own ghosts (`tailG`)
            self.ginst = [mk(((GB + j, 1),), 0) for j in range(len(G.ghosts))]
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
        if 'pfr' in F:
            import ptrrun
            for r, offs in G.prePR:
                t = self.trR(st, r, args, None)
                w = ptrrun.cover(self, st, t, offs, None) if t is not None else None
                ws.append(('prePR', w if w is not None else ('miss', t)))
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
                # an assembled guarantee (`assemble`): its parts are in scope, it is not a run there
                asm = 'asm' in F and t is not None and t in assemble(self, sts[0])
                w = ('asm',) if asm else self.cover_run(sts[0], t, ('ret',)) if t is not None else None
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
        live = []
        self.gforce = self.common_ghosts(st, x, fs, args)
        for j, f in enumerate(fs):
            self.n, self.nr = n0, nr0
            if 'armx' in F:
                u = []
                if self.lt(st, xm, num(j), u):
                    ws.append(('armx', ('armx', u)))
                    self.stats['armx'] += 1
                    continue
            live.append(j)
            t = st.copy()
            cd = self.conds_of(st, x, j) if 'cond' in F else []
            self.armconds = cd
            old = self.subst
            if 'cond' in F:
                self.subst = self.assume(st, x, j)
            self.path.append(('arm', x, j))
            self.call(t, f, args, rets, conds=cd, record=False)
            self.path.pop()
            ws.extend(self.lastws)
            self.subst = old
            self.armconds = None
            outs.append(t)
        self.gforce = {}
        self.calls.append((tuple(fs), ws))
        m = meet(outs, (xm, live) if 'cond' in F else None)
        # `heapOkC`'s numbering: the arms' common guarantees, in the first arm's order, one serial each
        self.n, self.nr = n0, nr0
        pts, runs = dict(st.pts), list(st.runs)
        sigs = [SIGS.get(fs[j]) for j in live]
        if sigs and all(sigs):
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
        vp = self.ret_ptrs(outs, rets) if 'retP' in F and m is not None else {}
        for a in St.__slots__:
            setattr(st, a, getattr(m, a))
        for v, offs in vp.items():
            st.vpf[v] = (offs, ('ev', self.n))
            self.n += 1
        if 'join' not in F or 'cond' not in F:
            st.pts, st.runs = pts, runs
        else:
            st.pts.update({c: w for c, w in pts.items() if c in st.pts})
            st.runs = runs + [x for x in st.runs if x[0] not in {r for r, _ in runs}]
        self.fact(st, xm, num(len(fs)), 'selector', cidx=(('val', x), ('num', len(fs))))
        if 'armblock' in F:
            self.arm_blocks(st, xm, outs, (x, tuple(s[2]), tuple(args)))

    def common_ghosts(self, st, x, fs, args):
        """A callee in several arms of a dispatch has one ghost instantiation (`HCert.gargs` is keyed by callee and
        arguments): each arm's, and where they differ, the one whose ghost runs are the shortest (the same bases,
        constant bounds), which every such arm's scope holds; none if they differ otherwise."""
        out = {}
        if 'obj' not in F:
            return out
        import objs
        for f in set(fs):
            js = [j for j, g in enumerate(fs) if g == f]
            G = SIGS.get(f)
            if len(js) < 2 or G is None or not G.ghosts:
                continue
            cands = []
            for j in js:
                if 'armx' in F and self.lt(st, self.mono(st, x), num(j), []):
                    continue
                old, olda = self.subst, self.armconds
                cd = self.conds_of(st, x, j) if 'cond' in F else []
                self.armconds = cd
                if 'cond' in F:
                    self.subst = self.assume(st, x, j)
                self.path.append(('arm', x, j))
                cands.append(objs.inst(self, st.copy(), G, args, cd))
                self.path.pop()
                self.subst, self.armconds = old, olda
            if len({tuple(c) for c in cands}) < 2:
                continue
            his = {i for i, a in enumerate(G.ghosts) if a[0] == 'hi'}
            if any(None in c for c in cands) or any(len({c[i] for c in cands}) > 1 for i in range(len(G.ghosts))
                                                    if i not in his) or \
                    any(c[i][0] for c in cands for i in his):
                self.stats['ghost-arms-differ'] += 1
                continue
            out[f] = min(cands, key=lambda c: tuple(c[i][1] for i in sorted(his)))
            self.stats['ghost-arms-min'] += 1
        return out

    def ret_ptrs(self, outs, rets):
        """A dispatch's returned word that each arm names (`retM`) as a pointer with cells written past it in that arm
        (its guarantees, or the caller's cells): those offsets, written past the returned word whichever arm ran."""
        out = {}
        for v in rets or ():
            common, ws = None, []
            for t in outs:
                mv = t.env.get(v) if t is not None else None
                if mv is None or not mv[0]:
                    return out
                offs = {}
                for o in range(0, 256):
                    c = shift(mv, o)
                    w = t.pts.get(c)
                    if w is None:
                        u = []
                        b = self.find_run(t, c, t.runs, u)
                        w = ('run', b[1], u) if b is not None and b[3] and b[4] and not u else None
                    if w is None and o < 64:
                        w = self.prepend(t, c, ('retP',), True, None)
                    if w is not None:
                        offs[o] = w
                    elif offs:
                        break
                ws.append(offs)
                common = set(offs) if common is None else common & set(offs)
                if not common:
                    break
            if common:
                out[v] = frozenset(common)
                self.vpoffs[v] = tuple(sorted(common))
                # the arms' witnesses of the cells, for the check (`calls`)
                self.calls.append((('retP', v), [('retP', w[o]) for w in ws for o in sorted(common)]))
        return out

    def arm_blocks(self, st, xm, outs, key=None):
        """Arms of a selector `x` each writing a growing block `Q·g^(c..j+c)`, `c <= 0`: the run `Q·[0, e(x) + d)`
        (`armBlocks`), `d` the least block's excess over its arm index."""
        if len(outs) < 3 or any(t is None for t in outs) or not xm[0]:
            return
        by = collections.defaultdict(set)
        for c in outs[-1].pts:
            if c[1] < 2 ** 20 and c[0] and c not in st.pts:
                by[c[0]].add(c[1])
        if ARMRUN[0]:
            # the arms' blocks also as runs at constant bounds (the callees' guarantees translated from mode
            # signatures, `callc.py`)
            for r, _ in outs[-1].runs:
                if r[1] == 1 and r[0][0] and r[0][1] == 0 and r[0] not in st.pts:
                    by[r[0][0]].add(0)

        def has(t, c, rs):
            if c in t.pts:
                return True
            if not ARMRUN[0]:
                return False
            u = []
            b = self.find_run(t, c, rs, u)
            return b is not None and b[3] and b[4] and not u
        for Q, offs in by.items():
            ns = []
            for j, t in enumerate(outs):
                # the runs whose cells can be over the bases `Q` (`idx_in`'s first test), once per arm
                rs = [x for x in t.runs if self.bases_in(Q, x[0])] if ARMRUN[0] else []
                n = 0
                while n < 2 ** 12 and has(t, (Q, n), rs):
                    n += 1
                ns.append(n)
            K = (ns[-1] - ns[0]) // (len(outs) - 1)
            if K < 1:
                continue
            d = min(n - K * j for j, n in enumerate(ns))
            if d < 0 or K * (len(outs) - 1) + d < 2:
                continue
            r = ((Q, 0), 1, num(0), shift(mpow(xm, K), d))
            if d % K == 0 and key is not None:
                # the dispatch's blocks, for the check's `ab` (`emitc.py`): `K` residue runs of stride `K`
                self.__dict__.setdefault('armblk', {}).setdefault(key, []).append(((Q, 0), K, d))
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
        for k, (r, offs) in enumerate(G.prePR):
            st.pfr.append((r, frozenset(offs), ('prePR', k)))
        for k, (c, offs) in enumerate(G.preP):
            st.pf[c] = (frozenset(offs), ('preP', k))
        self.block(st, self.body)
        return self


def reach(Q, S, runs, pts, mul=mmul, pw=mpow, sh=shift):
    """The bound `k` of the run `⟨Q, S, 0, k⟩` made up of at most three pieces in scope from `Q` (the shape `runOk`'s
    `catM`s split): `K` residue runs `⟨Q'·g^(S·d), S·K, 0, h⟩`, `d < K` (`h^K` more), or the points `Q'·g^(S·i)`, `i < m`
    (`g^m` more, the last piece); `None` if no piece has a bound over values."""
    k, Q1 = num(0), Q
    for _ in range(3):
        step = None
        for R in runs:
            if R[0][0] != Q1[0] or R[0][1] != Q1[1] or R[2] != num(0) or not R[3][0] or R[1] <= S or R[1] % S:
                continue
            K = R[1] // S
            if all((sh(Q1, S * d), R[1], num(0), R[3]) in runs for d in range(K)):
                step = pw(R[3], K)
                break
        if step is None:
            m = 0
            while m < 64 and sh(Q1, S * m) in pts:
                m += 1
            if m:
                k = sh(k, m)
            break
        k = mul(k, step)
        Q1 = mul(Q, pw(k, S))
    return k if k[0] else None


# Loops whose run preconditions may be over the counter: a table the loop fills itself, row by row, each iteration
# reading the row the previous one wrote (their rule files' `CTR_PRE`). The tail meets the next row.
import fnrules  # noqa: E402
CTR_PRE = fnrules.table('CTR_PRE') or set()
CTR_CALLERS = {f for k in CTR_PRE for f in CALLERS[k] if f not in CTR_PRE}


DUPCALL = [False]


def dup_guards(key):
    """The guards of the top-level `ite`s whose continuation goes into each branch (`HCert.dups`): a function (not a
    loop) whose `ite c` on `c = p + k` (`p` a parameter, `k` a constant) is followed only by atoms and its `ret`."""
    params, body = CORE[key][0], arm_body(key)
    if key in IS_LOOP:
        return []
    adds, consts = {}, set()
    for i, s in enumerate(body):
        if s[0] == 'a' and s[1][0] == 'add':
            adds[s[1][1]] = (s[1][2], s[1][3])
        elif s[0] == 'a' and s[1][0] == 'const':
            consts.add(s[1][1])
        elif s[0] == 'ite':
            rest = body[i + 1:]
            a = adds.get(s[1])
            if rest and rest[-1][0] == 'ret' and all(t[0] == 'a' for t in rest[:-1]) and a is not None and \
                    any(x < len(params) for x in a) and any(x in consts for x in a):
                return [s[1]]
            # (`callc`'s bodies with calls in branches: the last `ite`, its continuation atoms, calls and its `ret`)
            if DUPCALL[0] and rest and rest[-1][0] == 'ret' and all(t[0] in ('a', 'call', 'callIf') for t in rest[:-1]):
                return [s[1]]
    return []


def dup_body(ds, ss):
    """`dupB` (`heapc.dupB`)."""
    for i, s in enumerate(ss):
        if s[0] == 'ite' and s[1] in ds:
            rest = list(ss[i + 1:])
            return list(ss[:i]) + [('ite', s[1], list(s[2]) + rest, list(s[3]) + rest)]
    return ss


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


def gf_mulx(w, k):
    """`w·x^k` in `GF(2^64)` (`x^64 = x^4 + x^3 + x + 1`; `g` is `x`)."""
    for _ in range(k):
        w <<= 1
        if w >> 64:
            w ^= (1 << 64) | 0x1B
    return w


def neg_pows(P):
    """The values a constant `g^-k` (`k < 64`) defines: value -> `k`."""
    out = getattr(P, 'negpows', None)
    if out is None:
        out = {}
        for s in stmts(CORE[P.key][1]):
            if s[0] == 'a' and s[1][0] == 'const' and s[1][2][1] == 0 and s[1][2][0] not in POWS:
                for k in range(1, 64):
                    if gf_mulx(s[1][2][0], k) == 1:
                        out[s[1][1]] = k
                        break
        P.negpows = out
    return out


def assemble(P, st):
    """Runs `⟨Q, 1, 0, X·v⟩` in scope, `v` a constant `g^-k` and `Q` `k` cells past `B`: the same cells as
    `⟨B, 1, g^k, X⟩`; with the points `B·g^i`, `i < k`, before them and the points `B·X·g^i` after them, the run
    `⟨B, 1, 0, X·g^t⟩` (`t` those after)."""
    neg = neg_pows(P)
    if not neg:
        return []
    out = []
    for r, _ in st.runs:
        Q, S, lo, hi = r
        if S != 1 or lo != num(0):
            continue
        vs = [(b, e) for b, e in hi[0] if b in neg and e == 1]
        if len(vs) != 1:
            continue
        k = neg[vs[0][0]]
        X = mk(tuple(x for x in hi[0] if x != vs[0]), hi[1])
        if Q[1] < k or not X[0] or any(shift(Q, i - k) not in st.pts for i in range(k)):
            continue
        B = shift(Q, -k)
        top = mmul(B, X)
        t = 0
        while shift(top, t) in st.pts and t < 64:
            t += 1
        out.append((B, 1, num(0), shift(X, t)))
    return out


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
        if not WRAP[0] and off < 0:
            # below the returned word: not a cell over its slot (offsets are naturals)
            return None
        return mk(tuple(bs), off)

    G.retP = {}
    if 'retP' in F:
        for j, v in enumerate(P.retvals or ()):
            offs = None
            for st, vs in P.rets:
                mv = P.mono(st, vs[j]) if j < len(vs) else None
                o = set()
                if mv is not None and len(mv[0]) == 1 and mv[0][0][1] == 1 and mv[0][0][0] in st.vpf:
                    o = {x - mv[1] for x in st.vpf[mv[0][0][0]][0] if 0 <= x - mv[1] < 2 ** 20}
                offs = o if offs is None else offs & o
            if offs:
                G.retP[j] = frozenset(offs)
    G.retEq = []
    if 'div' in F:
        # equations of the body's top level (on every path) over the parameters and returned words
        for (x, y), pth in zip(P.eqs, P.eqpath):
            if pth:
                continue
            rx, ry = rename(x) if x[0] else x, rename(y) if y[0] else y
            if rx is not None and ry is not None and rx != ry and (rx[0] or ry[0]) and (rx, ry) not in G.retEq:
                G.retEq.append((rx, ry))
    post = postR = postV = postP = None
    rss = []
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
        if 'asm' in F:
            for r in assemble(P, st):
                t = tuple(rename(x) if x[0] else x for x in (r[0], r[2], r[3]))
                if None not in t and t[0][0]:
                    rs.add((t[0], r[1], t[1], t[2]))
        postR = rs if postR is None else postR & rs
        rss.append(rs)
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
    if P.dups and rss:
        # a run guaranteed at one `ret` and empty at the others by their zero branch's equation (`emptyE`)
        def eqs_at(st, path):
            E = []
            for c in path:
                if c[0] == 'ite' and c[2] and c[1] in P.adds:
                    x, y = (P.mono(st, v) for v in P.adds[c[1]])
                    if x is not None and y is not None:
                        rx, ry = rename(x) if x[0] else x, rename(y) if y[0] else y
                        if rx is not None and ry is not None:
                            E.append((rx, ry))
            return E

        def empty(E, r):
            lo, hi = r[2], r[3]
            if lo == hi:
                return True
            for a, b in E:
                for M, N in ((a, b), (b, a)):
                    if M[0] and hi[0]:
                        k = dict(hi[0]).get(M[0][0][0], 0) // M[0][0][1]
                        if k and mpow(M, k) == hi and mpow(N, k) == lo:
                            return True
            return False
        Es = [eqs_at(st, pth) for (st, _), pth in zip(P.rets, P.retpaths)]
        postR = {r for rs in rss for r in rs if all(r in rs_ or empty(E, r) for rs_, E in zip(rss, Es))}
    pre = set(G.pre)
    if 'retM' not in F or 'obj' in F:
        # a returned word `p·g^k` over a parameter: the cells past `p` also over the returned word's slot (with `obj`
        # beside `retM`: a dispatch's arms returning different offsets meet there)
        if 'retM' not in F:
            G.retM = {}
        for p_, slot, k in alias:
            post |= {mk(((slot, 1),), c[1] - k) for c in post if c[0] == ((p_, 1),) and (WRAP[0] or c[1] >= k)}
            postR |= {((((slot, 1),), (r[0][1] - k) % ORD if WRAP[0] else r[0][1] - k), r[1], r[2], r[3])
                      for r in postR if r[0][0] == ((p_, 1),) and (WRAP[0] or r[0][1] >= k)}
    G.post = sorted(c for c in post if c not in pre)[:MAXPTS]
    G.postR = sorted(r for r in postR if r not in set(G.preR))
    if 'ptsrun-long' in F:
        # long contiguous blocks of guaranteed points (an unrolled table) also as runs, for callers' run
        # preconditions; witnessed at the `ret` by their points
        by = collections.defaultdict(set)
        for c in G.post:
            if c[1] < 2 ** 20:
                by[c[0]].add(c[1])
        for bs, offs in by.items():
            offs = sorted(offs)
            i = 0
            while i < len(offs):
                j = i
                while j + 1 < len(offs) and offs[j + 1] == offs[j] + 1:
                    j += 1
                if j - i + 1 >= 16:
                    r = ((bs, offs[i]), 1, num(0), num(j - i + 1))
                    if r not in G.postR:
                        G.postR.append(r)
                i = j + 1
    if 'postQ' in F and P.key not in IS_LOOP:
        postQ = None
        for st, vs in P.rets:
            q = set()
            for c, w in st.hv.items():
                rc = rename(c)
                if rc is None or not rc[0] or not (len(w[0]) == 1 and w[0][0][1] == 1 and w[0][0][0] >= m):
                    continue
                # an own buffer's runs, published by the store of its pointer at `c`
                for r, _ in st.runs:
                    if dict(r[0][0]).get(w[0][0][0]) != 1:
                        continue
                    b = mk(tuple(x for x in r[0][0] if x[0] != w[0][0][0]), r[0][1] - w[1])
                    t = tuple(rename(x) if x[0] else x for x in (b, r[2], r[3]))
                    if None not in t:
                        q.add((rc, (t[0], r[1], t[1], t[2])))
            postQ = q if postQ is None else postQ & q
        G.postQ = sorted(postQ or ())
    G.postV = sorted(postV)[:MAXPTS]
    G.postP = sorted((c, tuple(sorted(o))) for c, o in postP.items())
    if 'pfr' in F:
        import ptrrun
        ptrrun.retsig(P, G, rename)


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
            coalesce_pre(G)
        k = G.key()
        if 'obj' in F:
            import objs
            objs.summary(P, G)
        k = G.key()
        if k == prev:
            break
        prev = k
        G = G.clone()
        SIGS[key] = G
    P.iters = it + 1
    return P


def coalesce_pre(G):
    """Constant residue preconditions `⟨Q·g^r, S, 0, n⟩`, every `r < S`, as the one run `⟨Q, 1, 0, S·n⟩` (the same
    cells): the function's callees then take their residues by points (`ptsrun`), its callers meet one run."""
    by = collections.defaultdict(dict)
    for r in G.preR:
        Q, S, lo, hi = r
        if S > 1 and Q[0] and Q[1] < S and lo == num(0) and not hi[0]:
            by[(Q[0], S, hi)][Q[1]] = r
    for (bs, S, hi), rs in by.items():
        if len(rs) != S or S * hi[1] > MAXPTS:
            continue
        R = (mk(bs, 0), 1, num(0), num(S * hi[1]))
        G.preR = [r for r in G.preR if r not in rs.values()]
        if R not in G.preR:
            G.preR.append(R)


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
    if P.key in CTR_PRE and tails and end[0] and len(end[0]) == 1 and end[1] == 0:
        # a run precondition over the counter, met at the tail for the next iteration: at the exit (`i·g = end`) the
        # path wrote it over `end`, and possibly a few cells further (the largest the tails cover)
        for r in G.preR:
            Q, S, lo, hi = r
            if not any(b == i for b, _ in Q[0]) or any(b == i for b, _ in lo[0]):
                continue
            sub = lambda m: mk(tuple((end[0][0][0], e * end[0][0][1]) if b == i else (b, e) for b, e in m[0]), m[1])
            best = None
            for t in range(3):
                g_ = (sub(Q), S, lo, shift(sub(hi), t))
                nxt = (mk(tuple((b, e) for b, e in Q[0] if b != i) + ((i, dict(Q[0])[i]),), Q[1] + dict(Q[0])[i]), S, lo,
                       shift(mk(tuple((b, e) for b, e in hi[0]), hi[1]) if not any(b == i for b, _ in hi[0]) else
                             mk(hi[0], hi[1] + dict(hi[0])[i]), t))
                P.at_tail = True
                ok = all(P.cover_run(st, nxt, ('tail',)) is not None for st in tails)
                P.at_tail = False
                if ok:
                    best = g_
            if best is not None and best not in G.postR:
                G.postR.append(best)
                P.stats['exit-run'] += 1
    if 'pfr' in F:
        import ptrrun
        ptrrun.loop_finish(P, G, tails, end)


# ---- reporting

NARROW = {}        # (function, table run) -> (offset, stride) its callers write it at (`objs.narrow_site`)
NARROW_SITES = {}


def run_all(rules=True):
    t = time.time()
    NARROW.clear()
    for rnd in range(3 if 'narrow' in F else 1):
        SIGS.clear()
        NARROW_SITES.clear()
        WRAP[0] = 'wrap' in F
        out = {}
        for k in ORDER:
            out[k] = infer(k, rules)
        if 'narrow' not in F:
            break
        import objs
        if not objs.narrow_update():
            break
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
        elif k == 'pfr':
            for i in w[2]:
                add(i)
        elif k == 'perm':
            for i in w[2]:
                add(i)
        elif k == 'armx':
            for i in w[1]:
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
           'ptrsub': 'a run of pointer cells inside the same table\'s runs of another stride (index arithmetic)',
           'selector': 'a match or dispatch selector below its arms (the statement\'s semantics)',
           'rangeCheck': 'a range check (the atom\'s semantics)',
           'merge': 'S residues of stride S are a contiguous run', 'concat': 'two adjacent runs are one',
           'rename': 'a bound rewritten by an assert =='}
# `perm` (a cell one of the cells written at a hinted order's indices) is an instance family: the order's lemma


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
