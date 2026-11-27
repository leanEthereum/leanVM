"""The kernel's heap check of a function in windows (`CoreMode/HeapCWin.lean` for a loop helper, `HeapCWinF.lean`
otherwise): the one `decide` of `heapOkC` would run past the default heartbeats or the memory a module may take.

`callc.py` and `loopcc.py` window every certificate whose check `fn_cost` estimates above `BUDGET` thousand heartbeats
(`one`). The statements are cut between top-level statements, each window estimated at most `WIN` and at most `ATOMS`
atoms; a window that is one `match` and still over `WIN` is checked by windows of its arms (`HeapCWinM.lean`).
`heapc.py`'s pass (the check in Python, step for step) gives the state at each cut, written as data over the previous
state (`Lits.lstate`: each trie `insL` of its new entries over the previous state's trie, the pass only adding entries;
the lists the previous state's plus what is new; values, runs, arms and cells' bases that recur shared as `def`s). The
windows cover a loop helper's body without its tail (`loopBody`), or a function's body before a last part that holds
its first top-level `ret`. Per function, in `GenW/<fn>/` (`callc.py`) or `GenWL/<fn>/` (`loopcc.py`):

* `Cx.lean` (parts `CxD<j>`, equations `CxH<j>` if long): `sigW` (the callees' signatures as `CFun.sigOf` reads
  them), which the context of a function with at least `SIGK` callees reads by the names' keys (`sigK`, `hsigK`,
  `SigIx.lean`: no string compared); each trie `cxOf` builds from the certificate as a literal of its shape whose
  entries are positions of the certificate's lists (`nthO`, `lrefs`: nothing restated), `hcx<field>` its equation
  (one `decide +kernel`); the context `cxL` and `hcx : cxOf .. = cxL` (`cxOf_lit`), so that no window builds the
  tries (each window's proof rewrites `withCx` by `withCx_cx hcx`); `S<j>.lean`: the states `st<i>`, in modules of at
  most `SPART` characters (each importing the last, the first `Cx`);
* `W<i>.lean`: `win<i> : winOk Fn.«{k}».pows sigW core hcert (((loopBody core).drop a).take (b - a)) st<i> st<i+1> =
  true` (`winOkF` over `core.body` for a function; one `decide +kernel`: no `ret` (a function's windows: no top-level
  one), no ghost value, the pass from one state to the next); for a `match` split by arms, `W<i>A<t>.lean` hold
  `arms<i>_<t> : armsOkW ..` (the arms' summaries `sum<i>_<t>`) and `W<i>` the join (`joinOk`) and `win<i>` by
  `winOk_of_arms`;
* `Ok.lean`: `head_ok`, `tail_ok` (a function: `last_ok`, the statements from the last cut on) and
  `Fn.«fn».heap_okW`, the check at the callees' signatures, by `heapOkC_of_wins` (`heapOkC_of_winsF`), which
  `core.py`'s `heap_okC` takes.
"""
import sys, os, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import infer as I
import heapc as C
import emitc as E
import windows
import genfiles

# the windows' sizes (`windows.py`)
BUDGET, WIN, ATOMS, FIXW = windows.HEAP_BUDGET, windows.HEAP_WIN, windows.HEAP_ATOMS, windows.HEAP_FIXW
CXPART, CXDEC, SPART = windows.HEAP_CXPART, windows.HEAP_CXDEC, windows.HEAP_SPART
# the callees' signatures as `CFun.sigOf` reads them (`sigW`), and the number of callees from which a context reads
# them by the names' keys instead (`sigK`, `SigIx.lean`'s `sigK_eq`, whose left side is `SIGW`): with fewer, the keys
# cost the kernel more than the scan of the names
SIGW = '(fun f ↦ bif f == core.name then hcert.sig else (csigs.lookup f).getD {})'
SIGK = 100
# The kernel's work, in thousands of heartbeats (the heartbeat limit's unit), estimated from `heapc.py`'s pass: per
# line it executes (`Meter`), per atom (the ghost check), per character of the certificate (the context's tries), per
# frame run cell and top-level statement (`faOk`), per trie entry or list element of a window's states (comparing the
# end state), fitted to the kernel's heartbeats of the one-piece checks and of the windows.
W_LINE, W_ATOM, W_CERT, W_FA, W_ENT = 0.2, 15, 0.02, 0.4, 0.5
# entries a context trie's reference walks at most (`lrefs`)
BLK = 32
DEPTH = 20                      # `Exec.indexDepth`: keys past it are dropped by `setF`
KEYMAX = 2 ** DEPTH - 1


class Meter:
    """The lines Python executes while active (`with`): the pass's work, loops included."""

    def __init__(self):
        self.n = 0

    def _trace(self, frame, ev, arg):
        if ev == 'line':
            self.n += 1
        return self._trace

    def __enter__(self):
        self.n = 0
        sys.settrace(self._trace)
        return self

    def __exit__(self, *a):
        sys.settrace(None)


def atoms(s):
    """Atoms of a statement, the arms' included."""
    k = s[0]
    if k == 'a':
        return 1
    if k == 'ite':
        return 1 + sum(map(atoms, s[2])) + sum(map(atoms, s[3]))
    if k == 'match':
        return 1 + sum(atoms(t) for arm in s[2] for t in arm)
    return 1


def is_loop(H):
    """A loop helper's certificate (`term = [(.val 0, end)]`); otherwise `term = []`."""
    return bool(H.sig.term)


def region(k, H):
    """The statements the windows cover: a loop helper's body without the tail (`loopBody`); a function's body up to
    its first top-level `ret` (the windows end at a cut `N`; `lastOkF` checks the statements from `N` on)."""
    body = I.arm_body(k)
    if is_loop(H):
        return body[:-2]
    r = next((i for i, s in enumerate(body) if s[0] == 'ret'), len(body))
    return body[:r]


def states(k, H, sigOf):
    """The check's pass (`heapc.heapOkC`) over the statements of `region`: `([S0, S1, ..], [cost0, ..])`, `S_i` the
    state before statement `i`, `cost_i` statement `i`'s estimated heartbeats."""
    params, body = I.CORE[k][0], I.arm_body(k)
    G = H.sig
    m = len(params)
    X_ = C.X(dict(I.POWS), H, sigOf, params)
    P = C.Pass(X_, sigOf, body)
    assert list(params) == list(range(m)), 'params'
    if is_loop(H):
        assert len(G.term) == 1 and G.term[0][0] == ('val', 0), ('not a loop helper', G.term)
        assert not (G.retM or G.postV or G.retEq), 'loop with retM/postV/retEq'
        assert body[-1] == ('ret', []) and body[-2][0] == 'callIf', 'loop shape'
    assert all(v < C.DB for v in C.values(params, body)), 'noGhost'
    st = C.St()
    for i in range(m):
        st.env[i] = C.baseC(i)
    ms = C.monos(st.env, params) + [C.baseC(C.GB + j) for j in range(G.ghosts)]
    pps, rs, prs = C.instPP(ms, G.preP), C.instAllR(ms, G.preR), C.instPRL(ms, G.prePR)
    assert None not in (pps, rs, prs), 'init-inst'
    for p in pps:
        st.pushP(p)
    for r in rs:
        st.pushR(r)
    for p in prs:
        st.pushPR(p)
    out, costs = [st.copy()], []
    for s in region(k, H):
        with Meter() as mt:
            st = P.block([s], st)
        costs.append(W_LINE * mt.n + W_ATOM * atoms(s))
        out.append(st.copy())
    return out, costs, P


def arm_blocks(P, s, st):
    """The pass over the arms of the `match` `s` from `st` (`Pass.block`'s, `chkArmsC`): per arm `(returns, start,
    end, estimated heartbeats)`."""
    out, cur = [], st
    for j, arm in enumerate(s[2]):
        with Meter() as mt:
            s1 = P.under(('arm', s[1], j), lambda: P.block(arm, cur.copy()))
        out.append((C.endsRet(arm), cur, s1, W_LINE * mt.n + W_ATOM * sum(map(atoms, arm))))
        cur = st.cnt(s1)
    return out


def rngd(t, lo, n):
    """`rng t lo n`: the entries at the keys `lo` .. `lo + n - 1`."""
    return [(k, t[k]) for k in range(lo, lo + n) if k in t and k < KEYMAX]


def lblk(b):
    """A block's `BlkSum` (`blkSum`), as a literal."""
    ret, s0, s1 = b[:3]
    dn, dr = max(0, s1.n - s0.n), max(0, s1.nr - s0.nr)
    pair = lambda l, f: '[' + ', '.join(f'({k}, {f(v)})' for k, v in l) + ']'
    return (f'⟨{"true" if ret else "false"}, {pair(rngd(s1.sc, s0.n, dn), lcell)}, '
            f'{pair(rngd(s1.rs, s0.nr, dr), lprun)}, '
            f'{pair(rngd(s1.pf, s0.n, dn), lambda p: f"({lcell(p[0])}, {lnums(p[1])})")}, '
            f'{pair(rngd(s1.pr, s0.nr, dr), lambda p: f"({lprun(p[0])}, {lnums(p[1])})")}⟩')


def lcnt(s):
    return f'({s.n}, {s.nr}, {s.nc}, {s.nt})'


def fn_cost(k, H, sigOf):
    """The estimated heartbeats (thousands) of `k`'s check in one `decide`: what `emitc.py` compares with `BUDGET`."""
    params, body = I.CORE[k][0], I.arm_body(k)
    with Meter() as mt:
        C.heapOkC(dict(I.POWS), sigOf, k, params, body, H)
    return W_LINE * mt.n + W_ATOM * sum(map(atoms, body)) + fixed_cost(k, H)


def fixed_cost(k, H):
    """What every window pays (the context's tries) and the head (`faOk`)."""
    body = I.arm_body(k)
    r = next((i for i, s in enumerate(body) if any(t[0] == 'ret' for t in C.stmts([s]))), len(body))
    return W_CERT * cert_size(H) + W_FA * len(H.fas) * r


def cert_size(H):
    """The certificate's size, its witnesses written one by one (as the kernel's check reads them, `E.RANGE` aside)."""
    rng, E.RANGE = E.RANGE, float('inf')
    try:
        aux, body = E.lcert(H)
    finally:
        E.RANGE = rng
    return len(body) + sum(map(len, aux))


def entries(st):
    """A state's size: its tries' entries and its lists' elements."""
    return (sum(len(getattr(st, f)) for f in ('env', 'sc', 'rs', 'ad', 'sv', 'src', 'pf', 'pr')) + len(st.eqs) +
            sum(1 + sum(1 + len(a[0]) + len(a[1]) + len(a[2]) + len(a[3]) for a in e[1]) for e in st.cd))


def cuts(costs, na, ents, budget):
    """Cut points `0 = a0 < a1 < .. < aN = len(costs)`, each window `[a, b)` at most `budget` (its statements' cost
    and `W_ENT` per entry of its two states) and `ATOMS` atoms, or one statement."""
    out, acc, accn = [0], 0, 0
    for i, (n, a) in enumerate(zip(costs, na)):
        if (acc or accn) and (acc + n + W_ENT * (ents[out[-1]] + ents[i + 1]) > budget or accn + a > ATOMS):
            out.append(i)
            acc = accn = 0
        acc += n
        accn += a
    out.append(len(costs))
    return out


# ---- Lean text

def lcell(c):
    return E.lcell(c)


def lprun(r, lc=None):
    lc = lc or lcell
    return f'⟨{lc(r[0])}, {r[1]}, {lc(r[2])}, {lc(r[3])}⟩'


def lbases(c):
    """A cell's bases (`CCell.bases`) as Lean."""
    return '[' + ', '.join(f'({b}, {e})' for b, e in c[0]) + ']'


def lnums(l):
    return '[' + ', '.join(map(str, l)) + ']'


def ldef(name, typ, text):
    """A `def` of a literal, on one line if it fits, built as a term (`data%`, `Guest/DataLit.lean`)."""
    one = f'noncomputable def {name} : {typ} := data% {text}'
    return one + '\n' if len(one) <= 120 else f'noncomputable def {name} : {typ} :=\n  data% {pack(text)}\n'


def dlst(text):
    """A list literal `emitc.Aux.lst` wrote inline, built as a term (`data%`); its parts' names as they are."""
    return f'(data% {text})' if text.startswith('[') else text


def larm(a, lc=None, lr=None):
    """A `CdA` (an arm's guarantees under its selector) as Lean, its cells by `lc` and runs by `lr`."""
    lc = lc or lcell
    lr = lr or (lambda r: lprun(r, lc))
    return (f'⟨[{", ".join(map(lc, a[0]))}], [{", ".join(map(lr, a[1]))}], '
            f'[{", ".join(f"({lc(p[0])}, {lnums(p[1])})" for p in a[2])}], '
            f'[{", ".join(f"({lprun(p[0], lc)}, {lnums(p[1])})" for p in a[3])}]⟩')


def larms(arms):
    return '[' + ', '.join(map(larm, arms)) + ']'


# a state's tries: their fields, how their values print, their types
TVAL = {'env': lambda c, lc: lc(c), 'sc': lambda c, lc: lc(c), 'rs': lprun,
        'ad': lambda p, lc: f'({lc(p[0])}, {lc(p[1])})', 'sv': lambda p, lc: f'({lc(p[0])}, {lc(p[1])})',
        'src': lambda c, lc: lc(c), 'pf': lambda p, lc: f"({lc(p[0])}, {lnums(p[1])})",
        'pr': lambda p, lc: f"({lprun(p[0], lc)}, {lnums(p[1])})"}
TTYP = {'env': 'CCell', 'sc': 'CCell', 'rs': 'PRun', 'ad': '(CCell × CCell)', 'sv': '(CCell × CCell)', 'src': 'CCell',
        'pf': '(CCell × List ℕ)', 'pr': '(PRun × List ℕ)'}


def tset(t, a, d, n):
    """`Check.setF a d t n` on a trie as nested lists `[value, left, right]` (`None` the empty trie)."""
    if d == 0:
        return t
    if n == 0:
        return [a, None, None] if t is None else [a, t[1], t[2]]
    m = n - 1
    v, l, r = t if t is not None else (None, None, None)
    if m % 2 == 0:
        return [v, tset(l, a, d - 1, m // 2), r]
    return [v, l, tset(r, a, d - 1, m // 2)]


CXSHARE = 6000  # characters: a context trie's subtree longer is its own `def` (a bound on a declaration)
VSHARE = 48   # characters: a state entry's value at most this long is never a shared `def`


def pack(text, ind='    ', width=118):
    """A term's text in lines of at most `width` characters, broken at spaces (the literals hold no strings)."""
    lines, cur = [], ''
    for tok in text.split():
        if cur and len(cur) + 1 + len(tok) > width:
            lines.append(cur)
            cur = ind + tok
        else:
            cur = f'{cur} {tok}' if cur else tok
    if cur:
        lines.append(cur)
    return '\n'.join(lines)


class Lits:
    """The literals of one function's states, each over the previous one (`lstate`), or of a context trie
    (`ltrie`)."""

    def __init__(self, prefix=''):
        self.shared = {}
        self.cnt = 0
        self.prev = {}
        self.prefix = prefix
        self.prevst = None
        self.counts = collections.Counter()

    def count(self, st):
        """Occurrences of each value, run, arm, arms list and cell's bases in `st` (the last state: the pass only
        adds), which the state literals share as `def`s where they recur (`want`)."""
        c = self.counts

        def lc(x):
            c[lbases(x)] += 1
            return lcell(x)
        for f, val in TVAL.items():
            for v in getattr(st, f).values():
                c[val(v, lcell)] += 1
                val(v, lc)
        for mx, arms in st.cd:
            c[larms(arms)] += 1
            lc(mx)
            for a in arms:
                c[larm(a)] += 1
                larm(a, lc)
                for r in a[1]:
                    c[lprun(r)] += 1
        for a, b in st.eqs:
            lc(a), lc(b)

    def want(self, text, typ, least=0):
        """Whether `text` is (to be) a shared `def`: already one, or longer than `least` and recurring often enough
        that the `def` takes less room than the copies (by the counts of `count`)."""
        n = self.counts[text]
        return ('v', typ, text) in self.shared or (len(text) > least and n >= 2 and
                                                   n * (len(text) - 6) > len(text) + 130)

    def sh(self, text, typ, defs, least=0, body=None):
        """`text`, or the name of its shared `def` (`want`; written into `defs` at its first use, as `body` if
        given: the same term with its own parts shared)."""
        if not self.want(text, typ, least):
            return body() if body else text
        key = ('v', typ, text)
        if key not in self.shared:
            b = body() if body else text
            self.shared[key] = f'{self.prefix}v{self.cnt}'
            self.cnt += 1
            defs.append(ldef(self.shared[key], typ, b))
        return self.shared[key]

    def lc(self, defs):
        """The cell printer: a cell's bases (a monomial's, often long and recurring at many offsets) shared."""
        def go(c):
            b = lbases(c)
            n = self.sh(b, 'List (ℕ × ℕ)', defs, 16)
            return f'⟨{n}, {c[1]}⟩'
        return go

    def lcd(self, mx, arms, defs):
        """A `CdE`, its runs, arms and arms list shared where they recur."""
        lc = self.lc(defs)

        def arm(a):
            return self.sh(larm(a), 'CdA', defs, body=lambda: larm(a, lc, lambda r: self.sh(
                lprun(r), 'PRun', defs, body=lambda: lprun(r, lc))))
        al = self.sh(larms(arms), 'List CdA', defs, body=lambda: '[' + ', '.join(map(arm, arms)) + ']')
        return f'⟨{lc(mx)}, {al}⟩'

    def ltrie(self, d, typ, defs):
        """The trie the check builds for the entries `d` (`setF` at `Exec.indexDepth`; its shape depends only on the
        keys), as `.node`s whose entries are the texts `d` maps keys to (terms of `Option typ`), a subtree longer
        than `CXSHARE` a `def` (into `defs`). A literal costs the kernel nothing to build, where building the trie
        costs about as much as a window's pass."""
        t = None
        for k in sorted(d):
            t = tset(t, d[k], DEPTH, k)

        def go(t):
            if t is None:
                return '.nil'
            out = f'(.node {"none" if t[0] is None else t[0]} {go(t[1])} {go(t[2])})'
            if len(out) > CXSHARE:
                name = f'{self.prefix}tr{self.cnt}'
                self.cnt += 1
                defs.append(ldef(name, f'Trie {typ}', out))
                return name
            return out
        return go(t)

    def llist(self, field, items, typ, name, defs, front):
        """A list growing at its end (`front` false: `cd`) or its front (`eqs`), as the previous state's plus what
        is new."""
        ax = E.Aux(data=True)
        p = self.prev.get(field)
        if p is not None and len(items) >= len(p[0]) and (
                items[:len(p[0])] == p[0] if not front else items[len(items) - len(p[0]):] == p[0]):
            new = items[len(p[0]):] if not front else items[:len(items) - len(p[0])]
            nl = dlst(ax.lst(f'{name}_', typ, new))
            text = f'{p[1]} ++ {nl}' if not front else f'{nl} ++ {p[1]}'
        else:
            text = dlst(ax.lst(f'{name}_', typ, items))
        defs += [d.replace('def ', 'noncomputable def ', 1) for d in ax.defs]
        defs.append(f'noncomputable def {name} : List {typ} := {text}\n')
        self.prev[field] = (items, name)
        return name

    def ldelta(self, d, val, typ, defs, name, field):
        """The trie the pass holds for the entries `d`, as `insL` of the entries new since the previous state over
        its trie (`<prev>.<field>`; the pass only adds entries, and a trie's shape depends only on its keys), or of
        all of them over `.nil`, values that recur shared (`sh`, longer than `VSHARE`)."""
        prev = self.prevst
        pd = getattr(prev[1], field) if prev else None
        if pd is not None and all(k in d and d[k] == v for k, v in pd.items() if k < KEYMAX):
            items, base = sorted((k, v) for k, v in d.items() if k < KEYMAX and k not in pd), f'{prev[0]}.{field}'
        else:
            items, base = sorted((k, v) for k, v in d.items() if k < KEYMAX), '.nil'
        if not items:
            return base
        lc = self.lc(defs)
        out = [f'({k}, {self.sh(val(v, lcell), typ, defs, VSHARE, body=lambda v=v: val(v, lc))})' for k, v in items]
        ax = E.Aux(data=True)
        lst = dlst(ax.lst(f'{name}_{field}_', f'(ℕ × {typ})', out))
        defs += [d.replace('def ', 'noncomputable def ', 1) for d in ax.defs]
        return f'insL {lst} {base}'

    def lstate(self, st, name):
        """A state's literal, `(aux defs, text)`: each trie `insL` of its new entries over the previous state's
        (`ldelta`), the lists the previous state's plus what is new (`llist`), recurring values, runs, arms and
        cells' bases shared (`sh`, `lcd`, `lc`)."""
        defs = []
        lc = self.lc(defs)
        cd = [self.lcd(mx, arms, defs) for mx, arms in st.cd]
        eqs = [f'({lc(a)}, {lc(b)})' for a, b in st.eqs]
        fs = [self.ldelta(getattr(st, f), val, TTYP[f], defs, name, f) for f, val in TVAL.items()]
        fs += [f'{st.n}, {st.nr}, {st.nc}, {st.nt}',
              self.llist('cd', cd, 'CdE', f'{name}_cd', defs, False),
              self.llist('eqs', eqs, '(CCell × CCell)', f'{name}_eqs', defs, True),
              '[' + ', '.join(f'({lc(c)}, {lprun(q, lc)})' for c, q in st.dq) + ']']
        self.prevst = (name, st)
        return defs, '⟨' + ',\n    '.join(fs) + '⟩'


HEADER = genfiles.header('core-mode/heapwin.py')
# the import the modules writing their literals `data% …` take (`Guest/DataLit.lean`)
DATA = 'public meta import LeanVM.Guest.DataLit\n'


def core_name(k):
    """The name `core.name` holds: the compiler's name whose stable name is `k` (`coreir.load`'s `stable`)."""
    ns = [n for n, s in I.STABLE.items() if s == k]
    if len(ns) > 1:
        raise SystemExit(f'heapwin: {k} is the stable name of {ns}')
    return ns[0] if ns else k


def str_key(name):
    """`CoreMode.strKey`: the name's UTF-8 bytes as base-256 digits, the first the least significant, under a 1."""
    return int.from_bytes(name.encode() + b'\x01', 'little')


def repack(text):
    """Code lines over 120 characters packed (`pack`), at their indentation plus four."""
    out = []
    for l in text.split('\n'):
        if len(l) > 120 and not l.lstrip().startswith(('--', '/-')):
            n = len(l) - len(l.lstrip())
            out.append(' ' * n + pack(l.strip(), ' ' * (n + 4), 118 - n))
        else:
            out.append(l)
    return '\n'.join(out)


def emit_arms(k, i, a, split, blk, ns, base, imps, sub='HeapW', smod=None):
    """The arm windows of window `i`, the `match` at statement `a`: `[(name, text)]`, module `W<i>A<t>` holding the
    summaries `sum<i>_<t>` of its arms and `arms<i>_<t> : armsOkW ..`."""
    bl, ac = split
    out = []
    for t in range(len(ac) - 1):
        j, j2 = ac[t], ac[t + 1]
        c0 = f'(cntOf st{i})' if t == 0 else lcnt(bl[j - 1][2])
        ax = E.Aux()
        sums = ax.lst(f'sum{i}_{t}_', 'BlkSum', [lblk(b) for b in bl[j:j2]])
        x = HEADER(f'{base}.W{i}A{t}', what=f'Arms {j} to {j2 - 1} of statement {a} of `{k}`\'s heap check.')
        x += f'public import {base}.{smod or "S" + str(i)}\npublic import LeanVM.Guest.CoreMode.HeapCWinM\n' + imps
        x += f'\nset_option maxRecDepth 100000\nset_option linter.all false\nset_option Elab.async false\n\n'
        x += f'namespace {ns}.{sub}\n\nopen LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
        x += ''.join(f'/-- Part of `sum{i}_{t}`. -/\n{d}\n' for d in ax.defs)
        x += f'/-- What the join reads of arms {j} to {j2 - 1}. -/\ndef sum{i}_{t} : List BlkSum := {sums}\n\n'
        x += (f'/-- Arms {j} to {j2 - 1}. -/\ntheorem arms{i}_{t} : armsOkW Fn.«{k}».pows sigW core hcert '
              f'({blk}.drop {a}) '
              f'{j} ({j2} - {j}) st{i} {c0} sum{i}_{t} {lcnt(bl[j2 - 1][2])} = true := {wprf("armsOkW")}\n\n')
        x += f'end\nend {ns}.{sub}\n'
        out.append((f'W{i}A{t}', x))
    return out


def chunks(items):
    """`emitc.Aux.lst`'s parts of a list of `items` (texts): `None` if it stays inline, else each part's first
    position."""
    if sum(len(x) + 2 for x in items) <= E.LIM:
        return None
    starts, n = [0], 0
    for i, x in enumerate(items):
        if i > starts[-1] and n + len(x) > E.LIM:
            starts.append(i)
            n = 0
        n += len(x) + 2
    return starts


def lrefs(items, name, whole, f):
    """Each position of a certificate's list as `Option` of its entry: `nthO` of the part of the list `emitc.lcert`
    wrote it in (`name<j>`, or the list `whole` if it is one piece), or of that part without its first `BLK * q`
    entries, a `def` (`cx<f>d<t>`) so that no reading walks more than `BLK` entries. `(refs, defs)`."""
    st = chunks(items) or [0]
    out, defs = [], []
    for j, a in enumerate(st):
        b = st[j + 1] if j + 1 < len(st) else len(items)
        part = whole if len(st) == 1 else f'{name}{j}'
        for q in range(0, b - a, BLK):
            src = part
            if q:
                src = f'cx{f}d{len(defs)}'
                defs.append(f'noncomputable def {src} := dropO {part} {q}\n')
            out += [f'(nthO {src} {i})' for i in range(min(BLK, b - a - q))]
    return out, defs


def fl_cost(H, f):
    """The characters of the certificate's list a context trie is built from: what its equation's evaluation
    grows with."""
    if f == 'R':
        return sum(len(E.lwit(w)) + 12 for w in H.reads.values())
    if f == 'P':
        return sum(len(E.lcell(c)) for c in H.sig.pre)
    if f in ('C', 'T'):
        return sum(len(E.lwit(w)) + 2 for ws in (H.calls if f == 'C' else H.rets) for w in ws)
    if f == 'RS':
        return sum(len(E.lres(r)) for r in H.res)
    return 8 * len(H.divs if f == 'DV' else H.hvs if f == 'HV' else H.eqs)


def lcx(H, pre='sig_pre', lpre=''):
    """The context's tries (`cxOf`) as literals: `[(field, its expression, type, defs, literal)]`, each of
    `hcert.readT` and of `trieFrom` a list of the certificate a literal of the trie's shape whose entries are positions
    of the certificate's lists (`lrefs`: the data is not restated), the key sets (`keysT`) plain literals. `pre` names
    the parts of the signature's `pre` (`emitc.lsig`'s, in the signature module for a signature callers name)."""
    by_d = collections.defaultdict(list)
    for (d, p, off), w in sorted(H.reads.items()):
        by_d[d].append(f'({p}, {off}, {E.lwit(w)})')
    ritems = [f'({d}, [{", ".join(rs)}])' for d, rs in sorted(by_d.items())]
    rref, rdefs = lrefs(ritems, lpre + 'reads', 'hcert.reads', 'R')
    rref = [f'(Option.map Prod.snd {r})' for r in rref]
    ax = E.Aux()
    citems = [E.lwits(ax, f'{lpre}call{i}_', ws) for i, ws in enumerate(H.calls)]
    titems = [E.lwits(ax, f'{lpre}ret{i}_', ws) for i, ws in enumerate(H.rets)]
    ref = lambda items, name, whole, f: (lambda r: (dict(enumerate(r[0])), r[1]))(lrefs(items, name, whole, f))
    fields = [('R', 'hcert.readT', '(List (ℕ × ℕ × CoreMode.Wit))', (dict(zip(sorted(by_d), rref)), rdefs)),
              ('P', 'trieFrom hcert.sig.pre 0 .nil', 'CCell', ref(list(map(E.lcell, H.sig.pre)), pre, 'hcert.sig.pre', 'P')),
              ('C', 'trieFrom hcert.calls 0 .nil', '(List CoreMode.Wit)', ref(citems, lpre + 'calls', 'hcert.calls', 'C')),
              ('T', 'trieFrom hcert.rets 0 .nil', '(List CoreMode.Wit)', ref(titems, lpre + 'rets', 'hcert.rets', 'T')),
              ('RS', 'trieFrom hcert.res 0 .nil', 'CoreMode.CRes', ref(list(map(E.lres, H.res)), 'res', 'hcert.res', 'RS')),
              ('DV', 'keysT hcert.divs .nil', 'Unit', (dict.fromkeys(H.divs, '(some ())'), [])),
              ('HV', 'keysT hcert.hvs .nil', 'Unit', (dict.fromkeys(H.hvs, '(some ())'), [])),
              ('EQ', 'keysT hcert.eqs .nil', 'Unit', (dict.fromkeys(H.eqs, '(some ())'), []))]
    out = []
    for f, lhs, typ, (d, defs) in fields:
        lit = Lits(f'cx{f}').ltrie({k: v for k, v in d.items() if k < KEYMAX}, typ, defs)
        out.append((f, lhs, typ, defs, lit))
    return out


def wprf(d):
    """A window's proof: the context's tries read from their literals (`Cx.lean`), then one kernel evaluation."""
    return f'by\n  simp only [{d}, withCx_cx hcx]\n  decide +kernel'


def emit(k, H, sts, cs, po, splits, gen):
    """The modules of one function: `[(name, text)]`. `gen`, a dict of `root` (the modules' prefix), `sub` (the
    namespace under the function's), `data` (the certificate's modules), `names` (the callees),
    `final` (the name of the heap check's theorem) and `pre` (its precondition's name, default `sig_pre`); for an arm
    of a split certificate (`HCert.arms`), `ns` and `base` (its namespace, where `core` and `hcert` are the arm's, and
    its modules' prefix), `lpre` (the prefix of its lists' declarations) and `one` (the theorem `heapOkC1`'s)."""
    pack, core_mod = po[k][0], po[k][1]
    data, sub = gen['data'], gen['sub']
    ns = gen.get('ns', f'LeanVM.Guest.Fn.«{k}»')
    base = gen.get('base', f'{gen["root"]}.«{k}»')
    mods = []
    loop = is_loop(H)
    nw = len(cs) - 1 if loop else len(cs) - 2      # a function's last chunk is `lastOkF`'s
    imps = (f'public import LeanVM.Guest.CoreMode.Pows.«{pack}»\npublic import LeanVM.Guest.Pack.«{pack}».{core_mod}\n')
    opn = (f'namespace {ns}.{sub}\n\nopen LeanVM.Guest.CoreMode\nopen LeanVM.Guest.Exec (Trie)\n\n'
           f'@[expose] public section\n')
    # the context (`Cx`): the callees' signatures, each trie stated once (`lcx`), their parts in modules of at most
    # `CXPART` characters (`CxD<j>`, each importing the last) if long
    fl = lcx(H, pre=gen.get('pre', 'sig_pre'), lpre=gen.get('lpre', ''))
    head = (f'public import LeanVM.Guest.CoreMode.HeapCWin{"" if loop else "F"}\n' +
            ''.join(f'public import {m}\n' for m in data) + imps)
    sigd = f'/-- The callees\' signatures. -/\nnoncomputable def sigW : String → CoreMode.HSig := {SIGW}\n'
    # the equations, in groups of at most `CXDEC` characters of the certificate's lists they read (`CxH<j>`, each
    # importing the definitions) if more than one, else in `Cx`
    groups, g = [], []
    for f, lhs, typ, defs, lit in fl:
        if g and sum(c for *_, c in g) + fl_cost(H, f) > CXDEC:
            groups.append(g)
            g = []
        g.append((f, lhs, fl_cost(H, f)))
    groups.append(g)
    parts, cur = [], [sigd]
    for f, lhs, typ, defs, lit in fl:
        for d in defs + [f'/-- `cxOf`\'s trie `{f}`. -/\nnoncomputable def cx{f} : Trie {typ} :=\n  data% {lit}\n']:
            if cur and sum(map(len, cur)) + len(d) > CXPART:
                parts.append(cur)
                cur = []
            cur.append(d)
    if len(groups) > 1:
        parts.append(cur)
        cur = []
    prev = None
    for j, ds in enumerate(parts):
        cd = HEADER(f'{base}.CxD{j}', what=f'Part {j} of the tries of `{k}`\'s heap check context.')
        cd += (f'public import {prev}\n' if prev else head) + DATA + '\nset_option maxRecDepth 100000\n'
        cd += 'set_option linter.all false\n\n' + opn + '\n' + ''.join(ds) + f'\nend\nend {ns}.{sub}\n'
        mods.append((f'CxD{j}', repack(cd)))
        prev = f'{base}.CxD{j}'
    thm = lambda g: ''.join(f'\ntheorem hcx{f} : {lhs} = cx{f} := by\n  decide +kernel\n' for f, lhs, _ in g)
    if len(groups) > 1:
        for j, g in enumerate(groups):
            ch = HEADER(f'{base}.CxH{j}', what=f'Equations {j} of the tries of `{k}`\'s heap check '
                               f'context.')
            ch += f'public import {prev}\n\nset_option Elab.async false\n\n' + opn + thm(g) + f'\nend\nend {ns}.{sub}\n'
            mods.append((f'CxH{j}', ch))
    cx = HEADER(f'{base}.Cx', what=f'The context of `{k}`\'s windowed heap check: the callees\' '
                       f'signatures, the tries stated.')
    if len(groups) > 1:
        cx += ''.join(f'public import {base}.CxH{j}\n' for j in range(len(groups)))
    else:
        cx += f'public import {prev}\n' if prev else head
    sigk = len(gen['names']) >= SIGK
    cx += ('public import LeanVM.Guest.CoreMode.SigIx\n' if sigk else '') + DATA
    cx += '\nset_option maxRecDepth 100000\nset_option linter.all false\nset_option Elab.async false\n\n' + opn
    cx += '\n' + ''.join(cur) if cur else ''
    cx += thm(groups[0]) if len(groups) == 1 else ''
    # past `SIGK` callees, their signatures read by their names' keys (`SigIx.lean`), the keys stated once
    sig = 'sigW'
    if sigk:
        own, keys = str_key(core_name(k)), ', '.join(str(str_key(f)) for f in gen['names'])
        sig = f'sigK {own} hcert.sig sigKeys csigs'
        cx += (f'\n/-- The keys of the callees\' names (`strKey`). -/\nnoncomputable def sigKeys : List ℕ :=\n'
               f'  data% [{keys}]\n\n/-- The callees\' signatures, read by key. -/\n'
               f'theorem hsigK : sigW = {sig} :=\n  sigK_eq (by decide +kernel) (by decide +kernel)\n')
    cx += (f'\n/-- The context, its tries stated. -/\n'
           f'noncomputable def cxL : CX := ⟨Fn.«{k}».pows, cxR, cxP, cxC, cxT, '
           f'cxRS, cxDV, cxHV, hcert.gargs, {sig}, hcert.sig, core.params, [], cxEQ, hcert.fas, hcert.ders⟩\n')
    lit = 'cxOf_lit hcxR hcxP hcxC hcxT hcxRS hcxDV hcxHV hcxEQ'
    prf = f' by\n  rw [hsigK]\n  exact {lit}' if sigk else f'\n  {lit}'
    cx += f'\ntheorem hcx : cxOf Fn.«{k}».pows sigW core hcert = cxL :={prf}\n'
    # the states, in modules of at most `SPART` characters (the first in `Cx`, then `S<j>`, each importing the last),
    # each sharing the previous state's tries (`Lits`); `smod[i]` the module of `st<i>`
    lits = Lits()
    lits.count(sts[cs[nw]])
    groups, cur, smod = [], [], {}
    for i, a in enumerate(cs[:nw + 1]):
        aux, text = lits.lstate(sts[a], f'st{i}')
        t = ''.join(aux) + f'/-- The state before statement {a}. -/\nnoncomputable def st{i} : CSt := data% {text}\n'
        if cur and sum(len(x[1]) for x in cur) + len(t) > SPART:
            groups.append(cur)
            cur = []
        cur.append((i, t))
    groups.append(cur)
    cx += '\n' + ''.join(t for _, t in groups[0]) + f'\nend\nend {ns}.{sub}\n'
    mods.append(('Cx', repack(cx)))
    for i, _ in groups[0]:
        smod[i] = 'Cx'
    for g, grp in enumerate(groups[1:], 1):
        si = HEADER(f'{base}.S{g}', what=f'The states {grp[0][0]} to {grp[-1][0]} of `{k}`\'s '
                           f'windowed heap check.')
        si += f'public import {base}.{"S" + str(g - 1) if g > 1 else "Cx"}\n' + DATA + '\nset_option maxRecDepth 100000\n'
        si += 'set_option linter.all false\n\n' + opn + '\n' + ''.join(t for _, t in grp)
        si += f'\nend\nend {ns}.{sub}\n'
        mods.append((f'S{g}', repack(si)))
        for i, _ in grp:
            smod[i] = f'S{g}'
    # an arm's `core` is its own (`CoreMode.selF`): `(core).body` its projection, where `core.body` would name the
    # function's whole body (`Fn.«k».core.body`)
    blk, wok = ('(Memory.loopBody core)', 'winOk') if loop else ('(core).body' if 'ns' in gen else 'core.body', 'winOkF')
    for i in range(nw):
        a, b = cs[i], cs[i + 1]
        w = HEADER(f'{base}.W{i}', what=f'Window {i} of `{k}`\'s heap check: statements {a} to {b - 1}.')
        w += f'public import {base}.{smod[i + 1]}\n'
        if i in splits:
            amods = emit_arms(k, i, a, splits[i], blk, ns, base, imps, sub, smod[i])
            mods += amods
            w += ''.join(f'public import {base}.{nm}\n' for nm, _ in amods)
            w += f'public import LeanVM.Guest.CoreMode.HeapCWinM\n'
        w += imps + f'\nset_option Elab.async false\n\nnamespace {ns}.{sub}\n\nopen LeanVM.Guest.CoreMode\n\n'
        w += f'@[expose] public section\n\n'
        if i in splits:
            bl, ac = splits[i]
            m = len(ac) - 1
            sums = '[' + ', '.join(f'sum{i}_{t}' for t in range(m)) + ']'
            lst = ', '.join(f'({ac[t + 1]}, {lcnt(bl[ac[t + 1] - 1][2])})' for t in range(m))
            wins = ''.join(f'arms{i}_{t}, by omega,\n    ' for t in range(m))
            w += (f'/-- The join of statement {a}\'s arms. -/\ntheorem join{i} : joinOk ({blk}.drop {a}) {len(bl)} '
                  f'st{i} '
                  f'{sums}.flatten {lcnt(bl[-1][2])} st{i + 1} = true := by\n  decide +kernel\n\n')
            if loop:
                w += (f'/-- No `ret` in statement {a}. -/\ntheorem nr{i} : nrL (({blk}.drop {a}).take 1) = true := by\n'
                      f'  decide +kernel\n\n')
            w += (f'/-- Statement {a}, from {m} windows of its arms. -/\ntheorem win{i} : {wok} Fn.«{k}».pows sigW core '
                  f'hcert (({blk}.drop {a}).take ({b} - {a})) st{i} st{i + 1} = true :=\n'
                  f'  {wok}_of_arms (a := {a}) (ss := {sums}) (l := [{lst}]) join{i}{f" nr{i}" if loop else ""}\n'
                  f'    ⟨{wins}trivial⟩ rfl\n\nend\nend {ns}.{sub}\n')
        else:
            w += (f'/-- Statements {a} to {b - 1}. -/\ntheorem win{i} : {wok} Fn.«{k}».pows sigW '
                  f'core hcert (({blk}.drop {a}).take ({b} - {a})) st{i} st{i + 1} = true := {wprf(wok)}\n'
                  f'\nend\nend {ns}.{sub}\n')
        mods.append((f'W{i}', w))
    n = nw
    ok = HEADER(f'{base}.Ok', what=f'`{k}`\'s heap check, from its {n} windows.')
    ok += ''.join(f'public import {base}.W{i}\n' for i in range(n))
    if not loop:
        ok += f'public import LeanVM.Guest.CoreMode.HeapCWinF\n' + ('' if n else f'public import {base}.Cx\n')
    ok += f'\nset_option Elab.async false\n\nnamespace {ns}.{sub}\n\nopen LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
    if loop:
        lei = E.lidx(H.sig.term[0][1])
        ok += (f'/-- The parameters, the tail\'s shape, the entry state. -/\ntheorem head_ok : headOk Fn.«{k}».pows sigW core '
               f'hcert {lei} {cs[-1]} st0 = true := {wprf("headOk")}\n\n')
        ok += (f'/-- The tail call and the guarantees at `ret []`. -/\ntheorem tail_ok : tailOkW Fn.«{k}».pows sigW core hcert '
               f'{lei} st{n} = true := {wprf("tailOkW")}\n\n')
    else:
        ok += (f'/-- The parameters, the entry state. -/\ntheorem head_ok : headOkF Fn.«{k}».pows sigW core hcert st0 = '
               f'true := {wprf("headOkF")}\n\n')
        ok += (f'/-- Statements {cs[-2]} to the end. -/\ntheorem last_ok : lastOkF Fn.«{k}».pows sigW core hcert {cs[-2]} '
               f'st{n} = true := {wprf("lastOkF")}\n\n')
    ok += f'end\nend {ns}.{sub}\n\nnamespace {ns}\n\n@[expose] public section\n\n'
    lst = ', '.join(f'({cs[i]}, {sub}.st{i})' for i in range(1, n + 1))
    wins = ''.join(f'{sub}.win{i}, by omega,\n    ' for i in range(n))
    thm, last = ('heapOkC_of_wins', 'tail_ok') if loop else ('heapOkC_of_winsF', 'last_ok')
    one = '1' if gen.get('one') else ''
    if one:
        thm = thm.replace('heapOkC', 'heapOkC1')
    ok += (f'/-- `{k}`: the heap check, in {n} windows. -/\ntheorem {gen["final"]} : CoreMode.heapOkC{one} Fn.«{k}».pows\n'
           f'    {SIGW}\n    core hcert = true :=\n'
           f'  CoreMode.{thm} (l := [{lst}]) {sub}.head_ok\n    {f"⟨{wins}trivial⟩" if n else "trivial"} rfl '
           f'{sub}.{last}\n')
    ok += f'\nend\nend {ns}\n'
    mods.append(('Ok', ok))
    return mods


def one(k, H, sigOf, po, gen, budget=None):
    """The windowed modules of one function's certificate `H` at its callees' signatures `sigOf`: `[(name, text)]`."""
    sts, costs, P = states(k, H, sigOf)
    pre = region(k, H)
    na = [atoms(s) for s in pre]
    ents = [entries(x) for x in sts]
    # at least two pieces (a function's last part counts as one), each at most `WIN`
    tot = sum(costs)
    bud = min(budget or WIN, 1.15 * tot / max(2, -(-tot // (budget or WIN))))
    fixed = min(W_CERT * cert_size(H), FIXW)
    cs = cuts(costs, na, ents, bud - fixed)
    nw = len(cs) - 1 if is_loop(H) else len(cs) - 2
    w = [(sum(costs[cs[i]:cs[i + 1]]) + W_ENT * (ents[cs[i]] + ents[cs[i + 1]]) + fixed,
          sum(na[cs[i]:cs[i + 1]])) for i in range(len(cs) - 1)]
    # a window of one `match` over the budget: its arms in windows (`HeapCWinM`)
    splits = {}
    for i in range(nw):
        a = cs[i]
        if cs[i + 1] == a + 1 and pre[a][0] == 'match' and w[i][0] > (budget or WIN):
            bl = arm_blocks(P, pre[a], sts[a].copy())
            ac = cuts([b[3] for b in bl], [0] * len(bl), [0] * (len(bl) + 1), (budget or WIN) - fixed)
            splits[i] = (bl, ac)
            w[i] = (max(sum(b[3] for b in bl[ac[t]:ac[t + 1]]) + fixed for t in range(len(ac) - 1)), w[i][1])
    print(f'{k}: {len(pre)} statements, {sum(na)} atoms, estimated {sum(costs):.0f}k heartbeats; {nw} windows'
          f'{f" ({len(splits)} split by arms)" if splits else ""}, the largest {max(w)[0]:.0f}k '
          f'({max(x[1] for x in w)} atoms)')
    return emit(k, H, sts, cs, po, splits, gen)
