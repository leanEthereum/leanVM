"""The kernel's heap check of a function in windows (`CoreMode/HeapCWin.lean` for a loop helper, `HeapCWinF.lean`
otherwise): the one `decide` of `heapOkC` would run past the default heartbeats or the memory a module may take.

The certificate is `emitc.py`'s (`GenC/<pack>/Data.lean`, its `hcert`); `emitc.py` windows `KERNEL_WIN` and every
function whose check `fn_cost` estimates above `BUDGET` thousand heartbeats. The statements are cut between top-level
statements, each window estimated at most `WIN` and at most `ATOMS` atoms; a window that is one `match` and still over
`WIN` is checked by windows of its arms (`HeapCWinM.lean`). `heapc.py`'s pass (the check in Python, step for step)
gives the state at each cut, written as a literal (`Lits`: the tries as `.node`s, long subtrees and the lists'
unchanged parts shared with the previous state). The windows cover a loop helper's body without its tail
(`loopBody`), or a function's body before a last part that holds its first top-level `ret`. Per function, in
`GenCW/<fn>/` (not under `GenC/`, whose files `emitc.py` owns):

* `St.lean`: `sigW` (the callees' signatures, as `emitc.py` writes them); `S<i>.lean`: the state `st<i>` (importing
  `S<i-1>`, whose subtrees it shares);
* `W<i>.lean`: `win<i> : winOk Data.powTree sigW core hcert (((loopBody core).drop a).take (b - a)) st<i> st<i+1> =
  true` (`winOkF` over `core.body` for a function; one `decide +kernel`: no `ret` (a function's windows: no top-level
  one), no ghost value, the pass from one state to the next); for a `match` split by arms, `W<i>A<t>.lean` hold
  `arms<i>_<t> : armsOk ..` (the arms' summaries `sum<i>_<t>`) and `W<i>` the join (`joinOk`) and `win<i>` by
  `winOk_of_arms` (`winOkF_of_arms`);
* `Ok.lean`: `head_ok`, `tail_ok` (a function: `last_ok`, the statements from the last cut on) and
  `Fn.«fn».heap_okC : heapOkC Data.powTree sigOf core hcert = true` (the statement `emitc.py` writes for the other
  functions), by `heapOkC_of_wins` (`heapOkC_of_winsF`).

usage (from formal/lean_vm, `CORE_MODE_CACHE` set): python3 -I scripts/core-mode/heapwin.py [--fn NAME,..]
  [--budget N] [--out DIR] [--check] [--mods FILE]. `emitc.py` runs it for the functions it windows (`run`), so its
  `--check` and `--mods` cover these modules too.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
argv = list(sys.argv)
sys.argv = sys.argv[:1]
import infer as I
import heapc as C
import emitc as E

GUEST = os.path.normpath(os.path.join(HERE, '..', '..', 'LeanVM', 'Guest'))
FNS = ['main_loop2']
# atoms per window: the kernel's memory grows with the atoms a window's pass and ghost check go through; the default
# keeps a window of `main_loop2` within the 7.5 GB a module may take (measured: `m2-heap.md`)
ATOMS = 15000
# The kernel's work, in thousands of heartbeats (the heartbeat limit's unit), estimated from `heapc.py`'s pass: per
# line it executes (`Meter`), per atom (the ghost check), per character of the certificate (the context's tries), per
# frame run cell and top-level statement (`faOk`), per trie entry or list element of a window's states (comparing the
# end state). Fitted to the measured heartbeats of the 1532 one-piece checks and of the windows.
W_LINE, W_ATOM, W_CERT, W_FA, W_ENT = 0.2, 15, 0.02, 0.4, 0.5
# a check estimated above `BUDGET` is windowed, each window estimated at most `WIN` (the default limit is 200000)
BUDGET, WIN = 50000, 55000
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
    body = I.CORE[k][1]
    if is_loop(H):
        return body[:-2]
    r = next((i for i, s in enumerate(body) if s[0] == 'ret'), len(body))
    return body[:r]


def states(k, H, sigOf):
    """The check's pass (`heapc.heapOkC`) over the statements of `region`: `([S0, S1, ..], [cost0, ..])`, `S_i` the
    state before statement `i`, `cost_i` statement `i`'s estimated heartbeats."""
    params, body = I.CORE[k]
    G = H.sig
    m = len(params)
    X_ = C.X(dict(I.POWS), H, sigOf, params)
    P = C.Pass(X_, sigOf, body)
    assert list(params) == list(range(m)), 'params'
    if is_loop(H):
        assert len(G.term) == 1 and G.term[0][0] == ('val', 0), ('not a loop helper', G.term)
        assert not (G.retM or G.postV or G.retEq), 'loop with retM/postV/retEq'
        assert body[-1] == ('ret', []) and body[-2][0] == 'callIf', 'loop shape'
    assert all(v < C.GB for v in C.values(params, body)), 'noGhost'
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
    params, body = I.CORE[k]
    with Meter() as mt:
        C.heapOkC(dict(I.POWS), sigOf, k, params, body, H)
    return W_LINE * mt.n + W_ATOM * sum(map(atoms, body)) + fixed_cost(k, H)


def fixed_cost(k, H):
    """What every window pays (the context's tries) and the head (`faOk`)."""
    body = I.CORE[k][1]
    r = next((i for i, s in enumerate(body) if any(t[0] == 'ret' for t in C.stmts([s]))), len(body))
    return W_CERT * cert_size(H) + W_FA * len(H.fas) * r


def cert_size(H):
    aux, body = E.lcert(H)
    return len(body) + sum(map(len, aux))


def entries(st):
    """A state's size: its tries' entries and its lists' elements."""
    return (sum(len(getattr(st, f)) for f in ('env', 'sc', 'rs', 'ad', 'sv', 'src', 'pf', 'pr')) + len(st.eqs) +
            sum(1 + len(e[2]) + len(e[3]) + len(e[4]) + len(e[5]) for e in st.cd))


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


def lprun(r):
    return f'⟨{lcell(r[0])}, {r[1]}, {lcell(r[2])}, {lcell(r[3])}⟩'


def lnums(l):
    return '[' + ', '.join(map(str, l)) + ']'


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


SHARE = 300   # characters: a subtree longer is its own `def`, shared by every later state holding it


class Lits:
    """The literals of one function's states: subtrees and list tails shared across states (a state differs from
    the previous one in a few entries, so each `S<i>` elaborates only what is new; `S<i>` imports `S<i-1>`)."""

    def __init__(self):
        self.shared = {}
        self.cnt = 0
        self.prev = {}

    def ltrie(self, d, val, typ, defs):
        """The trie the pass holds for the entries `d` (`setF` at `Exec.indexDepth`; its shape depends only on the
        keys), as `.node`s, a subtree longer than `SHARE` a `def` (into `defs`, or an earlier state's). A literal
        costs the kernel nothing to build, where `insL` of the entries costs about as much as a window's pass."""
        t = None
        for k in sorted(d):
            t = tset(t, val(d[k]), DEPTH, k)

        def go(t):
            if t is None:
                return '.nil'
            v = 'none' if t[0] is None else f'(some {t[0]})'
            l, r = go(t[1]), go(t[2])
            sep = '\n    ' if len(l) + len(r) > 100 else ' '
            out = f'(.node {v}{sep}{l}{sep}{r})'
            if len(out) > SHARE:
                key = (typ, out)
                if key not in self.shared:
                    self.shared[key] = f'tr{self.cnt}'
                    self.cnt += 1
                    defs.append(f'noncomputable def {self.shared[key]} : Trie {typ} :=\n  {out}\n')
                return self.shared[key]
            return out
        return go(t)

    def llist(self, field, items, typ, name, defs, front):
        """A list growing at its end (`front` false: `cd`) or its front (`eqs`), as the previous state's plus what
        is new."""
        ax = E.Aux()
        p = self.prev.get(field)
        if p is not None and len(items) >= len(p[0]) and (
                items[:len(p[0])] == p[0] if not front else items[len(items) - len(p[0]):] == p[0]):
            new = items[len(p[0]):] if not front else items[:len(items) - len(p[0])]
            nl = ax.lst(f'{name}_', typ, new)
            text = f'{p[1]} ++ {nl}' if not front else f'{nl} ++ {p[1]}'
        else:
            text = ax.lst(f'{name}_', typ, items)
        defs += ax.defs
        defs.append(f'noncomputable def {name} : List {typ} := {text}\n')
        self.prev[field] = (items, name)
        return name

    def lstate(self, st, name):
        """A state's literal: `(aux defs, text)`."""
        cd = [f'⟨{lcell(mx)}, {j}, [{", ".join(map(lcell, cs))}], [{", ".join(map(lprun, rs))}], '
              f'[{", ".join(f"({lcell(p[0])}, {lnums(p[1])})" for p in ps)}], '
              f'[{", ".join(f"({lprun(p[0])}, {lnums(p[1])})" for p in prs)}]⟩'
              for mx, j, cs, rs, ps, prs in st.cd]
        eqs = [f'({lcell(a)}, {lcell(b)})' for a, b in st.eqs]
        pair = lambda p: f'({lcell(p[0])}, {lcell(p[1])})'
        defs = []
        fs = [self.ltrie(st.env, lcell, 'CCell', defs),
              self.ltrie(st.sc, lcell, 'CCell', defs),
              self.ltrie(st.rs, lprun, 'PRun', defs),
              self.ltrie(st.ad, pair, '(CCell × CCell)', defs),
              self.ltrie(st.sv, pair, '(CCell × CCell)', defs),
              self.ltrie(st.src, lcell, 'CCell', defs),
              self.ltrie(st.pf, lambda p: f"({lcell(p[0])}, {lnums(p[1])})", '(CCell × List ℕ)', defs),
              self.ltrie(st.pr, lambda p: f"({lprun(p[0])}, {lnums(p[1])})", '(PRun × List ℕ)', defs),
              f'{st.n}, {st.nr}, {st.nc}, {st.nt}',
              self.llist('cd', cd, 'CdE', f'{name}_cd', defs, False),
              self.llist('eqs', eqs, '(CCell × CCell)', f'{name}_eqs', defs, True)]
        return defs, '⟨' + ',\n    '.join(fs) + '⟩'


HEADER = '''/-
  LeanVM.Guest.CoreMode.GenCW.«{fn}».{mod}

  Generated by `scripts/core-mode/heapwin.py`; do not edit.
  {what}
-/

module

'''


def sig_lam(k, names):
    arms = ''.join(f'\n    | "{n}" => Fn.«{I.callee(n)}».hcert.sig' for n in sorted(names) if I.callee(n) in I.CORE)
    return f'(fun g ↦ match g with{arms}\n    | _ => .empty)' if arms else '(fun _ ↦ .empty)'


def emit_arms(k, i, a, split, blk, ns, base, imps):
    """The arm windows of window `i`, the `match` at statement `a`: `[(name, text)]`, module `W<i>A<t>` holding the
    summaries `sum<i>_<t>` of its arms and `arms<i>_<t> : armsOk ..`."""
    bl, ac = split
    out = []
    for t in range(len(ac) - 1):
        j, j2 = ac[t], ac[t + 1]
        c0 = f'(cntOf st{i})' if t == 0 else lcnt(bl[j - 1][2])
        ax = E.Aux()
        sums = ax.lst(f'sum{i}_{t}_', 'BlkSum', [lblk(b) for b in bl[j:j2]])
        x = HEADER.format(fn=k, mod=f'W{i}A{t}', what=f'Arms {j} to {j2 - 1} of statement {a} of `{k}`\'s heap check.')
        x += f'public import {base}.S{i}\npublic import LeanVM.Guest.CoreMode.HeapCWinM\n' + imps
        x += f'\nset_option maxRecDepth 100000\nset_option linter.all false\nset_option Elab.async false\n\n'
        x += f'namespace {ns}.HeapW\n\nopen LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
        x += ''.join(f'/-- Part of `sum{i}_{t}`. -/\n{d}\n' for d in ax.defs)
        x += f'/-- What the join reads of arms {j} to {j2 - 1}. -/\ndef sum{i}_{t} : List BlkSum := {sums}\n\n'
        x += (f'/-- Arms {j} to {j2 - 1}. -/\ntheorem arms{i}_{t} : armsOk Data.powTree sigW core hcert '
              f'({blk}.drop {a}) '
              f'{j} ({j2} - {j}) st{i} {c0} sum{i}_{t} {lcnt(bl[j2 - 1][2])} = true := by\n  decide +kernel\n\n')
        x += f'end\nend {ns}.HeapW\n'
        out.append((f'W{i}A{t}', x))
    return out


def emit(k, H, sts, cs, names, po, splits={}):
    """The modules of one function: `[(name, text)]`."""
    pack, core_mod = po[k][0], po[k][1]
    cal = sorted({I.callee(n) for n in names} & set(I.CORE))
    data = sorted({f'LeanVM.Guest.CoreMode.GenC.«{po[c][0]}».Data' for c in cal + [k]})
    ns = f'LeanVM.Guest.Fn.«{k}»'
    base = f'LeanVM.Guest.CoreMode.GenCW.«{k}»'
    mods = []
    loop = is_loop(H)
    nw = len(cs) - 1 if loop else len(cs) - 2      # a function's last chunk is `lastOkF`'s
    st = HEADER.format(fn=k, mod='St', what=f'The callees\' signatures for `{k}`\'s windowed heap check.')
    st += (f'public import LeanVM.Guest.CoreMode.HeapCWin{"" if loop else "F"}\n' +
           ''.join(f'public import {m}\n' for m in data))
    st += f'\nset_option linter.all false\n\nnamespace {ns}.HeapW\n\n'
    st += 'open LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
    st += f'/-- The callees\' signatures. -/\nnoncomputable def sigW : String → CoreMode.HSig := {sig_lam(k, names)}\n'
    st += f'\nend\nend {ns}.HeapW\n'
    mods.append(('St', st))
    # one module per state, each importing the previous one, whose subtrees it shares (`Lits`)
    lits = Lits()
    for i, a in enumerate(cs[:nw + 1]):
        aux, text = lits.lstate(sts[a], f'st{i}')
        si = HEADER.format(fn=k, mod=f'S{i}', what=f'The state before statement {a} of `{k}`\'s windowed heap check.')
        si += f'public import {base}.{"S" + str(i - 1) if i else "St"}\n\nset_option maxRecDepth 100000\n'
        si += 'set_option linter.all false\n\n'
        si += (f'namespace {ns}.HeapW\n\nopen LeanVM.Guest.CoreMode\nopen LeanVM.Guest.Exec (Trie)\n\n'
               f'@[expose] public section\n')
        si += ''.join(f'\n{d}' for d in aux)
        si += f'\n/-- The state before statement {a}. -/\nnoncomputable def st{i} : CSt := {text}\n'
        si += f'\nend\nend {ns}.HeapW\n'
        mods.append((f'S{i}', si))
    imps = (f'public import LeanVM.Guest.Data.Pows\npublic import LeanVM.Guest.Pack.«{pack}».{core_mod}\n')
    blk, wok = ('(Memory.loopBody core)', 'winOk') if loop else ('core.body', 'winOkF')
    for i in range(nw):
        a, b = cs[i], cs[i + 1]
        w = HEADER.format(fn=k, mod=f'W{i}', what=f'Window {i} of `{k}`\'s heap check: statements {a} to {b - 1}.')
        w += f'public import {base}.S{i}\npublic import {base}.S{i + 1}\n'
        if i in splits:
            amods = emit_arms(k, i, a, splits[i], blk, ns, base, imps)
            mods += amods
            w += ''.join(f'public import {base}.{nm}\n' for nm, _ in amods)
            w += f'public import LeanVM.Guest.CoreMode.HeapCWinM\n'
        w += imps + f'\nset_option Elab.async false\n\nnamespace {ns}.HeapW\n\nopen LeanVM.Guest.CoreMode\n\n'
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
            w += (f'/-- Statement {a}, from {m} windows of its arms. -/\ntheorem win{i} : {wok} Data.powTree sigW core '
                  f'hcert (({blk}.drop {a}).take ({b} - {a})) st{i} st{i + 1} = true :=\n'
                  f'  {wok}_of_arms (a := {a}) (ss := {sums}) (l := [{lst}]) join{i}{f" nr{i}" if loop else ""}\n'
                  f'    ⟨{wins}trivial⟩ rfl\n\nend\nend {ns}.HeapW\n')
        else:
            w += (f'/-- Statements {a} to {b - 1}. -/\ntheorem win{i} : {wok} Data.powTree sigW '
                  f'core hcert (({blk}.drop {a}).take ({b} - {a})) st{i} st{i + 1} = true := by\n'
                  f'  decide +kernel\n\nend\nend {ns}.HeapW\n')
        mods.append((f'W{i}', w))
    n = nw
    ok = HEADER.format(fn=k, mod='Ok', what=f'`{k}`\'s heap check, from its {n} windows.')
    ok += ''.join(f'public import {base}.W{i}\n' for i in range(n))
    if not loop:
        ok += f'public import LeanVM.Guest.CoreMode.HeapCWinF\n' + ('' if n else f'public import {base}.S0\n' + imps)
    ok += f'\nset_option Elab.async false\n\nnamespace {ns}.HeapW\n\nopen LeanVM.Guest.CoreMode\n\n@[expose] public section\n\n'
    if loop:
        lei = E.lidx(H.sig.term[0][1])
        ok += (f'/-- The parameters, the tail\'s shape, the entry state. -/\ntheorem head_ok : headOk Data.powTree sigW core '
               f'hcert {lei} {cs[-1]} st0 = true := by\n  decide +kernel\n\n')
        ok += (f'/-- The tail call and the guarantees at `ret []`. -/\ntheorem tail_ok : tailOk Data.powTree sigW core hcert '
               f'{lei} st{n} = true := by\n  decide +kernel\n\n')
    else:
        ok += (f'/-- The parameters, the entry state. -/\ntheorem head_ok : headOkF Data.powTree sigW core hcert st0 = '
               f'true := by\n  decide +kernel\n\n')
        ok += (f'/-- Statements {cs[-2]} to the end. -/\ntheorem last_ok : lastOkF Data.powTree sigW core hcert {cs[-2]} '
               f'st{n} = true := by\n  decide +kernel\n\n')
    ok += f'end\nend {ns}.HeapW\n\nnamespace {ns}\n\n@[expose] public section\n\n'
    lst = ', '.join(f'({cs[i]}, HeapW.st{i})' for i in range(1, n + 1))
    wins = ''.join(f'HeapW.win{i}, by omega,\n    ' for i in range(n))
    thm, last = ('heapOkC_of_wins', 'tail_ok') if loop else ('heapOkC_of_winsF', 'last_ok')
    ok += (f'/-- `{k}`: the heap check, in {n} windows. -/\ntheorem heap_okC : CoreMode.heapOkC Data.powTree\n'
           f'    {sig_lam(k, names)}\n    core hcert = true :=\n'
           f'  CoreMode.{thm} (l := [{lst}]) HeapW.head_ok\n    {f"⟨{wins}trivial⟩" if n else "trivial"} rfl '
           f'HeapW.{last}\n')
    ok += f'\nend\nend {ns}\n'
    mods.append(('Ok', ok))
    return mods


def run(res, built, fns, out, budget=None, check=False):
    """The windowed modules of `fns` from `emitc.build`'s result `built`, written under `out` (or compared, `check`):
    `(modules, stale paths)`. `emitc.py` calls this for its `KERNEL_WIN` functions."""
    sigs, certs, why, drops, stmt_names, stats = built
    po = E.pack_of()
    stale, mods = [], []
    for k in fns:
        if k in why:
            sys.exit(f'{k}: the Python check fails: {why[k][:3]}')
        H = certs[k]
        sts, costs, P = states(k, H, lambda g: sigs.get(I.callee(g), C.EMPTY))
        pre = region(k, H)
        na = [atoms(s) for s in pre]
        ents = [entries(x) for x in sts]
        # at least two pieces (a function's last part counts as one), each at most `WIN`
        tot = sum(costs)
        bud = min(budget or WIN, 1.15 * tot / max(2, -(-tot // (budget or WIN))))
        cs = cuts(costs, na, ents, bud - W_CERT * cert_size(H))
        nw = len(cs) - 1 if is_loop(H) else len(cs) - 2
        fixed = W_CERT * cert_size(H)
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
        for name, text in emit(k, H, sts, cs, stmt_names[k], po, splits):
            path = os.path.join(out, k, name + '.lean')
            mods.append(f'LeanVM.Guest.CoreMode.GenCW.«{k}».{name}')
            if check:
                if not os.path.exists(path) or open(path, encoding='utf-8').read() != text:
                    stale.append(path)
            else:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, 'w', encoding='utf-8') as fh:
                    fh.write(text)
    return mods, stale


def main():
    fns = argv[argv.index('--fn') + 1].split(',') if '--fn' in argv else FNS
    budget = int(argv[argv.index('--budget') + 1]) if '--budget' in argv else None
    out = argv[argv.index('--out') + 1] if '--out' in argv else os.path.join(GUEST, 'CoreMode', 'GenCW')
    I.F.difference_update(E.OFF)
    I.set_features(argv)
    res, dt = I.run_all()
    print(f'inferred {len(res)} functions in {dt:.1f} s')
    mods, stale = run(res, E.build(res, set(fns)), fns, out, budget, '--check' in argv)
    if '--mods' in argv:
        with open(argv[argv.index('--mods') + 1], 'w') as fh:
            fh.write('\n'.join(mods) + '\n')
    if '--check' in argv:
        print('checked: ' + (f'{len(stale)} stale: {stale[:5]}' if stale else 'up to date'))
        if stale:
            sys.exit(1)


if __name__ == '__main__':
    main()
