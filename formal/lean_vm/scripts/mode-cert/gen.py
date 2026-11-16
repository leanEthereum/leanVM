"""Writes the mode walk's certificates into each pack: `Pack/*/ModeSig.lean`, every function's
signature (`Mode.Sig`), and `Pack/*/Mode{k}.lean`, every passing function's hints, residuals and
table sizes (`Mode.Fun`) with the kernel's check of its walk (`Mode.walk`, `Guest/Mode/Abs.lean`).
A function whose check is estimated to need more than `KBUDGET` of the kernel's memory
(`kprofile`) is checked in windows (`Guest/Mode/Win.lean`): its data in `ModeD{k}`, the snapshots at
its cuts in `ModeD{k}S{j}`, each window's check in `ModeD{k}W{m}`, their chain in `ModeL{k}`. Hints
too long to check in one piece are checked in parts (`ModeH{q}P{m}`, `Guest/Mode/HintsSplit.lean`). The signatures and residuals are `infer.py`'s, the snapshots `walk.py`'s states.
`--check` writes nothing and fails when a file differs. `MODE_CERT_CACHE=FILE` keeps the inference
in `FILE` between runs (development only: stale once the walk, the inference or the guest changes).
Usage: python3 -I scripts/mode-cert/gen.py [--check] [--only PACK...]"""
import sys, os, collections, textwrap
sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import infer as I
import walk as W
from walk import Fail

PACKS = os.path.join(I.data.ROOT, 'Pack')
# a module's checks, at most this many instructions
CHUNK = 2500
# a literal list longer than this is written as a flattened list of such lists
LONG = 16
# The kernel's memory on a check, estimated in MB (`kprofile`): `KBASE` a module, `KINS` an
# instruction, `KRUN` a run a lookup tries (`Abs.inRuns`) per base of the cell, `KARM` a call's arm and
# `KADD` each fact it adds to the state before the call (the arms are met by what they add: the state
# before is a tail they share), `KSIZE` a fact of the snapshot a window ends at (its cut's check). A
# module is sized to at most `KBUDGET`; a function one of whose instructions alone needs more than
# `KHARD` is not checked (`HEAVY`). `KHARD` is set from the kernel's measured peak on table calls, a
# margin below the 8 GB a check may take.
KBASE = 400
KINS = 1.5
KRUN = 0.01
KARM = 105
KADD = 1.6
KSIZE = 0.75
KBUDGET = 4500
KHARD = 12500
# a module's snapshots hold at most this many facts in all (the elaborator's memory)
SNAPMAX = 20000
# a snapshot whose literal is longer than this many characters is written as a def per state, each
# list longer than `SNAPCH` as defs of that many (the elaborator's heartbeats per def)
SNAPLIT = 400000
SNAPCH = 256
# a long function's windows are chained in links of this many
LINK = 32
# a function's hints are checked in parts of at most this many offsets
HPART = 25000


def checkable(n, fails): return n not in fails and n not in HEAVY


def nat(n): return str(n)


def base(b): return '(.fr %d)' % b[1] if b[0] == 'fr' else '(.hp %d %d)' % (b[1], b[2])


def mono(m): return '⟨%d, %d, [%s]⟩' % (m[0], m[1], ', '.join('(%s, %d)' % (base(b), e) for b, e in m[2]))


def idx(i): return '(.num %d)' % i[1] if i[0] == 'num' else '(.ex %s %d)' % (base(i[1]), i[2])


def rng(r): return '⟨%s, %s, %s, %d, %d⟩' % (mono(r[0]), idx(r[1]), idx(r[2]), r[3], r[4])


def lst(xs, f):
    xs = list(xs)
    if len(xs) <= LONG: return '[%s]' % ', '.join(f(x) for x in xs)
    parts = [xs[i:i + LONG] for i in range(0, len(xs), LONG)]
    def tree(ps):
        if len(ps) == 1: return '[%s]' % ', '.join(f(x) for x in ps[0])
        step = LONG
        while len(ps) > step * LONG: step *= LONG
        groups = [ps[i:i + step] for i in range(0, len(ps), step)] if len(ps) > LONG else [[p] for p in ps]
        return '(List.flatten [%s])' % ', '.join(tree(g) for g in groups)
    return tree(parts)


def ptr(q): return '(%s, %s)' % (rng(q[0]), lst(q[1], nat))


def sig(s):
    return '⟨%d, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s⟩' % (
        s.pc, lst(s.entry, nat), 'none' if s.self_ is None else '(some %d)' % s.self_, lst(s.pre, mono),
        lst(s.preR, rng), lst(s.term, lambda p: '(%s, %s)' % (idx(p[0]), idx(p[1]))), lst(s.ret, nat),
        lst(s.post, mono), lst(s.postR, rng), lst(s.postL, rng), lst(s.preP, ptr), lst(s.postP, ptr),
        lst(s.postLP, ptr), lst(s.retV, lambda p: '(%d, %s)' % (p[0], mono(p[1]))))


def dest(d): return '(.stack %d)' % d[1] if d[0] == 's' else '(.heap %d)' % d[1]


def strlit(t): return '"%s"' % t


def hint(h):
    t = h[0]
    if t == 'fa': return '(.frameAddress %d)' % h[1]
    if t == 'af': return '(.allocFrames %d %d %d (LeanVM.Parameters.K.ofBits 0x%s) %d)' % (h[1], h[2], h[3], h[4], h[5])
    if t == 'al': return '(.alloc %d %d)' % (h[1], h[2])
    if t == 'ad': return '(.allocDyn %d %d)' % (h[1], h[2])
    if t == 'av': return '(.allocAdvice %d %s)' % (h[1], strlit(h[2]))
    if t == 'lt': return '(.allocLate %d (.%s %d))' % (h[1], 'cells' if h[2] == 'c' else 'exp', h[3])
    if t == 'aa': return '(.allocArm %d %d %s)' % (h[1], h[2], lst(h[3], nat))
    if t == 'ca': return '(.cellAddress %d %d)' % (h[1], h[2])
    if t == 'ws': return '(.witnessStack %s %d %d)' % (strlit(h[1]), h[2], h[3])
    if t == 'wh': return '(.witnessHeap %s %d %d %d)' % (strlit(h[1]), h[2], h[3], h[4])
    if t == 'lc': return '(.log2Ceil %s %d %d %d)' % (dest(h[1]), h[2], h[3], h[4])
    if t == 'bd': return '(.bitDecompose %d %s %d)' % (h[1], dest(h[2]), h[3])
    if t == 'be': return '(.bitDecomposeExp %d %s %d)' % (h[1], dest(h[2]), h[3])
    if t == 'dd':
        return '(.digitDecomposeExp %d %s %d %d %d %d %s)' % (h[1], dest(h[2]), h[3], h[4], h[5], h[6],
                                                              'none' if h[7] == '-' else '(some %s)' % h[7])
    if t == 'we': return '(.windowsExp %d %s %d %d %d %d)' % (h[1], dest(h[2]), h[3], h[4], h[5], h[6])
    if t == 'fl': return '(.fieldLimbs %d %d %d)' % (h[1], h[2], h[3])
    if t == 'iv': return '(.inverse %d %d)' % (h[1], h[2])
    raise Exception(h)


def res(r):
    if r[0] == 'lt': return '(.lt %s %s)' % (idx(r[1]), idx(r[2]))
    if r[0] == 'sub': return '(.sub %s %s)' % (rng(r[1]), lst(r[2], rng))
    if r[0] == 'name': return '(.name %d)' % r[1]
    return '(.nz %d)' % r[1]


def trie(entries, val):
    """A literal `Exec.Trie`: key `0` at the root, `2m+1` at key `m` of the left child, `2m+2` at the
    right one's."""
    def build(es):
        if not es: return '.nil'
        here = None; left = []; right = []
        for k, v in es:
            if k == 0: here = v
            elif k % 2 == 1: left.append((k // 2, v))
            else: right.append((k // 2 - 1, v))
        return '(.node %s %s %s)' % ('none' if here is None else '(some %s)' % val(here), build(left), build(right))
    return build(sorted(entries.items()))


# a literal trie's subtree longer than this is a definition of its own
BIG = 40000


def bigTrie(name, typ, entries, val, defs):
    """`trie`, each subtree longer than `BIG` a definition `{name}{k}` of its own, written to `defs`."""
    def build(es):
        if not es: return '.nil'
        here = None; left = []; right = []
        for k, v in es:
            if k == 0: here = v
            elif k % 2 == 1: left.append((k // 2, v))
            else: right.append((k // 2 - 1, v))
        t = '(.node %s %s %s)' % ('none' if here is None else '(some %s)' % val(here), build(left), build(right))
        if len(t) > BIG:
            d = '%s%d' % (name, len(defs))
            defs.append('noncomputable def %s : Exec.Trie (%s) :=\n  %s\n\n' % (d, typ, t))
            return d
        return t
    return build(sorted(entries.items()))


def wrap(text, width=100):
    """Long lines broken at spaces (no generated string literal holds one), the rest indented: Lean's
    positions are slow to compute on very long lines."""
    out = []
    for line in text.split('\n'):
        while len(line) > width:
            k = line.rfind(' ', 0, width)
            if k <= 4: k = line.find(' ', width)
            if k < 0: break
            out.append(line[:k]); line = '    ' + line[k + 1:]
        out.append(line)
    return '\n'.join(out)


def header(mod, what):
    return '/-\n  %s\n\n  Generated by `scripts/mode-cert/gen.py`; do not edit.\n  %s\n-/\n\nmodule\n\n' % (mod, what)


def fnq(n): return 'Fn.«%s»' % I.fns[n]['ns']


def packs():
    by = collections.defaultdict(list)
    for n, f in I.fns.items(): by[f['pack']].append(n)
    return {p: sorted(ns, key=lambda n: I.fns[n]['entry']) for p, ns in by.items()}


def termFr(G):
    """Each termination fact reads entry cells or constants (`Mode.termFr`)."""
    ok = lambda i: i[0] == 'num' or (i[1][0] == 'fr' and i[1][1] in G.entry)
    return all(ok(p) and ok(q) for p, q in G.term)


def sigFile(p, ns, sigs):
    out = [header('LeanVM.Guest.Pack.«%s».ModeSig' % p, 'What a caller knows of compiled functions, for the mode walk.')]
    out.append('public import LeanVM.Guest.Mode.Abs\n')
    for n in ns:
        out.append('\nnamespace LeanVM.Guest.Fn.«%s»\n\n@[expose] public section\n\n' % I.fns[n]['ns'])
        out.append('/-- `%s`: its entry, the cells and heap facts it needs at entry and guarantees at return. -/\n' % n)
        assert termFr(sigs[n]), n
        out.append('noncomputable def modeSig : Mode.Sig :=\n  %s\n\n' % sig(sigs[n]))
        out.append('theorem modeSig_termFr : Mode.termFr modeSig = true := by decide +kernel\n\nend\n\nend LeanVM.Guest.Fn.«%s»\n' % I.fns[n]['ns'])
    return ''.join(out)


def calleesOf(n): return sorted(I.calls[n])


def unit(_): return '()'


def val(x):
    if x[0] == 'm': return '(.m %s)' % mono(x[1])
    if x[0] == 'imm': return '(.imm %d %d)' % (x[1], x[2])
    return '(.tab %s %d)' % (base(x[1]), x[2])


def absLit(A):
    """A state of `walk.py` as a literal `Mode.Abs`."""
    return '⟨%s⟩' % ', '.join([
        trie({o: 1 for o in A.w}, unit), trie(A.v, val), trie({o: 1 for o in A.nz}, unit),
        lst(sorted(A.hv.items()), lambda p: '(%s, %s)' % (mono(p[0]), val(p[1]))), lst(sorted(A.h), mono),
        lst(sorted(A.r), rng), lst(sorted(A.lt), lambda p: '(%s, %s)' % (idx(p[0]), idx(p[1]))),
        lst(A.pr, lambda t: '(%d, %d, %d)' % t), trie(A.xs, lambda p: '(%d, %d)' % p), lst(sorted(A.p), ptr),
        lst(sorted(A.c.items()), cnd)])


def cnd(kv):
    """A conditional fact of `walk.py` as a literal `Mode.Cnd`."""
    (x, j), (h, r, p, lt, hv) = kv
    return '⟨%s, %d, %s, %s, %s, %s, %s⟩' % (base(x), j, lst(sorted(h), mono), lst(sorted(r), rng),
        lst(sorted(p), ptr), lst(sorted(lt), lambda q: '(%s, %s)' % (idx(q[0]), idx(q[1]))),
        lst(sorted(hv.items()), lambda q: '(%s, %s)' % (mono(q[0]), val(q[1]))))


def snapLit(S):
    cur, pend = S
    return '(%s, %s)' % (lst(cur, absLit), lst(pend, lambda g: '⟨%s, %s, %s⟩' % (
        lst(g[0], nat), lst(g[1], absLit), 'true' if g[2] else 'false')))


def imports(p, ns):
    imps = {'LeanVM.Guest.Mode.Abs', 'LeanVM.Guest.Data.Pows', 'LeanVM.Guest.Pack.«%s».Bundle' % p,
            'LeanVM.Guest.Pack.«%s».ModeSig' % p}
    for n in ns:
        for m in calleesOf(n): imps.add('LeanVM.Guest.Pack.«%s».ModeSig' % I.fns[m]['pack'])
    return imps


def importLines(imps): return ''.join('public import %s\n' % i for i in sorted(imps))


def nsOpen(n, expose=True):
    return '\nnamespace LeanVM.Guest.Fn.«%s»\n\nopen LeanVM.Guest LeanVM.Guest.Exec\n\n%spublic section\n\n' % (
        I.fns[n]['ns'], '@[expose] ' if expose else '')


def nsClose(n): return 'end\n\nend LeanVM.Guest.Fn.«%s»\n' % I.fns[n]['ns']


def absSplit(A, name, defs):
    """`absLit`, each list longer than `SNAPCH` written as defs of `SNAPCH` elements named `name`."""
    def part(xs, f, ty, fld):
        xs = list(xs)
        if len(xs) <= SNAPCH: return lst(xs, f)
        ns = []
        for j in range(0, len(xs), SNAPCH):
            ns.append('%s%s%d' % (name, fld, j // SNAPCH))
            defs.append('noncomputable def %s : %s :=\n  %s\n\n' % (ns[-1], ty, lst(xs[j:j + SNAPCH], f)))
        return '(List.flatten %s)' % lst(ns, str)
    return '⟨%s⟩' % ', '.join([
        trie({o: 1 for o in A.w}, unit), trie(A.v, val), trie({o: 1 for o in A.nz}, unit),
        part(sorted(A.hv.items()), lambda p: '(%s, %s)' % (mono(p[0]), val(p[1])), 'List (Mode.Mono × Mode.Val)', 'hv'),
        part(sorted(A.h), mono, 'List Mode.Mono', 'h'), part(sorted(A.r), rng, 'List Mode.Rng', 'r'),
        part(sorted(A.lt), lambda p: '(%s, %s)' % (idx(p[0]), idx(p[1])), 'List (Mode.Idx × Mode.Idx)', 'lt'),
        lst(A.pr, lambda t: '(%d, %d, %d)' % t), trie(A.xs, lambda p: '(%d, %d)' % p),
        part(sorted(A.p), ptr, 'List (Mode.Rng × List ℕ)', 'p'), part(sorted(A.c.items()), cnd, 'List Mode.Cnd', 'c')])


def snapDef(n, b, S):
    """The snapshot `snap{b}`; one too long for the elaborator to take as one literal (`SNAPLIT`), as a
    def per state and per part of its long lists."""
    text = snapLit(S)
    doc = '/-- `%s`: the paths and pending edges at its cut at offset %d. -/\n' % (n, b)
    if len(text) <= SNAPLIT:
        return doc + 'noncomputable def snap%d : List Mode.Abs × Mode.Pend :=\n  %s\n\n' % (b, text)
    cur, pend = S
    defs = []
    def st(A, nm):
        defs.append('noncomputable def %s : Mode.Abs :=\n  %s\n\n' % (nm, absSplit(A, nm + '_', defs)))
        return nm
    cs = [st(A, 'snap%da%d' % (b, i)) for i, A in enumerate(cur)]
    ps = ['⟨%s, %s, %s⟩' % (lst(g[0], nat), lst([st(B, 'snap%dp%d_%d' % (b, k, i)) for i, B in enumerate(g[1])], str),
          'true' if g[2] else 'false') for k, g in enumerate(pend)]
    return ''.join(defs) + doc + 'noncomputable def snap%d : List Mode.Abs × Mode.Pend :=\n  (%s, %s)\n\n' % (
        b, lst(cs, str), lst(ps, str))


def snapDefs(n, cuts):
    """The snapshots `snap{b}` at a function's cuts."""
    return ''.join(snapDef(n, b, S) for b, S in sorted(cuts.items()))


def dataDefs(n, res, cuts=None, inline=True):
    """`modeEnv` and `modeFun`, its cuts' snapshots `snap{b}` named in `modeFun`'s trie (defined here when
    `inline`)."""
    f = I.fns[n]
    sigt = {I.fns[m]['entry']: m for m in calleesOf(n)}
    env = '⟨Data.powTree, Data.jtTrie, %d, %d, %s, %d⟩' % (
        I.JT_LO, I.JT_HI, trie(sigt, lambda m: '%s.modeSig' % fnq(m)), I.HALT)
    hs = {i: h for i, h in f['hints'].items() if h}
    rs = {i: r for i, r in res.get(n, {}).items() if r}
    defs = []
    fun = '⟨%d, %d, %s.modeSig, %s, %s, %s, %s, %s⟩' % (
        f['entry'], f['count'], fnq(n), bigTrie('modeHints', 'List LeanVM.Prover.Exec.Hint', hs, lambda l: lst(l, hint), defs),
        bigTrie('modeRes', 'List Mode.Res', rs, lambda l: lst(l, res_), defs),
        bigTrie('modeTabs', 'ℕ', f['tabs'], nat, defs), 'true' if n == 'main' else 'false',
        trie({b: b for b in cuts}, lambda b: 'snap%d' % b) if cuts else '.nil')
    out = defs
    if inline and cuts: out.append(snapDefs(n, cuts))
    out.append('/-- `%s`: the program its walk shares. -/\nnoncomputable def modeEnv : Mode.Env :=\n  %s\n\n' % (n, env))
    out.append('/-- `%s`: its hints, residuals, table sizes and cuts. -/\nnoncomputable def modeFun : Mode.Fun :=\n  %s\n\n' % (n, fun))
    return ''.join(out)


def checkFile(p, k, group, sigs, res):
    mod = 'LeanVM.Guest.Pack.«%s».Mode%d' % (p, k)
    out = [header(mod, "The kernel's checks of compiled functions' mode walks, over their data and their callees' signatures.")]
    out.append(importLines(imports(p, group)))
    out.append('\nset_option Elab.async false\n')
    for n in group:
        out.append(nsOpen(n))
        out.append(dataDefs(n, res))
        out.append('/-- `%s`: its mode walk accepts its code. -/\ntheorem modeOk : Mode.walk modeEnv modeFun code.chunks.flatten = true := by\n  decide +kernel\n\n' % n)
        out.append(nsClose(n))
    return ''.join(out)


def facts(A):
    """A state's facts held in lists, as a snapshot's size."""
    return len(A.r) + len(A.h) + len(A.hv) + len(A.lt) + len(A.p)


def kprofile(n, sig, res):
    """At each offset of a function's walk: the facts of the paths and pending edges there (`S`), and the
    kernel's memory its instruction is estimated to need (`C`, MB): `KINS`, and `KRUN` for each run a
    lookup tries and each base of the cell (`Abs.inRuns` tries the runs over `k`'s bases or all but one
    of them, a miss each, a hit half of them on average; none for a run of one point that is the cell,
    which `ptKey` finds at once), and for each arm of a call `KARM` and `KADD` for each fact it adds."""
    f = I.fns[n]; N = f['count']
    S = [0] * (N + 1); C = [KINS] * N; cur = [0]
    och = W.Abs.coveredHR
    def coveredHR(A, k):
        if k not in A.h:
            keys = {(k[0], k[2])} | {(k[0], tuple(q for q in k[2] if q[0] != e[0])) for e in k[2]}
            c = [r for r in A.r if (r[0][0], r[0][2]) in keys]
            if not any(onePt(r) == k for r in c):
                C[cur[0]] += KRUN * (1 + len(k[2])) * (len(c) / 2 if any(A.inRng(k, r) for r in c) else len(c))
        return och(A, k)
    def probe(i, sts, pend):
        cur[0] = i
        S[i] = sum(facts(A) for A in list(sts) + [B for g in pend for B in g[1]])
    oac = I.Walk.afterCall
    def afterCall(w, A, *a):
        B = oac(w, A, *a)
        C[cur[0]] += KARM + KADD * max(0, facts(B) - facts(A))
        return B
    W.Abs.coveredHR = coveredHR; I.Walk.afterCall = afterCall
    try:
        I.Walk(I.E, f['entry'], N, sig, f['hints'], res, f['tabs'], main=n == 'main').run(f['ops'], probe=probe)
    finally:
        W.Abs.coveredHR = och; I.Walk.afterCall = oac
    return S, C


def onePt(r):
    """A run's cell, if it is one point between constants (`ptKey`: `Abs.inRuns` finds it at once)."""
    q, lo, hi, S, d = r
    if lo[0] == 'num' and hi[0] == 'num' and hi[1] == lo[1] + 1: return W.shift(q, S * lo[1] + d)
    return None


class Heavy(Exception):
    pass


def cutsAt(S, C):
    """A function's cuts: each window from the previous cut is at most `KBUDGET` with its end cut's
    check, cut where the fewest facts are pending among the later half of the offsets it may end at; a
    single instruction at most `KHARD` (else `Heavy`)."""
    N = len(C); cuts = []; a = 0
    while KBASE + sum(C[a:]) > KBUDGET:
        acc = KBASE; cand = []
        for b in range(a + 1, N):
            acc += C[b - 1]
            if acc > KBUDGET: break
            if acc + KSIZE * S[b] <= KBUDGET: cand.append(b)
        if cand:
            lo = cand[len(cand) // 2]
            b = min((x for x in cand if x >= lo), key=lambda x: (S[x], -x))
        else:
            b = a + 1
            if KBASE + C[a] + (KSIZE * S[b] if b < N else 0) > KHARD: raise Heavy(a)
            if b == N: break
        cuts.append(b); a = b
    return cuts


def cutsOf(n, sig, res, cuts):
    """The paths and pending edges at a function's cuts."""
    f = I.fns[n]
    snaps = {}
    def rec(i, cur, pend):
        if i in cuts:
            snaps[i] = ([A.copy() for A in cur], [(list(ts), [B.copy() for B in Bs], m) for ts, Bs, m in pend])
    I.Walk(I.E, f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main').run(f['ops'], probe=rec)
    return snaps


def winFiles(p, k, n, sigs, res, cuts):
    """A long function's data (`ModeD{k}`), the snapshots at its cuts (`ModeD{k}S{j}`, at most `SNAPMAX`
    facts each), each window's check (`ModeD{k}W{m}`) and their chain (`ModeL{k}`)."""
    f = I.fns[n]
    snaps = cutsOf(n, sigs[n], res.get(n, {}), cuts)
    bs = sorted(snaps)
    base_ = 'LeanVM.Guest.Pack.«%s».ModeD%d' % (p, k)
    files = {}
    groups = []; size = SNAPMAX
    for b in bs:
        z = sum(facts(A) for A in snaps[b][0]) + sum(facts(B) for g in snaps[b][1] for B in g[1])
        if size + z > SNAPMAX: groups.append([]); size = 0
        groups[-1].append(b); size += z
    for j, g in enumerate(groups):
        out = [header('%sS%d' % (base_, j), "Snapshots at a long compiled function's cuts, for its mode walk.")]
        out.append('public import LeanVM.Guest.Mode.Abs\n')
        out.append(nsOpen(n))
        out.append(snapDefs(n, {b: snaps[b] for b in g}))
        out.append(nsClose(n))
        files['ModeD%dS%d.lean' % (k, j)] = ''.join(out)
    out = [header(base_, "A long compiled function's mode walk data, its cuts' snapshots named.")]
    out.append(importLines(imports(p, [n]) | {'LeanVM.Guest.Mode.Win'} | {'%sS%d' % (base_, j) for j in range(len(groups))}))
    out.append(nsOpen(n))
    out.append(dataDefs(n, res, snaps, inline=False))
    out.append(nsClose(n))
    files['ModeD%d.lean' % k] = ''.join(out)
    starts = [0] + bs
    for m, a in enumerate(starts):
        mod = '%sW%d' % (base_, m)
        out = [header(mod, "The kernel's check of one window of a long compiled function's mode walk.")]
        out.append('public import %s\n' % base_)
        out.append('\nset_option Elab.async false\n')
        out.append(nsOpen(n, False))
        st = '[Mode.entryAbs modeEnv modeFun.sig] []' if a == 0 else '(Mode.cutOf modeFun %d).1 (Mode.cutOf modeFun %d).2' % (a, a)
        if m + 1 < len(starts):
            b = starts[m + 1]
            out.append('/-- `%s`: its walk from offset %d goes through to its cut at %d. -/\ntheorem modeW%d :\n    (Mode.runCode modeEnv modeFun (Mode.winCode code.chunks %d %d) %d %s).isSome = true := by\n  decide +kernel\n\n' % (n, a, b, m, a, b, a, st))
        else:
            sa = '([Mode.entryAbs modeEnv modeFun.sig], [])' if a == 0 else '(Mode.cutOf modeFun %d)' % a
            out.append('/-- `%s`: its walk from offset %d goes through to its end. -/\ntheorem modeW%d :\n    Mode.runRest modeEnv modeFun (Mode.codeAt code.chunks %d) %d %s = true := by\n  decide +kernel\n\n' % (n, a, m, a, a, sa))
        out.append(nsClose(n))
        files['ModeD%dW%d.lean' % (k, m)] = ''.join(out)
    mod = 'LeanVM.Guest.Pack.«%s».ModeL%d' % (p, k)
    out = [header(mod, "A long compiled function's mode walk, from its windows' checks.")]
    out.append(''.join('public import %sW%d\n' % (base_, m) for m in range(len(starts))))
    out.append(nsOpen(n, False))
    # the chain in links of `LINK` windows, each from the windows after it (a deeper term exceeds the
    # elaborator's recursion depth); each link's cuts a constant ending in the next link's, so that
    # a link's statement is its successor's without comparing their lists (written last first)
    for m in reversed(range(0, len(bs), LINK)):
        seg = bs[m:m + LINK]
        rest = 'modeCuts%d' % (m + LINK) if m + LINK < len(bs) else '[]'
        body = ' :: '.join(nat(x) for x in seg) + ' :: ' + rest
        out.append('/-- `%s`: its cuts from its %d-th on. -/\ndef modeCuts%d : List ℕ :=\n  %s\n\n' % (
            n, m, m, '\n    '.join(textwrap.wrap(body, 96, break_long_words=False, break_on_hyphens=False))))
    proof = 'modeW%d' % len(bs)
    for m in range(len(bs) - 1, -1, -1):
        proof = '⟨by decide, by decide, by decide +kernel, modeW%d,\n    %s⟩' % (m, proof)
        if m and m % LINK == 0:
            out.append('/-- `%s`: its windows from offset %d go through. -/\ntheorem modeC%d :\n    Mode.WinsOk modeEnv modeFun code.chunks %d %d (Mode.cutOf modeFun %d) modeCuts%d :=\n  %s\n\n' % (
                n, starts[m], m, f['count'], starts[m], starts[m], m, proof))
            proof = 'modeC%d' % m
    out.append('/-- `%s`: its mode walk accepts its code, window by window. -/\ntheorem modeOk : Mode.walk modeEnv modeFun code.chunks.flatten = true :=\n  Mode.walk_of_wins (n := %d) (by decide +kernel) modeCuts0\n    %s\n\n' % (
        n, f['count'], proof))
    out.append(nsClose(n))
    files['ModeL%d.lean' % k] = ''.join(out)
    return files


def fnIndex():
    """Each function's index in the layout (`Statement/Data/Bytecode.lean`'s `f{j}`, `Data.adviceFns`)."""
    import re
    t = open(os.path.join(I.data.STATEMENT, 'Data', 'Bytecode.lean')).read()
    return {m.group(2): int(m.group(1)) for m in re.finditer(r'def f(\d+) : CompiledFunction :=\s*⟨"([^"]*)"', t)}


FNIDX = fnIndex()


def hintParts(n):
    """A long function's hints check in parts: each part's end as (entries before it, offset)."""
    N = I.fns[n]['count']
    offs = sorted(I.fns[n]['hints'])
    return [(sum(1 for o in offs if o < b), b) for b in range(HPART, N, HPART)]


def hintsFiles(p, mods, ns, fnMod):
    """The pack's functions' hints are the advice's (`Mode.HintsOk`), each checked by the kernel
    (`ModeH`), a function longer than `HPART` in parts (`ModeH{q}P{m}`)."""
    files = {}
    parts = {}
    for q, n in enumerate([n for n in ns if I.fns[n]['count'] > HPART]):
        j = FNIDX[n]
        ws = hintParts(n)
        parts[n] = (q, ws)
        pts = [(0, 0)] + ws
        for m, (c, o) in enumerate(pts):
            mod = 'LeanVM.Guest.Pack.«%s».ModeH%dP%d' % (p, q, m)
            out = [header(mod, "The kernel's check of part of a long compiled function's hints.")]
            out.append(importLines({'LeanVM.Guest.Mode.HintsData', 'LeanVM.Guest.Pack.«%s».%s' % (p, fnMod[n])}))
            out.append('\nset_option Elab.async false\n')
            out.append(nsOpen(n, False))
            if m + 1 < len(pts):
                c2, o2 = pts[m + 1]
                out.append('/-- `%s`: its hints at offsets %d to %d are the advice\'s. -/\ntheorem modeHP%d :\n    Mode.hintsChk modeFun.hints modeFun.entry ((Data.adviceFn%d.2.2.drop %d).take (%d - %d)) %d (%d - %d) = true := by\n  decide +kernel\n\n' % (
                    n, o, o2, m, j, c, c2, c, o, o2, o))
            else:
                out.append('/-- `%s`: its hints from offset %d are the advice\'s. -/\ntheorem modeHP%d :\n    Mode.hintsChk modeFun.hints modeFun.entry (Data.adviceFn%d.2.2.drop %d) %d (modeFun.len - %d) = true := by\n  decide +kernel\n\n' % (
                    n, o, m, j, c, o, o))
            out.append(nsClose(n))
            files['ModeH%dP%d.lean' % (q, m)] = ''.join(out)
    mod = 'LeanVM.Guest.Pack.«%s».ModeH' % p
    out = [header(mod, "The kernel's checks that compiled functions' mode walks read the advice's hints.")]
    imps = {'LeanVM.Guest.Mode.HintsData'} | {'LeanVM.Guest.Pack.«%s».%s' % (p, m) for m in mods}
    if parts: imps |= {'LeanVM.Guest.Mode.HintsSplit'} | {'LeanVM.Guest.Pack.«%s».ModeH%dP%d' % (p, q, m)
                                                        for q, ws in parts.values() for m in range(len(ws) + 1)}
    out.append(importLines(imps))
    out.append('\nset_option Elab.async false\n')
    for n in ns:
        out.append(nsOpen(n, False))
        j = FNIDX[n]
        if n in parts:
            q, ws = parts[n]
            proof = 'Mode.hparts_nil modeHP%d' % len(ws)
            for m in range(len(ws) - 1, -1, -1):
                proof = 'Mode.hparts_cons (by decide) (by decide) (by decide +kernel) modeHP%d\n      (%s)' % (m, proof)
            out.append('/-- `%s`: its walk reads the advice\'s hints, checked in parts. -/\ntheorem modeHintsOk : Mode.HintsOk modeFun Data.adviceHints :=\n  Mode.hintsOk_of_parts (j := %d) (d := Data.adviceFn%d) (ws := %s) Mode.adviceFns_ok (by decide +kernel)\n    (by decide +kernel)\n    (%s)\n\n' % (
                n, j, j, lst(ws, lambda w: '(%d, %d)' % w), proof))
        else:
            out.append('/-- `%s`: its walk reads the advice\'s hints. -/\ntheorem modeHintsOk : Mode.HintsOk modeFun Data.adviceHints :=\n  Mode.hintsOk_of_fn (j := %d) (d := Data.adviceFn%d) Mode.adviceFns_ok (by decide +kernel) (by decide +kernel)\n\n' % (n, j, j))
        out.append(nsClose(n))
    files['ModeH.lean'] = ''.join(out)
    return files


def dataFile(p, ns, R):
    """The data of the pack's functions the kernel does not check (`ModeX`): failing or too costly, each
    entering `ModeCerts` through a hypothesis (`Mode.WalkHyp`)."""
    mod = 'LeanVM.Guest.Pack.«%s».ModeX' % p
    out = [header(mod, "The mode walk data of compiled functions whose walks are hypotheses, unchecked.")]
    out.append(importLines(imports(p, ns)))
    for n in ns:
        out.append(nsOpen(n))
        out.append(dataDefs(n, R))
        out.append(nsClose(n))
    return ''.join(out)


def trieOrder(keys):
    """The keys in the order `Trie.entries` lists them, for a trie built by `trie`."""
    def go(ks):
        if not ks: return []
        here = [0] if 0 in ks else []
        left = go([k // 2 for k in ks if k % 2 == 1])
        right = go([k // 2 - 1 for k in ks if k and k % 2 == 0])
        return here + [2 * k + 1 for k in left] + [2 * k + 2 for k in right]
    return go(sorted(keys))


def calleeEntries(n):
    """`n`'s callees by entry, in the order its environment's trie lists them."""
    by = {I.fns[m]['entry']: m for m in calleesOf(n)}
    return [(e, by[e]) for e in trieOrder(by)]


def memProof(i):
    """`x ∈ l`, `x` the `i`-th element of the literal list `l`."""
    pr = 'List.mem_cons_self'
    for _ in range(i): pr = 'List.mem_cons_of_mem _ (%s)' % pr
    return pr


def chain(ps):
    """`∀ x ∈ l, P x` from the proofs `ps` of `P` at the literal list `l`'s elements."""
    out = 'Mode.fa_nil'
    for q in reversed(ps): out = 'Mode.fa_cons (%s)\n    (%s)' % (q, out)
    return out


def hypName(n, kind): return '«%s»' % n if kind == 'walk' else '«%s hints»' % n


def certFile(p, ns, mods, walkH, hintsH):
    """The pack's certificates (`Mode.Cert`), their static facts, walks and callee signatures as
    lists, the walks and hints not checked as hypotheses."""
    mod = 'LeanVM.Guest.Pack.«%s».ModeCert' % p
    out = [header(mod, "The mode walk's certificates of compiled functions, with what each contributes to `ModeCerts`.")]
    out.append(importLines({'LeanVM.Guest.Mode.CertDefs'} | {'LeanVM.Guest.Pack.«%s».%s' % (p, m) for m in mods}))
    out.append('meta import LeanVM.Guest.KernelLit\n')
    out.append('\nset_option Elab.async false\n')
    for n in ns:
        out.append(nsOpen(n))
        out.append('/-- `%s`: its mode walk certificate. -/\nnoncomputable def modeCert : Mode.Cert := ⟨modeEnv, modeFun, code.chunks.flatten⟩\n\n' % n)
        out.append('end\n\n')
        es = calleeEntries(n)
        out.append('/-- `%s`: the callee signatures its walk reads. -/\nkernel_rfl modeSigs : modeCert.E.sigs.entries = %s\n\n' % (
            n, lst(es, lambda e: '(%d, %s.modeSig)' % (e[0], fnq(e[1])))))
        out.append('end LeanVM.Guest.Fn.«%s»\n' % I.fns[n]['ns'])
    out.append('\nnamespace LeanVM.Guest.ModePack.«%s»\n\nopen LeanVM.Guest\n\n@[expose] public section\n\n' % p)
    out.append('/-- The pack\'s certificates. -/\nnoncomputable def certs : List Mode.Cert :=\n  %s\n\nend\n\npublic section\n\n' % lst(ns, lambda n: '%s.modeCert' % fnq(n)))
    for k, n in enumerate(ns):
        out.append('theorem mem%d : %s.modeCert ∈ certs := %s\n\n' % (k, fnq(n), memProof(k)))
    out.append('/-- The certificates\' static facts. -/\ntheorem certs_st : ∀ K ∈ certs, Mode.CertSt K :=\n  %s\n\n' % chain(
        ['⟨by decide +kernel, rfl, rfl⟩'] * len(ns)))
    hs = [(n, 'walk') for n in ns if n in walkH] + [(n, 'hints') for n in ns if n in hintsH]
    args = ''.join(' (%s : Mode.%s %s.modeCert)' % (hypName(n, k), 'WalkHyp' if k == 'walk' else 'HintsHyp', fnq(n)) for n, k in hs)
    def wp(n):
        return '⟨%s, %s⟩' % (hypName(n, 'walk') if n in walkH else '%s.modeOk' % fnq(n),
                             hypName(n, 'hints') if n in hintsH else '%s.modeHintsOk' % fnq(n))
    out.append('/-- The certificates\' walks and hints. -/\ntheorem certs_walk%s :\n    ∀ K ∈ certs, Mode.CertWalk K :=\n  %s\n\n' % (
        args, chain([wp(n) for n in ns])))
    out.append('end\n\nend LeanVM.Guest.ModePack.«%s»\n' % p)
    return ''.join(out)


def plumbs():
    """Each function's fixed cells (`plumb.stat`) and frame size (`fs`), from its pack's bundle."""
    import re
    out = {}
    for b in __import__('glob').glob(os.path.join(PACKS, '*', 'Bundle.lean')):
        txt = open(b).read()
        for blk in txt.split('\nnamespace LeanVM.Guest.Fn.')[1:]:
            ns = blk.split('\n', 1)[0].strip().strip('«»')
            st = re.search(r'def plumb : B2C.Plumb where\n  stat := \[(.*?)\]\n', blk, re.S)
            fs = re.search(r'\ndef fs : ℕ := (\d+)', blk)
            if st is None or fs is None: continue
            stat = {int(c): (int(a), int(b2)) for c, a, b2 in re.findall(r'\((\d+), \(\.k (\d+) (\d+)\)\)', st.group(1))}
            out[ns] = (stat, int(fs.group(1)))
    return out


def nzStatOk(n, R, PL):
    """`Mode.nzStat` at `n`'s index holds and some nonzero residual needs it: each nonzero residual's
    product cell a fixed nonzero constant of the frame."""
    f = I.fns[n]
    if f['ns'] not in PL: return False
    stat, fs = PL[f['ns']]
    nz = [i for i, rs in R.get(n, {}).items() for r in rs if r[0] == 'nz']
    if not nz: return False
    for i in nz:
        op, a = f['ops'][i]
        c = a[2] if op == 'mul' else 0
        w = stat.get(c)
        if not (w is not None and 2 <= c < fs and w[0] < 2 ** 64 and w[1] < 2 ** 64 and w != (0, 0)): return False
    return True


LINKS = sorted(os.path.basename(f)[:-5] for f in __import__('glob').glob(os.path.join(I.data.ROOT, 'Checked', 'Link*.lean')))
# the assembly's signature and link modules, packs at most this many functions each
SIGCHUNK = 160
# the certificates' packs in groups of this many, each group's facts one term
GROUP = 16


def assemblyFiles(packList, walkH, hintsH, R):
    """`Mode/Certs/List.lean` (the certificates, each one's membership, no entry repeated),
    `Mode/Certs/Sig{k}.lean` (callee signatures and the function table, pack by pack) and
    `Mode/Certs.lean` (`ModeHyps`, the hypotheses, and `ModeCerts` from them)."""
    base = os.path.join(I.data.ROOT, 'Mode')
    files = {}
    PL = plumbs()
    pk = sorted(packList)
    out = [header('LeanVM.Guest.Mode.Certs.List', "The mode walk's certificates, every guest function's, and their entries told apart.")]
    out.append(importLines({'LeanVM.Guest.Pack.«%s».ModeCert' % p for p in pk}))
    out.append('\nset_option Elab.async false\n')
    out.append('\nnamespace LeanVM.Guest.Mode\n\nopen LeanVM.Guest\n\n@[expose] public section\n\n')
    G = [pk[i:i + GROUP] for i in range(0, len(pk), GROUP)]
    gi = {p: (g, i) for g, ps in enumerate(G) for i, p in enumerate(ps)}
    out.append('/-- The certificates by pack, packs in groups. -/\nnoncomputable def guestGroups : List (List (List Cert)) :=\n  [%s]\n\n' % ',\n   '.join(
        '[%s]' % ', '.join('ModePack.«%s».certs' % p for p in ps) for ps in G))
    out.append('/-- The certificates by pack. -/\nnoncomputable def guestPacks : List (List Cert) := guestGroups.flatten\n\n')
    out.append('/-- **Every guest function\'s certificate.** -/\nnoncomputable def guestCerts : List Cert := guestPacks.flatten\n\nend\n\npublic section\n\n')
    for k, p in enumerate(pk):
        out.append('theorem guestPacks_mem%d : ModePack.«%s».certs ∈ guestPacks :=\n  mem_flatten_of (%s) (%s)\n\n' % (
            k, p, memProof(gi[p][0]), memProof(gi[p][1])))
    out.append('/-- No entry repeats. -/\ntheorem guestCerts_nodup : nodupB (guestCerts.map (·.F.entry)) 0 = true := by decide +kernel\n\n')
    out.append('/-- The certificates\' static facts. -/\ntheorem guestCerts_st : ∀ K ∈ guestCerts, CertSt K :=\n  fa_flatten (fa_flatten (%s))\n\n' % chain(
        ['(%s)' % chain(['ModePack.«%s».certs_st' % p for p in ps]) for ps in G]))
    out.append('end\n\nend LeanVM.Guest.Mode\n')
    for k, p in enumerate(pk):
        for i, n in enumerate(packList[p]):
            out.append('\nnamespace LeanVM.Guest.Fn.«%s»\n\npublic section\n\ntheorem modeCert_in : modeCert ∈ Mode.guestCerts :=\n  Mode.mem_flatten_of Mode.guestPacks_mem%d ModePack.«%s».mem%d\n\nend\n\nend LeanVM.Guest.Fn.«%s»\n' % (
                I.fns[n]['ns'], k, p, i, I.fns[n]['ns']))
    files[os.path.join(base, 'Certs', 'List.lean')] = ''.join(out)
    chunks = []; cur = []; size = 0
    for p in pk:
        if cur and size + len(packList[p]) > SIGCHUNK: chunks.append(cur); cur = []; size = 0
        cur.append(p); size += len(packList[p])
    if cur: chunks.append(cur)
    for c, ps in enumerate(chunks):
        out = [header('LeanVM.Guest.Mode.Certs.Sig%d' % c, "The mode walk's certificates' callee signatures and code, pack by pack.")]
        out.append(importLines({'LeanVM.Guest.Mode.Certs.List', 'LeanVM.Guest.Mode.CertNz', 'LeanVM.Guest.SoundFacts'} | {'LeanVM.Guest.Checked.%s' % l for l in LINKS}))
        out.append('\nset_option Elab.async false\n')
        nzs = []
        for p in ps:
            out.append('\nnamespace LeanVM.Guest.ModePack.«%s»\n\nopen LeanVM.Guest LeanVM.Guest.Mode\n\npublic section\n\n' % p)
            ns = packList[p]
            sp = []
            for n in ns:
                es = calleeEntries(n)
                sp.append('Mode.sigsIn_of %s.modeSigs\n    (%s)' % (fnq(n), chain(['⟨_, %s.modeCert_in, rfl, rfl, rfl⟩' % fnq(m) for e, m in es])))
            out.append('theorem certs_sigs : ∀ K ∈ certs, SigsIn guestCerts K :=\n  %s\n\n' % chain(sp))
            fl = ['Mode.fnLink_of (End.fnOf_mem (by decide)) Checked.code%d rfl rfl' % FNIDX[n] for n in ns]
            out.append('theorem certs_fn : ∀ K ∈ certs, FnLink K :=\n  %s\n\n' % chain(fl))
            out.append('end\n\nend LeanVM.Guest.ModePack.«%s»\n' % p)
            nzs += [n for n in ns if nzStatOk(n, R, PL)]
        for n in nzs:
            j = FNIDX[n]
            out.append('\nnamespace LeanVM.Guest.Fn.«%s»\n\nopen LeanVM.Guest LeanVM.Guest.Mode\n\npublic section\n\n/-- `%s`: each nonzero residual\'s product a fixed nonzero constant of its frame. -/\ntheorem modeNzStat : NzStatOk modeCert :=\n  ⟨%d, by decide, by rw [Checked.code%d]; rfl,\n    by rw [Checked.plumbEq%d, Checked.fsEq%d]; decide +kernel⟩\n\nend\n\nend LeanVM.Guest.Fn.«%s»\n' % (
                I.fns[n]['ns'], n, j, j, j, j, I.fns[n]['ns']))
        files[os.path.join(base, 'Certs', 'Sig%d.lean' % c)] = ''.join(out)
    # the hypotheses and the closed certificates
    hs = [(n, 'walk') for n in sorted(walkH)] + [(n, 'hints') for n in sorted(hintsH)]
    out = [header('LeanVM.Guest.Mode.Certs', "The mode walk's certificates closed (`ModeCerts`), from the walks and hints the kernel does not check.")]
    out.append(importLines({'LeanVM.Guest.Mode.CertAssemble'} | {'LeanVM.Guest.Mode.Certs.Sig%d' % c for c in range(len(chunks))}))
    out.append('\nset_option Elab.async false\n')
    out.append('\nnamespace LeanVM.Guest.Mode\n\nopen LeanVM.Guest\n\npublic section\n\n')
    out.append('/-- **The walks and hints the kernel does not check**, one per function: a walk failing or too\n    costly to check (`WalkHyp`), hints too costly to check in one piece (`HintsHyp`). -/\nstructure ModeHyps : Prop where\n')
    for n, k in hs:
        out.append('  %s : %s %s.modeCert\n' % (hypName(n, k), 'WalkHyp' if k == 'walk' else 'HintsHyp', fnq(n)))
    out.append('\n')
    def packWalk(p):
        ns = packList[p]
        a = ''.join(' h.%s' % hypName(n, k) for k, H in (('walk', walkH), ('hints', hintsH)) for n in ns if n in H)
        return 'ModePack.«%s».certs_walk%s' % (p, a)
    G = [pk[i:i + GROUP] for i in range(0, len(pk), GROUP)]
    for g, ps in enumerate(G):
        body = chain([packWalk(p) for p in ps])
        out.append('theorem guestGroup_walk%d (%s : ModeHyps) : ∀ l ∈ guestGroups[%d]!, ∀ K ∈ l, CertWalk K :=\n  %s\n\n' % (
            g, 'h' if ' h.' in body else '_h', g, body))
    def two(f):
        return 'fa_flatten (fa_flatten (%s))' % chain(['(%s)' % chain([f % p for p in ps]) for ps in G])
    out.append('theorem guestCerts_walk (h : ModeHyps) : ∀ K ∈ guestCerts, CertWalk K :=\n  fa_flatten (fa_flatten (%s))\n\n' % chain(
        ['guestGroup_walk%d h' % g for g in range(len(G))]))
    out.append('theorem guestCerts_sigs : ∀ K ∈ guestCerts, SigsIn guestCerts K :=\n  %s\n\n' % two('ModePack.«%s».certs_sigs'))
    out.append('theorem guestCerts_fn : ∀ K ∈ guestCerts, FnLink K :=\n  %s\n\n' % two('ModePack.«%s».certs_fn'))
    out.append('/-- **The certificates closed**, given the walks and hints the kernel does not check. -/\ntheorem modeCerts_guest (h : ModeHyps) :\n    EndExec.ModeCerts guestCerts Fn.«main».modeCert guestE0 :=\n  modeCerts_of guestCerts_st (guestCerts_walk h) guestCerts_fn guestCerts_sigs guestCerts_nodup\n    Fn.«main».modeCert_in rfl (by decide +kernel) rfl\n\n')
    out.append('/-- No certificate\'s entry is `__jump_tables`\'s. -/\ntheorem guestCerts_entry_ne : ∀ K ∈ guestCerts, K.F.entry ≠ 0 := entry_ne_zero guestCerts_st\n\n')
    out.append('/-- **`main`\'s certificate starts as the prologue leaves it.** -/\ntheorem mainOk_guestCerts : EndExec.MainOk Fn.«main».modeCert guestE0 := mainOk_guest rfl rfl\n\n')
    out.append('end\n\nend LeanVM.Guest.Mode\n')
    files[os.path.join(base, 'Certs.lean')] = ''.join(out)
    return files


res_ = res
HEAVY = set()


def main(argv):
    check = '--check' in argv
    only = argv[argv.index('--only') + 1:] if '--only' in argv else None
    cache = os.environ.get('MODE_CERT_CACHE')
    if cache and os.path.exists(cache):
        import pickle
        sigs, fails, R, I.E.sigs, cost = pickle.load(open(cache, 'rb'))
    else:
        sigs = {}; fails = {}; R = {}
        for n in I.order:
            f = I.fns[n]
            try:
                sigs[n], R[n] = I.infer(n)
            except Fail as e:
                fails[n] = e.args[0]
                s = I.mkSig(f, [], [], list(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0))))
                I.E.sigs[f['entry']] = s; sigs[n] = s
        # a callee inferred again for a caller (`infer.narrow`): its last inference
        for n, (s, r) in I.LAST.items(): sigs[n], R[n] = s, r
        cost = {n: kprofile(n, sigs[n], R.get(n, {})) for n in I.fns if n not in fails}
        if cache:
            import pickle
            pickle.dump((sigs, fails, R, I.E.sigs, cost), open(cache, 'wb'))
    # each function's cuts, none if it fits in `KBUDGET`; too heavy if an instruction alone exceeds `KHARD`
    cuts = {}
    for n, (S, C) in cost.items():
        try: cuts[n] = cutsAt(S, C)
        except Heavy: HEAVY.add(n)
    work = {n: sum(C) for n, (S, C) in cost.items()}
    files = {}
    nwin = 0
    walkH = set(); hintsH = set(); packList = {}
    for p, ns in packs().items():
        if only and p not in only: continue
        files[os.path.join(PACKS, p, 'ModeSig.lean')] = sigFile(p, ns, sigs)
        groups = []; cur = []; size = 0; mem = KBASE; long_ = []
        for n in ns:
            if not checkable(n, fails): continue
            c = I.fns[n]['count']
            if cuts[n]: long_.append(n); continue
            if cur and (size + c > CHUNK or mem + work[n] > KBUDGET): groups.append(cur); cur = []; size = 0; mem = KBASE
            cur.append(n); size += c; mem += work[n]
        if cur: groups.append(cur)
        for k, g in enumerate(groups):
            files[os.path.join(PACKS, p, 'Mode%d.lean' % k)] = checkFile(p, k, g, sigs, R)
        for k, n in enumerate(long_):
            for name, text in winFiles(p, k, n, sigs, R, cuts[n]).items():
                files[os.path.join(PACKS, p, name)] = text; nwin += name.startswith('ModeD') and 'W' in name
        xs = [n for n in ns if not checkable(n, fails)]
        if xs: files[os.path.join(PACKS, p, 'ModeX.lean')] = dataFile(p, xs, R)
        mods = ['Mode%d' % k for k in range(len(groups))] + ['ModeD%d' % k for k in range(len(long_))] + (['ModeX'] if xs else [])
        hs = [n for g in groups for n in g] + long_ + xs
        fnMod = {n: 'Mode%d' % k for k, g in enumerate(groups) for n in g}
        fnMod.update({n: 'ModeD%d' % k for k, n in enumerate(long_)}); fnMod.update({n: 'ModeX' for n in xs})
        if hs:
            for name, text in hintsFiles(p, mods, hs, fnMod).items(): files[os.path.join(PACKS, p, name)] = text
        walkH.update(xs)
        cmods = ['Mode%d' % k for k in range(len(groups))] + ['ModeL%d' % k for k in range(len(long_))] + \
            (['ModeX'] if xs else []) + (['ModeH'] if hs else [])
        files[os.path.join(PACKS, p, 'ModeCert.lean')] = certFile(p, ns, cmods, walkH, hintsH)
        packList[p] = ns
    if not only: files.update(assemblyFiles(packList, walkH, hintsH, R))
    import glob
    bad = []
    for path in glob.glob(os.path.join(PACKS, '*', 'Mode*.lean')):
        if path.endswith('ModeSig.lean'): continue
        if path in files or (only and path.split(os.sep)[-2] not in only): continue
        if check: bad.append(path)
        else: os.remove(path)
    for path, text in sorted(files.items()):
        old = open(path).read() if os.path.exists(path) else None
        text = wrap(text)
        if old == text: continue
        if check: bad.append(path)
        else:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            open(path, 'w').write(text)
    if check and bad:
        print('stale:', *bad, sep='\n  '); sys.exit(1)
    nck = sum(1 for n in I.fns if checkable(n, fails))
    print('functions', len(I.fns), 'failing', len(fails), 'checked', nck, 'unchecked', sorted(HEAVY), 'windows', nwin, 'files', len(files),
          'changed', len(bad) if check else 'written')
    print('failing', sorted(fails))
    print('hypotheses: walks', sorted(walkH), 'hints', sorted(hintsH))


if __name__ == '__main__':
    main(sys.argv[1:])
