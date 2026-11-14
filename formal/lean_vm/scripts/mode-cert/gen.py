"""Writes the mode walk's certificates into each pack: `Pack/*/ModeSig.lean`, every function's
signature (`Mode.Sig`), and `Pack/*/Mode{k}.lean`, every passing function's hints, residuals and
table sizes (`Mode.Fun`) with the kernel's check of its walk (`Mode.walk`, `Guest/Mode/Abs.lean`).
A function longer than `WMAX` is checked in windows (`Guest/Mode/Win.lean`): its data and the
snapshots at its cuts in `ModeD{k}`, each window's check in `ModeD{k}W{m}`, their chain in
`ModeL{k}`. The signatures and residuals are `infer.py`'s, the snapshots `walk.py`'s states.
`--check` writes nothing and fails when a file differs.
Usage: python3 -I scripts/mode-cert/gen.py [--check] [--only PACK...]"""
import sys, os, collections
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
# a function longer than this, or costlier (`walk.COST`, the kernel's list work, roughly), is checked
# in windows of at most `2 WIN` instructions and `WCOST`, each cut where the fewest states are pending;
# a module checks functions of at most `CHUNK` instructions and `WCOST` in all
WMAX = 2000
WIN = 1500
# the estimate misses work on runs and joins, so a window of a function shorter than `LONGW` is at
# most `SHORTW` instructions
LONGW = 10000
SHORTW = 600
WCOST = 200000
# a function longer than this has no hints check (`ModeH`): the kernel's walk over its offsets is too
# costly in one piece
HMAX = 20000
# a function whose list work is denser than this per instruction, and more than `XCOST`, is not checked
XDENSE = 1500
XCOST = 2000000


# measured: its windows exceed 3.5 GB however short, the estimate missing its work
MEASURED_HEAVY = {'__loop17'}


def checkable(n, fails): return n not in fails and n not in HEAVY and n not in MEASURED_HEAVY


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


def sigFile(p, ns, sigs):
    out = [header('LeanVM.Guest.Pack.«%s».ModeSig' % p, 'What a caller knows of compiled functions, for the mode walk.')]
    out.append('public import LeanVM.Guest.Mode.Abs\n')
    for n in ns:
        out.append('\nnamespace LeanVM.Guest.Fn.«%s»\n\n@[expose] public section\n\n' % I.fns[n]['ns'])
        out.append('/-- `%s`: its entry, the cells and heap facts it needs at entry and guarantees at return. -/\n' % n)
        out.append('noncomputable def modeSig : Mode.Sig :=\n  %s\n\nend\n\nend LeanVM.Guest.Fn.«%s»\n' % (sig(sigs[n]), I.fns[n]['ns']))
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


def dataDefs(n, res, cuts=None):
    """`modeEnv` and `modeFun`, its cuts' snapshots `snap{b}` named in `modeFun`'s trie."""
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
    for b, S in sorted((cuts or {}).items()):
        out.append('/-- `%s`: the paths and pending edges at its cut at offset %d. -/\nnoncomputable def snap%d : List Mode.Abs × Mode.Pend :=\n  %s\n\n' % (n, b, b, snapLit(S)))
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


def profile(n, sig, res):
    """At each offset of a function's walk: the states there and the list work before it."""
    f = I.fns[n]
    cnt = [0] * f['count']; acc = [0] * (f['count'] + 1)
    W.COST[0] = 0
    def size(i, cur, pend):
        cnt[i] = len(cur) + sum(len(g[1]) for g in pend); acc[i] = W.COST[0]
    I.Walk(I.E, f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main').run(f['ops'], probe=size)
    acc[f['count']] = W.COST[0]
    return cnt, acc


def cutsOf(n, sig, res):
    """The cuts of a long function, with the paths and pending edges there."""
    f = I.fns[n]
    cnt, acc = profile(n, sig, res)
    cuts = []; b = 0; N = f['count']
    L = 2 * WIN if N > LONGW else SHORTW
    while b + L // 4 < N and (acc[N] - acc[b] > WCOST or N - b > L):
        e = b + 1
        while e < N and e - b < L and acc[e] - acc[b] < WCOST: e += 1
        if e >= N - L // 8: break
        lo = max(b + 1, e - max(1, (e - b) // 2))
        b = min(range(lo, e + 1), key=lambda i: (cnt[i], -i))
        cuts.append(b)
    snaps = {}
    def rec(i, cur, pend):
        if i in cuts:
            snaps[i] = ([A.copy() for A in cur], [(list(ts), [B.copy() for B in Bs], m) for ts, Bs, m in pend])
    I.Walk(I.E, f['entry'], f['count'], sig, f['hints'], res, f['tabs'], main=n == 'main').run(f['ops'], probe=rec)
    return snaps


def winFiles(p, k, n, sigs, res):
    """A long function's data and snapshots (`ModeD{k}`), each window's check (`ModeD{k}W{m}`) and
    their chain (`ModeL{k}`)."""
    f = I.fns[n]
    snaps = cutsOf(n, sigs[n], res.get(n, {}))
    bs = sorted(snaps)
    base_ = 'LeanVM.Guest.Pack.«%s».ModeD%d' % (p, k)
    files = {}
    out = [header(base_, "A long compiled function's mode walk data and the snapshots at its cuts.")]
    out.append(importLines(imports(p, [n]) | {'LeanVM.Guest.Mode.Win'}))
    out.append(nsOpen(n))
    out.append(dataDefs(n, res, snaps))
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
    proof = 'modeW%d' % len(bs)
    for m in range(len(bs) - 1, -1, -1):
        proof = '⟨by decide, by decide, by decide +kernel, modeW%d,\n    %s⟩' % (m, proof)
    out.append('/-- `%s`: its mode walk accepts its code, window by window. -/\ntheorem modeOk : Mode.walk modeEnv modeFun code.chunks.flatten = true :=\n  Mode.walk_of_wins (n := %d) (by decide +kernel) %s\n    %s\n\n' % (
        n, f['count'], lst(bs, nat), proof))
    out.append(nsClose(n))
    files['ModeL%d.lean' % k] = ''.join(out)
    return files


def fnIndex():
    """Each function's index in the layout (`Statement/Data/Bytecode.lean`'s `f{j}`, `Data.adviceFns`)."""
    import re
    t = open(os.path.join(I.data.STATEMENT, 'Data', 'Bytecode.lean')).read()
    return {m.group(2): int(m.group(1)) for m in re.finditer(r'def f(\d+) : CompiledFunction :=\s*⟨"([^"]*)"', t)}


FNIDX = fnIndex()


def hintsFile(p, mods, ns):
    """The pack's functions' hints are the advice's (`Mode.HintsOk`), each checked by the kernel."""
    mod = 'LeanVM.Guest.Pack.«%s».ModeH' % p
    out = [header(mod, "The kernel's checks that compiled functions' mode walks read the advice's hints.")]
    out.append(importLines({'LeanVM.Guest.Mode.HintsData'} | {'LeanVM.Guest.Pack.«%s».%s' % (p, m) for m in mods}))
    out.append('\nset_option Elab.async false\n')
    for n in ns:
        out.append(nsOpen(n, False))
        j = FNIDX[n]
        out.append('/-- `%s`: its walk reads the advice\'s hints. -/\ntheorem modeHintsOk : Mode.HintsOk modeFun Data.adviceHints :=\n  Mode.hintsOk_of_fn (j := %d) (d := Data.adviceFn%d) Mode.adviceFns_ok (by decide +kernel) (by decide +kernel)\n\n' % (n, j, j))
        out.append(nsClose(n))
    return ''.join(out)


res_ = res
HEAVY = set()


def main(argv):
    check = '--check' in argv
    only = argv[argv.index('--only') + 1:] if '--only' in argv else None
    sigs = {}; fails = {}; R = {}
    for n in I.order:
        f = I.fns[n]
        try:
            sigs[n], R[n] = I.infer(n)
        except Fail as e:
            fails[n] = e.args[0]
            s = I.mkSig(f, [], [], list(range(2 + f.get('nargs', 0), 2 + f.get('nargs', 0) + f.get('nret', 0))))
            I.E.sigs[f['entry']] = s; sigs[n] = s
    cost = {n: profile(n, sigs[n], R.get(n, {}))[1][-1] for n in I.fns if n not in fails}
    HEAVY.update(n for n, c in cost.items() if c > XCOST and c > XDENSE * I.fns[n]['count'])
    files = {}
    nwin = 0
    for p, ns in packs().items():
        if only and p not in only: continue
        files[os.path.join(PACKS, p, 'ModeSig.lean')] = sigFile(p, ns, sigs)
        groups = []; cur = []; size = 0; work = 0; long_ = []
        for n in ns:
            if not checkable(n, fails): continue
            c = I.fns[n]['count']
            if c > WMAX or cost[n] > WCOST: long_.append(n); continue
            if cur and (size + c > CHUNK or work + cost[n] > WCOST): groups.append(cur); cur = []; size = 0; work = 0
            cur.append(n); size += c; work += cost[n]
        if cur: groups.append(cur)
        for k, g in enumerate(groups):
            files[os.path.join(PACKS, p, 'Mode%d.lean' % k)] = checkFile(p, k, g, sigs, R)
        for k, n in enumerate(long_):
            for name, text in winFiles(p, k, n, sigs, R).items():
                files[os.path.join(PACKS, p, name)] = text; nwin += name.startswith('ModeD') and 'W' in name
        mods = ['Mode%d' % k for k in range(len(groups))] + ['ModeD%d' % k for k in range(len(long_))]
        hs = [n for n in [n for g in groups for n in g] + long_ if I.fns[n]['count'] <= HMAX]
        if hs:
            files[os.path.join(PACKS, p, 'ModeH.lean')] = hintsFile(p, mods, hs)
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
        else: open(path, 'w').write(text)
    if check and bad:
        print('stale:', *bad, sep='\n  '); sys.exit(1)
    nck = sum(1 for n in I.fns if checkable(n, fails))
    print('functions', len(I.fns), 'failing', len(fails), 'checked', nck, 'unchecked', sorted(HEAVY | MEASURED_HEAVY), 'windows', nwin, 'files', len(files),
          'changed', len(bad) if check else 'written')


if __name__ == '__main__':
    main(sys.argv[1:])
