"""Writes the mode walk's certificates into each pack: `Pack/*/ModeSig.lean`, every function's
signature (`Mode.Sig`), and `Pack/*/Mode{k}.lean`, every passing function's hints, residuals and
table sizes (`Mode.Fun`) with the kernel's check of its walk (`Mode.walk`, `Guest/Mode/Abs.lean`).
The signatures and residuals are `infer.py`'s. `--check` writes nothing and fails when a file
differs. Usage: python3 -I scripts/mode-cert/gen.py [--check] [--only PACK...]"""
import sys, os, collections
sys.setrecursionlimit(100000)
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import infer as I
from walk import Fail

PACKS = os.path.join(I.data.ROOT, 'Pack')
# a module's checks, at most this many instructions
CHUNK = 2500
# a literal list longer than this is written as a flattened list of such lists
LONG = 16
# The walk is evaluated lazily by the kernel, whose recursion is bounded: a function is checked here
# only when its code, the lists its walk reads (its and its callees' signatures) and the runs its hints
# write are at most these sizes.
MAX_CODE = 2000
MAX_LIST = 300


def sigSize(s):
    return max(len(s.pre), len(s.preR), len(s.post), len(s.postR), len(s.postL), len(s.preP), len(s.postP),
               len(s.postLP), len(s.entry), len(s.ret))


def hintSize(h):
    t = h[0]
    if t == 'ws': return h[3]
    if t == 'wh': return h[4]
    if t in ('bd', 'be'): return h[3]
    if t == 'we': return h[6]
    if t == 'dd': return h[4]
    if t == 'fl': return h[3]
    if t == 'lc': return h[3]
    return 0


def checkable(n, sigs):
    f = I.fns[n]
    return (f['count'] <= MAX_CODE and sigSize(sigs[n]) <= MAX_LIST and
            all(sigSize(sigs[m]) <= MAX_LIST for m in I.calls[n]) and
            all(hintSize(h) <= MAX_LIST for hs in f['hints'].values() for h in hs))


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
    return '⟨%d, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s⟩' % (
        s.pc, lst(s.entry, nat), 'none' if s.self_ is None else '(some %d)' % s.self_, lst(s.pre, mono),
        lst(s.preR, rng), lst(s.term, lambda p: '(%s, %s)' % (idx(p[0]), idx(p[1]))), lst(s.ret, nat),
        lst(s.post, mono), lst(s.postR, rng), lst(s.postL, rng), lst(s.preP, ptr), lst(s.postP, ptr),
        lst(s.postLP, ptr))


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


def res(r): return '(.lt %s %s)' % (idx(r[1]), idx(r[2])) if r[0] == 'lt' else '(.nz %d)' % r[1]


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


def checkFile(p, k, group, sigs, res):
    mod = 'LeanVM.Guest.Pack.«%s».Mode%d' % (p, k)
    out = [header(mod, "The kernel's checks of compiled functions' mode walks, over their data and their callees' signatures.")]
    imps = {'LeanVM.Guest.Mode.Abs', 'LeanVM.Guest.Data.Pows', 'LeanVM.Guest.Pack.«%s».Bundle' % p,
            'LeanVM.Guest.Pack.«%s».ModeSig' % p}
    for n in group:
        for m in calleesOf(n): imps.add('LeanVM.Guest.Pack.«%s».ModeSig' % I.fns[m]['pack'])
    out.append(''.join('public import %s\n' % i for i in sorted(imps)))
    out.append('\nset_option Elab.async false\n')
    for n in group:
        f = I.fns[n]
        sigt = {I.fns[m]['entry']: m for m in calleesOf(n)}
        env = '⟨Data.powTree, Data.jtTrie, %d, %d, %s, %d⟩' % (
            I.JT_LO, I.JT_HI, trie(sigt, lambda m: '%s.modeSig' % fnq(m)), I.HALT)
        hs = {i: h for i, h in f['hints'].items() if h}
        rs = {i: r for i, r in res.get(n, {}).items() if r}
        fun = '⟨%d, %d, %s.modeSig, %s, %s, %s, %s⟩' % (
            f['entry'], f['count'], fnq(n), trie(hs, lambda l: lst(l, hint)), trie(rs, lambda l: lst(l, res_)),
            trie(f['tabs'], nat), 'true' if n == 'main' else 'false')
        out.append('\nnamespace LeanVM.Guest.Fn.«%s»\n\nopen LeanVM.Guest LeanVM.Guest.Exec\n\n@[expose] public section\n\n' % I.fns[n]['ns'])
        out.append('/-- `%s`: the program its walk shares. -/\nnoncomputable def modeEnv : Mode.Env :=\n  %s\n\n' % (n, env))
        out.append('/-- `%s`: its hints, residuals and table sizes. -/\nnoncomputable def modeFun : Mode.Fun :=\n  %s\n\n' % (n, fun))
        out.append('/-- `%s`: its mode walk accepts its code. -/\ntheorem modeOk : Mode.walk modeEnv modeFun code.chunks.flatten = true := by\n  decide +kernel\n\nend\n\nend LeanVM.Guest.Fn.«%s»\n' % (n, I.fns[n]['ns']))
    return ''.join(out)


res_ = res


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
    files = {}
    for p, ns in packs().items():
        if only and p not in only: continue
        files[os.path.join(PACKS, p, 'ModeSig.lean')] = sigFile(p, ns, sigs)
        groups = []; cur = []; size = 0
        for n in ns:
            if n in fails or not checkable(n, sigs): continue
            c = I.fns[n]['count']
            if cur and size + c > CHUNK: groups.append(cur); cur = []; size = 0
            cur.append(n); size += c
        if cur: groups.append(cur)
        for k, g in enumerate(groups):
            files[os.path.join(PACKS, p, 'Mode%d.lean' % k)] = checkFile(p, k, g, sigs, R)
    import glob
    bad = []
    for path in glob.glob(os.path.join(PACKS, '*', 'Mode[0-9]*.lean')):
        if path in files or (only and path.split(os.sep)[-2] not in only): continue
        if check: bad.append(path)
        else: os.remove(path)
    for path, text in sorted(files.items()):
        old = open(path).read() if os.path.exists(path) else None
        if old == text: continue
        if check: bad.append(path)
        else: open(path, 'w').write(text)
    if check and bad:
        print('stale:', *bad, sep='\n  '); sys.exit(1)
    nck = sum(1 for n in I.fns if n not in fails and checkable(n, sigs))
    print('functions', len(I.fns), 'failing', len(fails), 'checked', nck, 'files', len(files),
          'changed', len(bad) if check else 'written')


if __name__ == '__main__':
    main(sys.argv[1:])
