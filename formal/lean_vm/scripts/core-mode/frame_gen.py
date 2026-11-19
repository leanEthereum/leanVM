"""Writes the frame walk's checks (`LeanVM/Guest/CoreMode/Frame.lean`): per pack,
`LeanVM/Guest/CoreMode/Pack/<pack>/Frame{k}.lean`, each function's data (`CoreMode.FFun`: its
executor facts, its signature and its callees', its hints, residual divisors, table targets, the
oracle) with the kernel's check of its walk (`frameOk … = true := by decide +kernel`); a long
function in windows (`frameWin`), each its own module `FrameW{k}.lean`, from the cut states
`frame.py` computes. The oracle and the residual divisors are read off today's mode walk
(`frame_data.py`, `MODE_CERT_CACHE`) until the core heap certificate gives them.
Usage: MODE_CERT_CACHE=FILE python3 -I scripts/core-mode/frame_gen.py [--only PACK...] [--fns NAME...]"""
import os, re, sys, collections, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frame as FR  # noqa: E402
import frame_data as FD  # noqa: E402
import frame_run as RUN  # noqa: E402
sys.path.insert(0, FD.MODE)
import gen as MG  # noqa: E402

OUT = os.path.join(FD.ROOT, 'CoreMode', 'Pack')
# a module's checks: at most this many instructions
CHUNK = int(os.environ.get('FRAME_CHUNK', 12000))
# a function longer than this is checked in windows of about this many instructions
WIN = int(os.environ.get("FRAME_WIN", 7000))


def wrap(text, width=100):
    """`MG.wrap` in linear time: long lines broken at spaces, the rest indented."""
    out = []
    for line in text.split('\n'):
        if len(line) <= width:
            out.append(line); continue
        toks = line.split(' ')
        cur = toks[0]
        for t in toks[1:]:
            if len(cur) + 1 + len(t) > width and cur.strip():
                out.append(cur); cur = '    ' + t
            else:
                cur = cur + ' ' + t
        out.append(cur)
    return '\n'.join(out)


def lst(xs, f=str): return '[%s]' % ', '.join(f(x) for x in xs)


def sym(s):
    if s[0] == 'z': return '.zero'
    return '(.%s %d)' % (s[0], s[1])


def unitTrie(keys): return MG.trie({k: () for k in keys}, lambda _: '()')


def natTrie(d): return MG.trie(d, str)


def hqk(q, o): return q * FR.HQ_SHIFT + o


def fstLit(A):
    """A state of `frame.py` as a literal `CoreMode.FSt` (its `Exec` state restarted)."""
    env = 'envOf %s' % lst(sorted(A.st.env.items()), lambda p: '(%d, %s)' % (p[0], sym(p[1])))
    return '⟨St.init (%s), %s, %s, %s, %s, %s, %s⟩' % (
        env, unitTrie(A.w), unitTrie(A.nz), unitTrie(hqk(q, o) for q, o in A.hq),
        unitTrie(hqk(q, o) for q, o in A.hs), natTrie(A.cp), natTrie(A.one))


def adviceIdx():
    """Each function's index in `Data.adviceFn{k}` (`Statement/Data/AdviceHints.lean`)."""
    import re
    d = os.path.join(FD.ROOT, '..', '..', '..', 'Statement', 'Data')
    t = ''.join(open(f).read() for f in sorted(glob.glob(os.path.join(d, 'AdviceHints*.lean'))))
    return {m.group(1): int(m.group(2)) for m in re.finditer(r'/-- `([^`]*)`: its entry, length and hints by pc\. -/\ndef adviceFn(\d+)', t)}


ADV = None
ROUTE = {}


def cutsFor(D, n):
    """Offsets to cut a long function at, about every `WIN` instructions."""
    f = D['fns'][n]
    return list(range(WIN, f['count'] - WIN // 4, WIN))


def cutLit(c):
    """A cut (the live path and the pending groups) as a literal."""
    cur, pend = c
    return '(%s, %s)' % ('none' if cur is None else '(some %s)' % fstLit(cur),
                         lst(pend, lambda g: '(%d, %s, %s)' % (g[0], lst(g[1]), fstLit(g[2]))))


def fnData(D, n, cuts):
    """The function's `FFun` literal, its callees' packs, and the walk (with its cut states)."""
    f = D['fns'][n]
    F, entry, ln, sig, tgt, nzr = RUN.inputs(D, n)
    rt = ROUTE.get(n)
    O_ = set(rt['O']) if rt else set(D['O'].get(n, []))
    S_ = set(rt['S']) if rt else set()
    w = FR.Walk(F, entry, ln, sig, D['fsig'], f['hints'], nzr, tgt, O_, D['halt'], S=S_)
    w.cutAt = set(cuts)
    w.run(f['ops'])
    byentry = {g['entry']: m for m, g in D['fns'].items()}
    sigs = {pc: '%s.modeSig' % MG.fnq(byentry[pc]) for pc in sorted(w.used)}
    if rt and rt.get('kind') == 'l':
        # a leaf loop helper on the core route: its walk is told no callee (`CoreMode.loopShapeOk`)
        sigs = {}
    if rt and rt.get('kind') == 'lc':
        # a loop helper with calls on the core route: its walk is told its environment's callees, its own entry
        # among them (`CoreMode.LoopOkC.fsigs`)
        sigs[entry] = '%s.modeSig' % MG.fnq(n)
    packs = {D['fns'][byentry[pc]]['pack'] for pc in w.used}
    fx = D['facts'][n]
    facts = '{ env := %s, fpOne := %s, pows := Data.powTree, scaled := %s }' % (
        lst(sorted(fx['env'].items()), lambda p: '(%d, %s)' % (p[0], sym(p[1]))),
        'true' if fx['fpOne'] else 'false', lst(fx['scaled']))
    global ADV
    if ADV is None: ADV = adviceIdx()
    hints = 'Data.adviceFn%d.2.2' % ADV[n]
    defs = []
    tidx, tarms, tcalls = tgt
    names = {}
    for nm, tab, what in (('frameArm', tarms, 'a table jump\'s arms, as offsets'), ('frameCallee', tcalls, 'a table call\'s callees\' pcs')):
        for k, ps in sorted(tab.items()):
            names[(nm, k)] = '%s%d' % (nm, k)
            defs.append('def %s%d : List ℕ := %s\n' % (nm, k, lst(ps)))
    cutT = '.nil'
    if cuts:
        cn = {}
        for i in cuts:
            cn[i] = 'frameCut%d' % len(cn)
            defs.append('/-- `%s`: its walk at offset %d. -/\nnoncomputable def %s : Option CoreMode.FSt × List (ℕ × List ℕ × '
                        'CoreMode.FSt) :=\n  %s\n\n' % (n, i, cn[i], cutLit(w.cutSt[i])))
        cutT = MG.trie(cn, lambda x: x)
    if rt:
        O, S = '%s.pairO' % MG.fnq(n), '%s.pairS' % MG.fnq(n)
    else:
        O, S = MG.bigTrie('frameO', 'Unit', {i: () for i in D['O'].get(n, [])}, lambda _: '()', defs), '.nil'
    lit = ('⟨%s, %d, %d, %s.modeSig, %s, %d, %s, %s, %s, %s, %s, %s, %s, %s⟩' % (
        facts, entry, ln, MG.fnq(n), MG.trie(sigs, lambda s: s), D['halt'], hints,
        MG.trie(nzr, lambda os: lst(os)), MG.trie(tidx, str), MG.trie({k: names[('frameArm', k)] for k in tarms}, lambda x: x),
        MG.trie({k: names[('frameCallee', k)] for k in tcalls}, lambda x: x), O, S, cutT))
    return lit, defs, packs


def header(mod, what):
    return ('/-\n  %s\n\n  Generated by `scripts/core-mode/frame_gen.py`; do not edit.\n  %s\n-/\n\nmodule\n\n' % (mod, what))


def imports(pack, packs, gens=()):
    out = ['public import LeanVM.Guest.CoreMode.Frame', 'public import LeanVM.Guest.Data.Pows',
           'public import Statement.Data.AdviceHints',
           'public import LeanVM.Guest.Pack.«%s».Bundle' % pack]
    out += ['public import %s' % pair_mod(g, n) for g, n in sorted(set(gens))]
    out += ['public import LeanVM.Guest.Pack.«%s».ModeSig' % p for p in sorted(packs | {pack})]
    return '\n'.join(out) + '\n\nset_option Elab.async false\n'


def pair_mod(g, n):
    """The module of function `n`'s pairing (`pairO`, `pairS`, `pair_ok`) in pack `g`: the pack's, or a long
    function's own, checked in windows."""
    gen = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'LeanVM', 'Guest', 'CoreMode', 'Gen')
    if os.path.exists(os.path.join(gen, g, n, 'Ok.lean')):
        # its oracle only (`pairO`, `pairS`), not its windows' checks
        return 'LeanVM.Guest.CoreMode.Gen.«%s».«%s».Ctx' % (g, n)
    return 'LeanVM.Guest.CoreMode.Gen.«%s».Pair' % g


def ns(n, body):
    return ('\nnamespace LeanVM.Guest.Fn.«%s»\nopen LeanVM.Guest LeanVM.Guest.Exec\n@[expose] public section\n%s'
            'end\nend LeanVM.Guest.Fn.«%s»\n' % (n, body, n))


def qual(ns_, text):
    """A function's top-level declarations named in its namespace (`Fn.«ns».name`), in a section shared with others."""
    return re.sub(r'^((?:noncomputable )?def )(\w+)', lambda m: '%sFn.«%s».%s' % (m.group(1), ns_, m.group(2)), text,
                  flags=re.M)


def funDef(D, n, lit, defs):
    return ''.join(defs) + 'noncomputable def frameFun : CoreMode.FFun :=\n  %s\n\n' % lit


def main(argv):
    only = None; fns_only = None
    if '--only' in argv: only = argv[argv.index('--only') + 1:]
    if '--fns' in argv: fns_only = argv[argv.index('--fns') + 1:]
    D = FD.load(os.environ['MODE_CERT_CACHE'], os.environ.get('FRAME_CACHE'))
    global ROUTE
    import route, heap
    ROUTE = route.route_sub()
    gen_pack = {k: v[0] for k, v in heap.pack_of().items()}
    for n, f in D['fns'].items():
        f['ns'] = f.get('ns', n)
        # a function the compiler names apart from its stable name (a loop helper `__loopN`): on the route by the latter
        if f['ns'] != n and f['ns'] in ROUTE:
            ROUTE[n] = ROUTE[f['ns']]
            gen_pack[n] = gen_pack[f['ns']]
    files = {}
    stats = collections.Counter()
    for p, names in sorted(MG.packs().items()):
        if only and p not in only: continue
        names = [n for n in names if not fns_only or n in fns_only]
        if not names: continue
        groups = []; cur = []; size = 0; long_ = []
        for n in names:
            c = D['fns'][n]['count']
            if c > WIN: long_.append(n); continue
            if cur and size + c > CHUNK: groups.append(cur); cur = []; size = 0
            cur.append(n); size += c
        if cur: groups.append(cur)
        for k, g in enumerate(groups):
            body = []; packs = set(); gens = set()
            for n in g:
                lit, defs, ps = fnData(D, n, [])
                packs |= ps
                ns_ = D['fns'][n]['ns']
                if n in ROUTE: gens.add((gen_pack[n], ns_))
                body.append(qual(ns_, funDef(D, n, lit, defs)) + 'theorem Fn.«%s».frameOk : CoreMode.frameOk frameFun '
                            'code.chunks.flatten = true := by\n  decide +kernel\n' % ns_)
                stats['fns'] += 1
            mod = 'LeanVM.Guest.CoreMode.Pack.«%s».Frame%d' % (p, k)
            files[os.path.join(OUT, p, 'Frame%d.lean' % k)] = (
                header(mod, 'The kernel\'s checks of compiled functions\' frame walks.') + imports(p, packs, gens) +
                '\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\nopen LeanVM.Guest.Exec\n\n'
                '@[expose] public section\n\n' + ''.join(body) + 'end\n\nend LeanVM.Guest\n')
        for k, n in enumerate(long_):
            cuts = cutsFor(D, n)
            lit, defs, packs = fnData(D, n, cuts)
            ns_ = D['fns'][n]['ns']
            mod = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameD%d' % (p, k)
            files[os.path.join(OUT, p, 'FrameD%d.lean' % k)] = (
                header(mod, 'The frame walk\'s data of `%s`, checked in windows.' % n) +
                imports(p, packs, [(gen_pack[n], ns_)] if n in ROUTE else []) +
                ns(ns_, funDef(D, n, lit, defs)))
            bounds = [0] + cuts + [D['fns'][n]['count']]
            for m in range(len(bounds) - 1):
                a, b = bounds[m], bounds[m + 1]
                wm = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameD%dW%d' % (p, k, m)
                files[os.path.join(OUT, p, 'FrameD%dW%d.lean' % (k, m))] = (
                    header(wm, 'A window of `%s`\'s frame walk.' % n) +
                    'public import LeanVM.Guest.CoreMode.Pack.«%s».FrameD%d\n\nset_option Elab.async false\n' % (p, k) +
                    ns(ns_, '/-- `%s`: its frame walk accepts offsets %d to %d. -/\ntheorem frameWin%d : CoreMode.frameWin '
                       'frameFun code.chunks.flatten %d %d = true := by\n  decide +kernel\n' % (n, a, b, m, a, b)))
            pairs = list(zip(bounds[:-1], bounds[1:]))
            wl = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameL%d' % (p, k)
            chain = 'List.forall_mem_nil _'
            for m in reversed(range(len(pairs))):
                chain = 'List.forall_mem_cons.2 ⟨frameWin%d, %s⟩' % (m, chain)
            files[os.path.join(OUT, p, 'FrameL%d.lean' % k)] = (
                header(wl, 'The windows of `%s`\'s frame walk, chained.' % n) +
                'public import LeanVM.Guest.CoreMode.FrameWin\n' +
                ''.join('public import LeanVM.Guest.CoreMode.Pack.«%s».FrameD%dW%d\n' % (p, k, m) for m in range(len(pairs))) +
                '\nset_option Elab.async false\n' +
                ns(ns_, '/-- `%s`: its hints by pc increase. -/\ntheorem frameHints : Mode.pcsIncr frameFun.hints = true := by\n'
                   '  decide +kernel\n\n/-- `%s`: its code\'s length. -/\ntheorem frameLen : code.chunks.flatten.length = %d := by\n'
                   '  decide +kernel\n\n/-- `%s`: its frame walk accepts its code, its windows chained. -/\n'
                   'theorem frameAcc : CoreMode.FrameAcc frameFun code.chunks.flatten := by\n'
                   '  have hl : frameFun.len = code.chunks.flatten.length := by rw [frameLen]; rfl\n'
                   '  have hc0 : frameFun.cuts.get 0 = none := rfl\n'
                   '  refine CoreMode.frameAcc_of_wins frameHints hl %s 0 _ (by rw [frameLen]; decide) rfl\n'
                   '    ⟨_, by simp [CoreMode.winStart, hc0], fun _ _ ↦ rfl⟩ ?_\n'
                   '  rw [frameLen]\n  show ∀ p ∈ %s, CoreMode.frameWin frameFun code.chunks.flatten p.1 p.2 = true\n'
                   '  exact %s\n' % (n, n, D['fns'][n]['count'], n, lst(bounds[1:-1]),
                                    lst(pairs, lambda q: '(%d, %d)' % q), chain)))
            stats['fns'] += 1; stats['windows'] += len(bounds) - 1
    lines = 0
    for path, text in sorted(files.items()):
        text = wrap(text)
        lines += text.count('\n')
        os.makedirs(os.path.dirname(path), exist_ok=True)
        old = open(path).read() if os.path.exists(path) else None
        if old != text: open(path, 'w').write(text)
    print('files', len(files), 'functions', stats['fns'], 'windows', stats['windows'], 'lines', lines)


if __name__ == '__main__':
    main(sys.argv[1:])
