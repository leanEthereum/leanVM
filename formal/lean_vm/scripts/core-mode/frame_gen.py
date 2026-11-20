"""Writes the frame walk's checks (`LeanVM/Guest/CoreMode/Frame.lean`): per pack,
`LeanVM/Guest/CoreMode/Pack/<pack>/Frame{k}.lean`, each function's data (`CoreMode.FFun`: its
executor facts, its signature and its callees', its hints, residual divisors, table targets, the
oracle) with the kernel's check of its walk (`frameOk … = true := by decide +kernel`); a long
function in windows (`frameWin`), each its own module `FrameW{k}.lean`, from the cut states
`frame.py` computes. For a function on the core route, beside its walk, its frame interface's data
(`envC`, its callees' signatures by key, `CoreMode.envOf`; `funC`, its entry, length, signature
(`sigc.py`) and nonzero residuals). A function on the core route takes its oracle and stores from its pairing and its
residual divisors from its own walk (`frame_run.own_nz`); one off the route, from the mode walk's inference
(`frame_data.py`, `MODE_CERT_CACHE`, read only then). The frame signatures are the frame layout's (`compiled.fsig`).
Usage: [MODE_CERT_CACHE=FILE] python3 -I scripts/core-mode/frame_gen.py [--only PACK...] [--fns NAME...]"""
import os, re, sys, collections, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frame as FR  # noqa: E402
import frame_data as FD  # noqa: E402
import frame_run as RUN  # noqa: E402
from pmap import pmap  # noqa: E402
import compiled as MG  # noqa: E402

OUT = os.path.join(FD.ROOT, 'CoreMode', 'Pack')
# a module's checks: at most this many instructions
CHUNK = int(os.environ.get('FRAME_CHUNK', 12000))
# a function longer than this is checked in windows of about this many instructions
WIN = int(os.environ.get("FRAME_WIN", 7000))


def wrap(text, width=100):
    """`compiled.wrap` in linear time: long lines broken at spaces, the rest indented."""
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


# the function whose data is being written: its entry, length and key; and every function by entry (`codePtr`)
CUR = [0, 0, None]
BYENTRY = {}
CALLEES = set()


def codePtr(e):
    """An exponent of `g` as the data names it: an offset of the current function from its entry, a function's entry
    by its key (the glue's `Fn.«k».entry`) if a callee's, or the number."""
    if CUR[0] <= e < CUR[0] + CUR[1]:
        return '(%s.entry + %d)' % (MG.fnq(CUR[2]), e - CUR[0])
    if e in BYENTRY and e in CALLEES:
        return '%s.entry' % MG.fnq(BYENTRY[e])
    return str(e)


def sym(s):
    if s[0] == 'z': return '.zero'
    return '(.%s %s)' % (s[0], codePtr(s[1]) if s[0] == 'gp' else s[1])


def unitTrie(keys):
    """A set of keys: the list of its keys (`CoreMode.unitOf`, `CoreMode/TrieOf.lean`)."""
    ks = sorted(set(keys))
    return '(CoreMode.unitOf %s)' % lst(ks) if ks else '.nil'


def natTrie(d): return MG.trie(d, str)


def hqk(q, o): return q * FR.HQ_SHIFT + o


def fstLit(A):
    """A state of `frame.py` as a literal `CoreMode.FSt` (its `Exec` state restarted)."""
    env = 'envOf %s' % lst(sorted(A.st.env.items()), lambda p: '(%d, %s)' % (p[0], sym(p[1])))
    return '⟨St.init (%s), %s, %s, %s, %s, %s, %s⟩' % (
        env, unitTrie(A.w), unitTrie(A.nz), unitTrie(hqk(q, o) for q, o in A.hq),
        unitTrie(hqk(q, o) for q, o in A.hs), natTrie(A.cp), natTrie(A.one))


ROUTE = {}


# a function whose windows at `WIN` instructions take past 6.5 GB a module: its own size (`main_loop2`,
# `__loop2_main` to the compiler: its walk reads its packed alignment context)
WINS = {'__loop2_main': 3000}


def cutsFor(D, n):
    """Offsets to cut a long function at, about every `WIN` instructions (`WINS`)."""
    f = D['fns'][n]
    w = WINS.get(n, WIN)
    return list(range(w, f['count'] - w // 4, w))


def cutLit(c):
    """A cut (the live path and the pending groups) as a literal."""
    cur, pend = c
    return '(%s, %s)' % ('none' if cur is None else '(some %s)' % fstLit(cur),
                         lst(pend, lambda g: '(%d, %s, %s)' % (g[0], lst(g[1]), fstLit(g[2]))))


def fnData(D, n, cuts):
    """The function's `FFun` literal, its callees' packs, and the walk (with its cut states)."""
    f = D['fns'][n]
    rt = ROUTE.get(n)
    O_ = set(rt['O']) if rt else set(D['O'].get(n, []))
    S_ = set(rt['S']) if rt else set()
    # a function on the core route: its own residual divisors, not the mode walk's
    F, entry, ln, sig, tgt, nzr = RUN.inputs(D, n, RUN.own_nz(D, n, O_, S_) if rt else None)
    w = FR.Walk(F, entry, ln, sig, D['fsig'], f['hints'], nzr, tgt, O_, D['halt'], S=S_)
    w.cutAt = set(cuts)
    w.run(f['ops'])
    byentry = {g['entry']: m for m, g in D['fns'].items()}
    BYENTRY.clear(); BYENTRY.update(byentry); CUR[:] = [entry, ln, n]
    CALLEES.clear(); CALLEES.update(w.used); CALLEES.update(pc for ps in tgt[2].values() for pc in ps)
    sigs = {pc: byentry[pc] for pc in sorted(w.used)}
    if rt and rt.get('kind') == 'l':
        # a leaf loop helper on the core route: its walk is told no callee (`CoreMode.loopShapeOk`)
        sigs = {}
    if rt and rt.get('kind') == 'lc':
        # a loop helper with calls on the core route: its walk is told its environment's callees, its own entry
        # among them (`CoreMode.LoopOkC.fsigs`)
        sigs[entry] = n
    packs = {D['fns'][byentry[pc]]['pack'] for pc in w.used}
    if rt: packs |= {D['fns'][m]['pack'] for m in MG.calleesOf(n)}
    fx = D['facts'][n]
    facts = '{ env := %s, fpOne := %s, pows := fpows, scaled := %s }' % (
        lst(sorted(fx['env'].items()), lambda p: '(%d, %s)' % (p[0], sym(p[1]))),
        'true' if fx['fpOne'] else 'false', lst(fx['scaled']))
    hints = 'advice.2.2'
    defs = []
    tidx, tarms, tcalls = tgt
    names = {}
    for nm, tab, f in (('frameArm', tarms, str), ('frameCallee', tcalls, lambda pc: '%s.entry' % MG.fnq(byentry[pc]))):
        for k, ps in sorted(tab.items()):
            names[(nm, k)] = '%s%d' % (nm, k)
            defs.append('def %s%d : List ℕ := %s\n' % (nm, k, lst(ps, f)))
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
    nzT, tidxT = MG.trie(nzr, lambda os: lst(os)), MG.trie(tidx, str)
    armsT = MG.trie({k: names[('frameArm', k)] for k in tarms}, lambda x: x)
    callsT = MG.trie({k: names[('frameCallee', k)] for k in tcalls}, lambda x: x)
    if rt and D['halt'] == 524287 and cutT == '.nil':
        # one `frame_fn%` (`CoreMode/FrameLit.lean`): the clauses that are not the defaults
        f = D['fns'][n]
        q = lambda m: MG.fnq(m)[3:]
        callees = sorted({q(m) for m in MG.calleesOf(n)})
        fsigs = sorted({q(m) for m in sigs.values()})
        fnz = {i: [('nz', o) for o in os_] for i, os_ in nzr.items() if os_}
        cl = []
        if fsigs != callees: cl.append('sigs [%s]' % ', '.join(fsigs))
        if fx['env']: cl.append('env %s' % lst(sorted(fx['env'].items()), lambda p: '(%d, %s)' % (p[0], sym(p[1]))))
        if fx['fpOne']: cl.append('fpOne')
        if fx['scaled']: cl.append('scaled %s' % lst(fx['scaled']))
        for kw, t in (('nzr', nzT), ('tidx', tidxT), ('arms', armsT), ('calls', callsT)):
            if t != '.nil': cl.append('%s %s' % (kw, t))
        if fnz: cl.append('fnz %s' % MG.trie(fnz, lambda l: MG.lst(l, MG.res)))
        if n == 'main': cl.append('main')
        assert ln == f['count']
        return ('frame_fn%% %s %d [%s]%s\n' % (q(n), ln, ', '.join(callees), ''.join(' ' + c for c in cl))), defs, packs
    if rt:
        defs += envDefs(D, n, nzr)
    lit = ('⟨%s, %s.entry, %d, %s.csig, %s, %d, %s, %s, %s, %s, %s, %s, %s, %s⟩' % (
        facts, MG.fnq(n), ln, MG.fnq(n), sigTrie(sigs.values()), D['halt'], hints, nzT, tidxT, armsT, callsT, O, S, cutT))
    return lit, defs, packs


def header(mod, what):
    return ('/-\n  %s\n\n  Generated by `scripts/core-mode/frame_gen.py`; do not edit.\n  %s\n-/\n\nmodule\n\n' % (mod, what))


def sigTrie(ns):
    """The signatures of functions `ns` by entry, by key (`CoreMode.sigTrie`); `.nil` for none."""
    if not ns: return '.nil'
    return '(CoreMode.sigTrie %s)' % lst(sorted({MG.fnq(m) for m in ns}), lambda q: '%s.csig' % q)


def envDefs(D, n, nzr):
    """A function on the core route: its frame interface's environment (its callees' signatures) and data (its
    entry, length, signature, nonzero residuals: its walk's residual divisors `nzr`), `Mode.Cert`'s parts."""
    f = D['fns'][n]
    nz = {i: [('nz', o) for o in os_] for i, os_ in nzr.items() if os_}
    return ['noncomputable def envC : Mode.Env := CoreMode.envOf %s\n' % (
                lst(sorted({MG.fnq(m) for m in MG.calleesOf(n)}), lambda q: '%s.csig' % q)),
            'noncomputable def funC : Mode.Fun := ⟨%s.entry, %d, %s.csig, .nil, %s, .nil, %s, .nil⟩\n' % (
                MG.fnq(n), f['count'], MG.fnq(n), MG.trie(nz, lambda l: MG.lst(l, MG.res)) if nz else '.nil',
                'true' if n == 'main' else 'false')]


def imports(pack, packs, gens=(), glue=(), env=False):
    out = ['public import LeanVM.Guest.CoreMode.Frame', 'public import LeanVM.Guest.CoreMode.FrameLit', 'public import LeanVM.Guest.CoreMode.GlueP.«%s»' % pack,
           'public import LeanVM.Guest.CoreMode.%s' % ('Env' if env else 'SigTrie'),
           *['public import LeanVM.Guest.CoreMode.GlueA.«%s»' % q for q in sorted(set(glue) or {pack})],
           'public import LeanVM.Guest.Pack.«%s».Bundle' % pack]
    out += ['public import %s' % pair_mod(g, n) for g, n in sorted(set(gens))]
    out += ['public import LeanVM.Guest.CoreMode.Sig.«%s»' % p for p in sorted(packs | {pack})]
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
    return re.sub(r'^((?:noncomputable )?(?:def|theorem) )(\w+)', lambda m: '%sFn.«%s».%s' % (m.group(1), ns_, m.group(2)), text,
                  flags=re.M)


FPOWS = None


def fpowsDef(k):
    """`k`'s frame walk's powers of `g`: the immediates of its code's `SET`s that `Data.powTree` names (code
    pointers among them: glue, `CoreMode/GlueP/<pack>.lean`), checked by the kernel."""
    global FPOWS
    if FPOWS is None:
        import pows as PW
        G = PW.global_pows(); FPOWS = {}
        for path in glob.glob(os.path.join(FD.ROOT, 'Pack', '*', 'Bundle*.lean')):
            for m in PW.NS.finditer(open(path, encoding='utf-8').read()):
                FPOWS.setdefault(m.group(1), set()).update(int(x) for x in PW.SET.findall(m.group(2)) if int(x) in G)
        FPOWS = {key: PW.tree(sorted((x, G[x]) for x in xs)) for key, xs in FPOWS.items()}
    return ('noncomputable def Fn.«%s».fpows : PowTree :=\n  %s\n'
            'theorem Fn.«%s».fpows_ok : fpows.OkW :=\n  PowTree.okW_of_okWB (by decide +kernel)\n' % (k, FPOWS.get(k, '.leaf'), k))


def funDef(D, n, lit, defs):
    return ''.join(defs) + 'noncomputable def frameFun : CoreMode.FFun :=\n  %s\n\n' % lit


def main(argv):
    only = None; fns_only = None
    if '--only' in argv: only = argv[argv.index('--only') + 1:]
    if '--fns' in argv: fns_only = argv[argv.index('--fns') + 1:]
    global ROUTE
    import route, heap
    ROUTE = route.route_sub()
    gen_pack = {k: v[0] for k, v in heap.pack_of().items()}
    fns = MG.code()['fns']
    for n, f in fns.items():
        # a function the compiler names apart from its stable name (a loop helper `__loopN_f`): on the route by the latter
        if f['ns'] != n and f['ns'] in ROUTE:
            ROUTE[n] = ROUTE[f['ns']]
            gen_pack[n] = gen_pack[f['ns']]
    # the mode walk's inference, only for the functions off the core route
    off = [n for p, names in MG.packs().items() if not only or p in only for n in names
           if n not in ROUTE and (not fns_only or n in fns_only)]
    if off and not os.environ.get('MODE_CERT_CACHE'):
        raise SystemExit('frame_gen: %d functions off the core route need MODE_CERT_CACHE' % len(off))
    D = FD.load(os.environ['MODE_CERT_CACHE'] if off else None, os.environ.get('FRAME_CACHE'), only=off)
    files = {}
    stats = collections.Counter()
    def one_pack(item):
        """A pack's frame modules and their counts."""
        p, names = item
        files, stats = {}, collections.Counter()
        if only and p not in only: return files, stats
        names = [n for n in names if not fns_only or n in fns_only]
        if not names: return files, stats
        groups = []; cur = []; size = 0; long_ = []
        for n in names:
            c = D['fns'][n]['count']
            if c > WIN: long_.append(n); continue
            if cur and size + c > CHUNK: groups.append(cur); cur = []; size = 0
            cur.append(n); size += c
        if cur: groups.append(cur)
        for k, g in enumerate(groups):
            body = []; packs = set(); gens = set(); env = False
            for n in g:
                lit, defs, ps = fnData(D, n, [])
                packs |= ps
                if n in ROUTE: env = True
                ns_ = D['fns'][n]['ns']
                if n in ROUTE: gens.add((gen_pack[n], ns_))
                if lit.startswith('frame_fn% '):
                    body.append(qual(ns_, ''.join(defs)) + lit)
                else:
                    body.append(qual(ns_, funDef(D, n, lit, defs)) + 'theorem Fn.«%s».frameOk : CoreMode.frameOk frameFun '
                                'code.chunks.flatten = true := by\n  decide +kernel\n' % ns_)
                stats['fns'] += 1
            mod = 'LeanVM.Guest.CoreMode.Pack.«%s».Frame%d' % (p, k)
            files[os.path.join(OUT, p, 'Frame%d.lean' % k)] = (
                header(mod, 'The kernel\'s checks of compiled functions\' frame walks.') + imports(p, packs, gens, {gen_pack.get(D['fns'][n]['ns'], p) for n in g}, env) +
                '\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\nopen LeanVM.Guest.Exec\n\n'
                '@[expose] public section\n\n' + ''.join(body) + 'end\n\nend LeanVM.Guest\n')
        for k, n in enumerate(long_):
            cuts = cutsFor(D, n)
            lit, defs, packs = fnData(D, n, cuts)
            ns_ = D['fns'][n]['ns']
            mod = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameD%d' % (p, k)
            files[os.path.join(OUT, p, 'FrameD%d.lean' % k)] = (
                header(mod, 'The frame walk\'s data of `%s`, checked in windows.' % n) +
                'public import LeanVM.Guest.CoreMode.TrieOf\n' +
                imports(p, packs, [(gen_pack[n], ns_)] if n in ROUTE else [], {gen_pack.get(ns_, p)}, n in ROUTE) +
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
        return files, stats
    # each pack on its own, in worker processes (`pmap.py`)
    for fs, st in pmap(one_pack, sorted(MG.packs().items())):
        files.update(fs)
        stats.update(st)
    for p, names in sorted(MG.packs().items()):
        if only and p not in only: continue
        files[os.path.join(FD.ROOT, 'CoreMode', 'GlueP', '%s.lean' % p)] = (
            header('LeanVM.Guest.CoreMode.GlueP.«%s»' % p, 'The powers of `g` the code of each function of the pack names, '
                   'code pointers among them.') +
            'public import LeanVM.Guest.Pow\n\nset_option Elab.async false\nset_option linter.all false\n'
            'set_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\nopen LeanVM.Guest.Exec\n\n'
            '@[expose] public section\n\n' +
            ''.join(fpowsDef(D['fns'][n]['ns']) for n in sorted(names, key=lambda n: D['fns'][n]['ns'])) +
            '\nend\n\nend LeanVM.Guest\n')
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
