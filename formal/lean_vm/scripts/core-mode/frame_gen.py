"""Writes the frame walk's checks (`LeanVM/Guest/CoreMode/Frame.lean`): per pack,
`LeanVM/Guest/CoreMode/Pack/<pack>/Frame{k}.lean`, each function's data (`CoreMode.FFun`: its
executor facts, its signature and its callees', its hints, residual divisors, table targets, the
oracle) with the kernel's check of its walk (`frameOk … = true := by decide +kernel`); a long
function in windows (`frameWin`), each its own module `FrameD{k}W{m}.lean`, from the cut states
`frame.py` computes (its data `FrameD{k}.lean`, the check that its oracle's list is the pairing's
`FrameO{k}.lean`, the chain `FrameL{k}.lean`). For a function on the core route, beside its walk, its frame interface's data
(`envC`, its callees' signatures by key, `CoreMode.envOf`; `funC`, its entry, length, signature
(`sigc.py`) and nonzero residuals). A function takes its oracle and stores from its pairing and its residual divisors
from its own walk (`frame_run.own_nz`). The frame signatures are the frame layout's (`compiled.fsig`).
Usage: python3 -I scripts/core-mode/frame_gen.py [--only PACK...] [--fns NAME...]"""
import os, re, sys, collections, glob
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
import frame as FR  # noqa: E402
import frame_data as FD  # noqa: E402
import frame_run as RUN  # noqa: E402
from pmap import pmap  # noqa: E402
import compiled as MG  # noqa: E402

OUT = os.path.join(FD.ROOT, 'CoreMode', 'Pack')
OUT_GLUE = os.path.join(FD.ROOT, 'CoreMode', 'GlueA')
import windows  # noqa: E402
# a module's checks: at most this many instructions; a function longer than `WIN` is checked in windows of about it
CHUNK, WIN = windows.FRAME_CHUNK, windows.FRAME_WIN


def wrap(text, width=100):
    """Long lines broken at spaces, the rest indented, each piece filled up to `width` (`compiled.wrap` keeps them
    shorter: the frame walks' modules keep this breaking)."""
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


def bitsLit(keys):
    """A set of frame offsets as the bits of a number (`CoreMode/Bits.lean`), in hexadecimal."""
    assert all(0 <= k < 2 ** FR.ENV_DEPTH - 1 for k in keys)
    return hex(sum(1 << k for k in set(keys)))


def natTrie(d): return MG.trie(d, str)


def hqk(q, o): return q * FR.HQ_SHIFT + o


# the current function's jump-table reads (`DEREF`s whose word cell the next `JUMP` jumps through) and its first slot
# as the glue names it (`Fn.«k».jt0`, `glue.py`): a cut's `hq` keys at those slots are named from it, so a cut stays
# put when the jump table moves
TABQ = set()
JT0 = [None]


def hqLit(q, o):
    if (q, o) in TABQ and JT0[0] is not None:
        d = o - JT0[0]
        return '(%d * %d + (%s.jt0 %s %d))' % (q, FR.HQ_SHIFT, MG.fnq(CUR[2]), '+' if d >= 0 else '-', abs(d))
    return str(hqk(q, o))


def hqTrie(keys):
    """`unitTrie` of `hq`'s pairs, a jump-table read's key named from the glue's first slot."""
    ks = sorted(set(keys))
    return '(CoreMode.unitOf %s)' % lst(ks, lambda p: hqLit(*p)) if ks else '.nil'


def jt0Of(n):
    """The glue's first jump-table slot of `n` (`CoreMode/GlueA/*.lean`), or None."""
    if not JT0S:
        for f in glob.glob(os.path.join(OUT_GLUE, '*.lean')):
            for k, v in re.findall(r'^abbrev Fn\.«([^»]+)»\.jt0 : ℕ := (\d+)$', open(f, encoding='utf-8').read(), re.M):
                JT0S[k] = int(v)
    return JT0S.get(n)


JT0S = {}
# where a pack of one frame module takes its powers of `g`
POWS = '\x00pows\x00'


def fstLit(A):
    """A state of `frame.py` as a literal `CoreMode.FSt` (its `Exec` state restarted)."""
    env = 'envOf %s' % lst(sorted(A.st.env.items()), lambda p: '(%d, %s)' % (p[0], sym(p[1])))
    return '⟨St.init (%s), %s, %s, %s, %s, %s, %s⟩' % (
        env, bitsLit(A.w), bitsLit(A.nz), hqTrie(A.hq),
        unitTrie(hqk(q, o) for q, o in A.hs), natTrie(A.cp), natTrie(A.one))


ROUTE = {}


# a function's own window size (`windows.py`)
WINS = windows.own('FRAME_WIN')


def cutsFor(D, n):
    """Offsets to cut a long function at, about every `WIN` instructions (`WINS`)."""
    f = D['fns'][n]
    w = WINS.get(f['ns'], WIN)
    return list(range(w, f['count'] - w // 4, w))


def cutLit(c):
    """A cut (the live path and the pending groups) as a literal."""
    cur, pend = c
    return '(%s, %s)' % ('none' if cur is None else '(some %s)' % fstLit(cur),
                         lst(pend, lambda g: '(%d, %s, %s)' % (g[0], lst(g[1]), fstLit(g[2]))))


def fnData(D, n, cuts):
    """The function's `FFun` literal, its callees' packs, and the walk (with its cut states)."""
    f = D['fns'][n]
    rt = ROUTE[n]
    O_, S_ = set(rt['O']), set(rt['S'])
    F, entry, ln, sig, tgt, nzr = RUN.inputs(D, n, RUN.own_nz(D, n, O_, S_))
    w = FR.Walk(F, entry, ln, sig, D['fsig'], f['hints'], nzr, tgt, O_, D['halt'], S=S_)
    w.cutAt = set(cuts)
    w.run(f['ops'])
    byentry = {g['entry']: m for m, g in D['fns'].items()}
    BYENTRY.clear(); BYENTRY.update(byentry); CUR[:] = [entry, ln, n]
    ops = f['ops']
    TABQ.clear()
    TABQ.update((a[0], a[1]) for i, (op, a) in enumerate(ops[:-1])
                if op == 'deref' and a[3] == '.cell' and ops[i + 1][0] == 'jump' and ops[i + 1][1][1] == a[2])
    JT0[0] = jt0Of(D['fns'][n]['ns'])
    CALLEES.clear(); CALLEES.update(w.used); CALLEES.update(pc for ps in tgt[2].values() for pc in ps)
    sigs = {pc: byentry[pc] for pc in sorted(w.used)}
    if rt.get('kind') == 'lc':
        # a loop helper on the core route: its walk is told its environment's callees, its own entry
        # among them (`CoreMode.LoopOkC.fsigs`)
        sigs[entry] = n
    packs = {D['fns'][byentry[pc]]['pack'] for pc in w.used} | {D['fns'][m]['pack'] for m in MG.calleesOf(n)}
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
            defs.append('def %s%d : List ℕ := data%% %s\n' % (nm, k, lst(ps, f)))
    cutT, cutW = '.nil', 1
    if cuts:
        # the cuts at multiples of the stride, by index (`FFun.cutAt`)
        cutW = cuts[0]
        assert all(i % cutW == 0 for i in cuts)
        cn = {}
        for i in cuts:
            cn[i // cutW] = 'frameCut%d' % len(cn)
            defs.append('/-- `%s`: its walk at offset %d. -/\nnoncomputable def %s : Option CoreMode.FSt × List (ℕ × List ℕ × '
                        'CoreMode.FSt) :=\n  data%% %s\n\n' % (n, i, cn[i // cutW], cutLit(w.cutSt[i])))
        cutT = MG.trie(cn, lambda x: x)
    O, S = '%s.pairO' % MG.fnq(n), '%s.pairS' % MG.fnq(n)
    nzT, tidxT = MG.trie(nzr, lambda os: lst(os)), MG.trie(tidx, str)
    armsT = MG.trie({k: names[('frameArm', k)] for k in tarms}, lambda x: x)
    callsT = MG.trie({k: names[('frameCallee', k)] for k in tcalls}, lambda x: x)
    if cutT == '.nil':
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
    defs += envDefs(D, n, nzr)
    lit = ('⟨%s, %s.entry, %d, %s.csig, %s, %d, %s, %s, %s, %s, %s, %s, data%% %s, %s, %d, %s⟩' % (
        facts, MG.fnq(n), ln, MG.fnq(n), sigTrie(sigs.values()), D['halt'], hints, nzT, tidxT, armsT, callsT, O,
        lst(sorted(O_)), S, cutW, cutT))
    return lit, defs, packs


header = genfiles.header('core-mode/frame_gen.py')


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


def imports(pack, packs, gens, glue, pows=True):
    out = ['public import LeanVM.Guest.CoreMode.Frame', 'public import LeanVM.Guest.CoreMode.FrameLit',
           'public import LeanVM.Guest.DataLit',
           *(['public import LeanVM.Guest.CoreMode.GlueP.«%s»' % pack] if pows else ['public import LeanVM.Guest.Pow']),
           'public import LeanVM.Guest.CoreMode.Env',
           *['public import LeanVM.Guest.CoreMode.GlueA.«%s»' % q for q in sorted(set(glue) or {pack})],
           'public import LeanVM.Guest.Pack.«%s».Bundle' % pack]
    out += ['public import %s' % pair_mod(g, n) for g, n in sorted(set(gens))]
    out += ['public import LeanVM.Guest.CoreMode.Sig.«%s»' % p for p in sorted(packs | {pack})]
    # the walks read the advice's values, which `Statement/Data` does not expose
    out += ['import all Statement.Data.AdviceHints']
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
    pointers among them: glue, `CoreMode/GlueP/<pack>.lean`, or the pack's frame module when it has one), checked by
    the kernel."""
    global FPOWS
    if FPOWS is None:
        import pows as PW
        G = PW.global_pows(); FPOWS = {}
        for key, (_, blk) in MG.BD.bundle_blocks().items():
            FPOWS.setdefault(key, set()).update(int(x) for x in PW.SET.findall(blk) if int(x) in G)
        FPOWS = {key: PW.tree(sorted((x, G[x]) for x in xs)) for key, xs in FPOWS.items()}
    return ('noncomputable def Fn.«%s».fpows : PowTree :=\n  %s\n'
            'theorem Fn.«%s».fpows_ok : fpows.OkW :=\n  PowTree.okW_of_okWB (by decide +kernel)\n' % (k, FPOWS.get(k, '.leaf'), k))


def chunk_lens(k):
    """The lengths of function `k`'s code chunks (`CompiledFunction.chunks`)."""
    BD = MG.BD
    if k not in BD.bundle_blocks():
        raise SystemExit('frame_gen: no code of %s' % k)
    return [len(ch) for ch in BD.chunks_of(BD.bundle_blocks()[k][1])]


def cut_of(clens, i):
    """Offset `i` of the code as a cut `(p, r)` of its chunks (`Bridge.PCut`); the code's end is `(len, 0)`."""
    p = 0
    while p < len(clens) and i >= clens[p]:
        i -= clens[p]; p += 1
    assert p < len(clens) or i == 0
    return '(%d, %d)' % (p, i)


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
    off = [n for p, names in MG.packs().items() if not only or p in only for n in names
           if n not in ROUTE and (not fns_only or n in fns_only)]
    if off:
        raise SystemExit('frame_gen: off the core route: %s' % ', '.join(sorted(off)))
    D = FD.load()
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
            body = []; packs = set(); gens = set()
            for n in g:
                lit, defs, ps = fnData(D, n, [])
                packs |= ps
                ns_ = D['fns'][n]['ns']
                gens.add((gen_pack[n], ns_))
                # one `frame_fn%` a function: a short one has no cuts
                body.append(qual(ns_, ''.join(defs)) + lit)
                stats['fns'] += 1
            # a pack of one module holds its powers of `g` itself, `GlueP` otherwise
            alone = len(groups) == 1 and not long_
            mod = 'LeanVM.Guest.CoreMode.Pack.«%s».Frame%d' % (p, k)
            files[os.path.join(OUT, p, 'Frame%d.lean' % k)] = (
                header(mod, 'The kernel\'s checks of compiled functions\' frame walks.') +
                imports(p, packs, gens, {gen_pack.get(D['fns'][n]['ns'], p) for n in g}, not alone) +
                '\nset_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\nopen LeanVM.Guest.Exec\n\n'
                '@[expose] public section\n\n' + (POWS if alone else '') + ''.join(body) + 'end\n\nend LeanVM.Guest\n')
        for k, n in enumerate(long_):
            cuts = cutsFor(D, n)
            lit, defs, packs = fnData(D, n, cuts)
            ns_ = D['fns'][n]['ns']
            mod = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameD%d' % (p, k)
            files[os.path.join(OUT, p, 'FrameD%d.lean' % k)] = (
                header(mod, 'The frame walk\'s data of `%s`, checked in windows.' % n) +
                'public import LeanVM.Guest.CoreMode.TrieOf\npublic import LeanVM.Guest.CoreMode.FrameSlice\n' +
                imports(p, packs, [(gen_pack[n], ns_)], {gen_pack.get(ns_, p)}) +
                ns(ns_, funDef(D, n, lit, defs)))
            bounds = [0] + cuts + [D['fns'][n]['count']]
            # the windows over slices of the code's chunks (`CoreMode/FrameSlice.lean`): none walks the code before it
            clens = chunk_lens(ns_)
            assert sum(clens) == bounds[-1]
            for m in range(len(bounds) - 1):
                a, b = bounds[m], bounds[m + 1]
                wm = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameD%dW%d' % (p, k, m)
                files[os.path.join(OUT, p, 'FrameD%dW%d.lean' % (k, m))] = (
                    header(wm, 'A window of `%s`\'s frame walk.' % n) +
                    'public import LeanVM.Guest.CoreMode.Pack.«%s».FrameD%d\nimport all Statement.Data.AdviceHints\n\nset_option Elab.async false\n' % (p, k) +
                    ns(ns_, '/-- `%s`: its frame walk accepts offsets %d to %d. -/\ntheorem frameWin%d : CoreMode.frameWinS '
                       'frameFun code.chunks %s %s %d %d = true := by\n  decide +kernel\n' % (
                           n, a, b, m, cut_of(clens, a), cut_of(clens, b), a, b)))
            pairs = list(zip(bounds[:-1], bounds[1:]))
            # the oracle's offsets the windows read, checked once (`CoreMode.oracleChk`), beside the windows
            wo = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameO%d' % (p, k)
            files[os.path.join(OUT, p, 'FrameO%d.lean' % k)] = (
                header(wo, 'The oracle\'s offsets `%s`\'s frame walk reads.' % n) +
                'public import LeanVM.Guest.CoreMode.Pack.«%s».FrameD%d\n\nset_option Elab.async false\n' % (p, k) +
                ns(ns_, '/-- `%s`: its frame walk reads offsets of its oracle. -/\ntheorem frameOracle : '
                   'CoreMode.oracleChk frameFun = true := by\n  decide +kernel\n' % n))
            wl = 'LeanVM.Guest.CoreMode.Pack.«%s».FrameL%d' % (p, k)
            chain = 'trivial'
            for m in reversed(range(len(pairs))):
                chain = '⟨frameWin%d, %s⟩' % (m, chain)
            chain = 'CoreMode.chainFS_wins %s (0, 0) 0\n    %s (CoreMode.restL_zero _)' % (
                lst(bounds[1:], lambda x: '(%s, %d)' % (cut_of(clens, x), x)), chain)
            files[os.path.join(OUT, p, 'FrameL%d.lean' % k)] = (
                header(wl, 'The windows of `%s`\'s frame walk, chained.' % n) +
                'public import LeanVM.Guest.CoreMode.FrameSlice\npublic import %s\n' % wo +
                ''.join('public import LeanVM.Guest.CoreMode.Pack.«%s».FrameD%dW%d\n' % (p, k, m) for m in range(len(pairs))) +
                'import all Statement.Data.AdviceHints\n\nset_option Elab.async false\n' +
                ns(ns_, '/-- `%s`: its hints by pc increase. -/\ntheorem frameHints : Mode.pcsIncr frameFun.hints = true := by\n'
                   '  decide +kernel\n\n/-- `%s`: its code\'s length. -/\ntheorem frameLen : code.chunks.flatten.length = %d := by\n'
                   '  decide +kernel\n\n/-- `%s`: its frame walk accepts its code, its windows chained. -/\n'
                   'theorem frameAcc : CoreMode.FrameAcc frameFun code.chunks.flatten := by\n'
                   '  have hl : frameFun.len = code.chunks.flatten.length := by rw [frameLen]; rfl\n'
                   '  have hc0 : frameFun.cutAt 0 = none := rfl\n'
                   '  refine CoreMode.frameAcc_of_wins frameOracle frameHints hl %s 0 _\n    (by rw [frameLen]; decide) rfl\n'
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
        defs = ''.join(fpowsDef(D['fns'][n]['ns']) for n in sorted(names, key=lambda n: D['fns'][n]['ns']))
        f0 = os.path.join(OUT, p, 'Frame0.lean')
        if POWS in files.get(f0, ''):
            files[f0] = files[f0].replace(POWS, re.sub(r'^(?=noncomputable def |theorem )', 'set_option linter.all false in\n',
                                                       defs, flags=re.M) + '\n')
            continue
        files[os.path.join(FD.ROOT, 'CoreMode', 'GlueP', '%s.lean' % p)] = (
            header('LeanVM.Guest.CoreMode.GlueP.«%s»' % p, 'The powers of `g` the code of each function of the pack names, '
                   'code pointers among them.') +
            'public import LeanVM.Guest.Pow\n\nset_option Elab.async false\nset_option linter.all false\n'
            'set_option linter.style.nameCheck false\n\nnamespace LeanVM.Guest\n\nopen LeanVM.Guest.Exec\n\n'
            '@[expose] public section\n\n' + defs + '\nend\n\nend LeanVM.Guest\n')
    files = {path: wrap(text) for path, text in files.items()}
    # a window, module or pack no longer written (fewer windows, a function moved, a pack gone)
    have = [] if only or fns_only else (glob.glob(os.path.join(OUT, '*', 'Frame*.lean')) +
                                        glob.glob(os.path.join(FD.ROOT, 'CoreMode', 'GlueP', '*.lean')))
    genfiles.sync(files, have)
    lines = sum(text.count('\n') for text in files.values())
    print('files', len(files), 'functions', stats['fns'], 'windows', stats['windows'], 'lines', lines)


if __name__ == '__main__':
    main(sys.argv[1:])
