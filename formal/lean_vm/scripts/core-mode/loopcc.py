"""The core route's loop helpers (`formal/notes/core-mode.md`, `CoreMode/CoreLoopC.lean`'s
`LoopOkC`): bodies of atoms and calls, their tail call to themselves and `ret []`, checked by `heapOkC`'s loop rules
with the function's heap signature its mode signature's translated (`CoreMode.sigOkLP`: `loopc.py`'s helpers, its pointer
runs `preP`/`postLP` as `prePR`/`postPR`) and each
callee's its mode signature's (`CoreMode.fitB`, as `callc.py`). The certificate's witnesses come from the emitter's
solver (`emitc.solve`) in `infer.py`'s pass at those signatures, which must not grow.

`results()` returns `{name: dict(cert, cs)}` for the functions whose certificate is complete, and the reasons of the
others. Usage: python3 -I scripts/core-mode/loopcc.py --emit [--check] [--why]"""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.append(os.path.join(HERE, '..'))
import genfiles  # noqa: E402
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)
import route, callc, loopc  # noqa: E402

CORE, STABLE = I.CORE, I.STABLE
No = callc.No


# loop helpers not taken
HELD = set()


def candidates(S=None):
    """Loop helpers: atoms and calls, the tail `callIf` to itself with a word per parameter, `ret []`; or
    (`CoreMode.loopBB`) a body with branches and `match`es, its statements before the tail (nested ones included) atoms, calls, branches, `match`es."""
    out = []
    for k in sorted(I.IS_LOOP):
        params, body = CORE[k]
        if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf':
            continue
        t = body[-2]
        if I.callee(t[2]) != k or len(t[3]) != len(params):
            continue
        kinds = {s[0] for s in body[:-2]}
        nkinds = {s[0] for s in I.stmts(body[:-2])}
        if k in HELD:
            continue
        # (`CoreMode.isBS`: conditional calls of other functions too)
        if kinds & {'ite', 'match'} and nkinds <= {'a', 'call', 'ite', 'match', 'callIf'} and \
                all(I.callee(s[2]) != k for s in I.stmts(body[:-2]) if s[0] == 'callIf'):
            out.append(k)
            continue
        # atoms and calls, a leaf loop helper among them
        if kinds <= {'a', 'call'}:
            out.append(k)
    return out


def infer_one(k, S):
    EM = callc._em()
    params, body = CORE[k]
    np = len(params)
    G = S.get(k)
    if G is None:
        raise No('no mode signature')
    if G['self'] == ('id', 'none'):
        raise No('no self cell')
    if 0 not in G['entry'] or 1 not in G['entry']:
        raise No('header')
    # `CoreMode.LoopOkC.rdFree`: a range check or `touch` reads memory only with no pointer fact on the path
    # (`noPtrL`, checked below); no `frameAddr`
    mem_read = any(s[0] == 'a' and s[1][0] in ('rangeCheck', 'touch') for s in I.stmts(body))
    if any(s[0] == 'a' and s[1][0] == 'frameAddr' for s in I.stmts(body)) or (mem_read and (G['preP'] or G['postLP'])):
        raise No('memory read')
    # `CoreMode.tailPass`: the parameters' cells the tail call passes on unchanged
    ps = [2 + b for b, a in enumerate(body[-2][3]) if a == params[b]]
    G2 = dict(G)
    G2['preP'], G2['postLP'] = [], []
    # the caller's cells and frame as ghost slots (`CoreMode.loopGl`, `sigOkLP`'s `gl`)
    own = loopc.own_sig(G2, np, ps, callc.gl_of(k) or None)
    # `sigOkLP`: the loop's pointer runs, its preconditions' and its loop's, translated, offsets as they are
    for f, src, kps in (('prePR', G['preP'], ps), ('postPR', G['postLP'], loopc.exp_cells(G))):
        for r, offs in src:
            if list(offs) != sorted(set(offs)):
                raise No('offsets')
            getattr(own, f).append((loopc.run(G, np, r, kps), tuple(offs)))
    if any(p[0] not in own.preR for p in own.prePR) or any(p[0] not in own.postR for p in own.postPR):
        raise No('own pointer run cells')
    if I.loop_params(k)[0] != 0:
        raise No('counter not 0')
    cs = {}
    for s in I.stmts(body[:-2]):
        if s[0] == 'callIf':
            # a conditional call of another function (`CoreMode.callsBL`): checked as a call returning nothing
            s = ('call', s[2], s[3], [])
        if s[0] != 'call':
            continue
        f = s[1]
        Gf = S.get(STABLE.get(f, f)) or S.get(f)
        if Gf is None:
            raise No('callee without mode signature')
        if I.callee(f) == k:
            raise No('recursive')
        # `CoreMode.fitBL`: `callc.py`'s `fitB`; no pointer cell guaranteed (`calleePtrOk`)
        h = callc.callee_sig(Gf, len(s[2]), len(s[3]), ext=False)
        # `fitBL` and `callChk`: no returned word's monomial at a loop's call
        h.retM = {}
        if h.postP:
            raise No('callee pointer base')
        callc.exp_bounds(h, s[2], body, np, callc.exp_cells(G))
        # `CoreMode.fitBL`: a callee's pointer run's run (its loop's too) is a run it guarantees written
        for r, _ in Gf['postP'] + Gf['postLP']:
            try:
                q = callc.runX(r, len(s[2]) + len(s[3]))
            except No:
                continue
            if q not in h.postR:
                h.postR.append(q)
        if h.postP or any(p[0] not in h.postR for p in h.postPR):
            raise No('callee pointer run cells')
        if mem_read and h.postPR:
            raise No('memory read')
        if f in cs and cs[f].key() != h.key():
            raise No('callee arity')
        cs[f] = h
    I.SIGS.clear()
    for f, h in cs.items():
        I.SIGS[I.callee(f)] = h
    G0 = own.clone()
    I.SIGS[k] = G0
    P = I.Pass(k, G0).run()
    import callcres
    # (a stream-cursor loop's reads past its cursor: pointer facts the inference wants, the `st` family's residuals
    # instead, `callcres.st_sub`)
    if G0.pre != own.pre or G0.preR != own.preR or (k not in callcres.ST_LOOPS and (G0.prePR != own.prePR or
                                                                                   G0.preP != own.preP)):
        raise No('own precondition grows')
    sigs, hs = {}, {}
    for f, h in cs.items():
        dr = []
        hs[f] = sigs[I.callee(f)] = EM.sig_of(h, len(CORE[I.callee(f)][0]), dr)
        if dr:
            raise No('callee signature dropped')
    dr = []
    sigs[k] = EM.sig_of(own, np, dr)
    if dr:
        raise No('own signature dropped')
    sigOf = lambda g: sigs.get(I.callee(g), EM.C.EMPTY)
    H, Sv, pas = EM.solve(k, P, sigs, sigOf)
    if pas.fails or Sv.miss:
        raise No('unwitnessed: ' + str((list(pas.fails) + [('miss',) + m for m in Sv.miss])[0])[:60])
    if EM.check(k, H, sigOf) is not None:
        raise No('recheck')
    # `CoreMode.hiRes`: a linked upper bound over the parameters, its exponent by a residual
    gl = callc.gl_of(k) or None
    for r in G['preR']:
        q = loopc.run_h(r, np, gl)
        if q is not None and q[3][0]:
            hi = EM.cidx(q[3], np)
            if len(q[3][0]) == 1 and q[3][0][0][0] >= I.GB and q[3][0][0][1] == 1 and q[3][1] == 0:
                # a ghost slot's exponent (`CoreMode.hiG`), by its family's residual over the ghost's value
                x = ('lt', ('num', 0), ('val', q[3][0][0][0]))
                if x not in H.res:
                    H.res.append(x)
                continue
            if any(b >= np for b, _ in q[3][0]) or not any(x[0] == 'lt' and x[2] == hi for x in H.res):
                raise No('linked bound without residual')
    import callcres
    if H.res and not callcres.res_ok(k, H.res, S):
        raise No('residuals')
    return dict(cert=H, cs=hs)


def results(verbose=False):
    """`_results`, computed once while its inputs are unchanged (`memo.py`)."""
    import memo
    return memo.cached('loopcc.results', lambda: _results(verbose))


def _results(verbose=False):
    I.F.clear()
    I.F.update({'ptr', 'pfr'})
    S = route.sigs()
    out, why = {}, collections.Counter()
    cs = candidates(S)
    # the solver's read witnesses also from the residual families (`callcres.cs_reads`: the `st` family's)
    import callcres
    EM = callc._em()
    base, EM.Solver.pt = callcres.cs_reads(EM)
    try:
        for k in cs:
            try:
                try:
                    out[k] = infer_one(k, S)
                except No:
                    # then with reads at any index of a run, their bounds residuals of families (`idx`, `rules`)
                    I.F.update({'idx', 'rules'})
                    try:
                        out[k] = infer_one(k, S)
                    finally:
                        I.F.clear()
                        I.F.update({'ptr', 'pfr'})
                out[k]['text'] = callc.ldata(k, out[k], data=True)
            except No as e:
                why[str(e).split(':')[0]] += 1
                if verbose == 'why':
                    print(k, e)
    finally:
        EM.Solver.pt = base
    if verbose:
        print('loops with calls: %d of %d candidates' % (len(out), len(cs)), dict(why.most_common()))
    return out, why


# ---- the certificates in `heapOkC`'s format: `Gen/<pack>/DataLC.lean`

GEN = callc.GEN
head = genfiles.header('core-mode/loopcc.py --emit')
HEADER = """public import LeanVM.Guest.CoreMode.Defs
public meta import LeanVM.Guest.DataLit

set_option maxRecDepth 100000
set_option linter.all false
"""


GENWL = os.path.join(os.path.dirname(GEN), 'GenWL')


def windows(R, po):
    """The heap checks estimated past `heapwin.BUDGET`, in windows (`heapwin.one`, `HeapCWin` for a loop helper):
    `GenWL/<fn>/`, its `Ok.lean` stating `Fn.«fn».heap_okW` at the callees' signatures `csigs` and its own as
    `CFun.sigOf` reads them, which `core.py`'s `heap_okC` takes, by path."""
    import heapwin
    import heap
    epo = heap.pack_of()
    files = {}
    for k in sorted(R):
        H = R[k]['cert']
        sigs = {I.callee(f): h for f, h in R[k]['cs'].items()}
        sigs[I.callee(k)] = H.sig
        sigOf = lambda g, sigs=sigs: sigs.get(I.callee(g), heapwin.C.EMPTY)
        if heapwin.fn_cost(k, H, sigOf) <= heapwin.BUDGET:
            continue
        gen = dict(root='LeanVM.Guest.CoreMode.GenWL', sub='HeapWL', final='heap_okW',
                   data=['LeanVM.Guest.CoreMode.Gen.«%s».DataLC' % po[k][0]],
                   names=sorted(R[k]['cs']))
        for name, text in heapwin.one(k, H, sigOf, epo, gen):
            files[os.path.join(GENWL, k, name + '.lean')] = text
    return files


def emit(R, check):
    import heap, glob
    po = heap.pack_of()
    packs = collections.defaultdict(list)
    for k in sorted(R):
        packs[po[k][0]].append(k)
    files = {}
    for pack, ks in sorted(packs.items()):
        out = [head(f'LeanVM.Guest.CoreMode.Gen.«{pack}».DataLC', f'The heap certificates of `{ks[0]}` and '
                    f"{len(ks) - 1} more (loop helpers with calls), their callees' heap signatures.") + HEADER]
        for k in ks:
            out.append(f'\nnamespace LeanVM.Guest.Fn.«{k}»\n@[expose] public section\n{R[k]["text"]}'
                       f'\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        text = ''.join(out)
        if 'CoreMode.evR ' in text or 'CoreMode.runR ' in text:
            # runs of witnesses (`emitc.lwits`)
            text = text.replace('public import LeanVM.Guest.CoreMode.Defs\n',
                                'public import LeanVM.Guest.CoreMode.Defs\npublic import LeanVM.Guest.CoreMode.WitOf\n', 1)
        files[os.path.join(GEN, pack, 'DataLC.lean')] = text
    files.update(windows(R, po))
    have = glob.glob(os.path.join(GEN, '*', 'DataLC.lean')) + glob.glob(os.path.join(GENWL, '*', '*.lean'))
    stale = genfiles.sync(files, have, check)
    print('loopcc: %d functions, %d files, %d lines' % (len(R), len(files), sum(t.count('\n') for t in files.values())) +
          ((', stale: %d' % len(stale)) if check else ''))
    genfiles.fail_if_stale(stale, check)


if __name__ == '__main__' and '--emit' in sys.argv:
    R, _ = results('why' if '--why' in sys.argv else True)
    emit(R, '--check' in sys.argv)
