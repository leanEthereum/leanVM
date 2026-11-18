"""The core route's loop helpers whose bodies have calls (`formal/notes/core-mode.md`, `CoreMode/CoreLoopC.lean`'s
`LoopOkC`): bodies of atoms and calls, their tail call to themselves and `ret []`, checked by `heapOkC`'s loop rules
with the function's heap signature its mode signature's translated (`CoreMode.sigOkLP`: `loopc.py`'s, its pointer
runs `preP`/`postLP` as `prePR`/`postPR`) and each
callee's its mode signature's (`CoreMode.fitB`, as `callc.py`). The certificate's witnesses come from the emitter's
solver (`emitc.solve`) in `infer.py`'s pass at those signatures, which must not grow.

`results()` returns `{name: dict(cert, cs)}` for the functions whose certificate is complete, and the reasons of the
others. Usage (a census): python3 -I scripts/core-mode/loopcc.py [--fn NAME] [--why] [--emit [--check]]"""
import os, sys, collections
ARGV = list(sys.argv)
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)
import route, callc, loopc  # noqa: E402

CORE, STABLE = I.CORE, I.STABLE
No = callc.No


def candidates():
    """Loop helpers: atoms and calls (at least one), the tail `callIf` to itself with a word per parameter, `ret []`."""
    out = []
    for k in sorted(I.IS_LOOP):
        params, body = CORE[k]
        if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf':
            continue
        t = body[-2]
        if I.callee(t[2]) != k or len(t[3]) != len(params):
            continue
        kinds = {s[0] for s in body[:-2]}
        if 'call' in kinds and kinds <= {'a', 'call'}:
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
    if any(s[0] == 'a' and s[1][0] in ('rangeCheck', 'touch', 'frameAddr') for s in body):
        raise No('memory read')
    G2 = dict(G)
    G2['preP'], G2['postLP'] = [], []
    own = loopc.own_sig(G2, np)
    # `sigOkLP`: the loop's pointer runs, its preconditions' and its loop's, translated, offsets as they are
    for f, src in (('prePR', G['preP']), ('postPR', G['postLP'])):
        for r, offs in src:
            if list(offs) != sorted(set(offs)):
                raise No('offsets')
            getattr(own, f).append((loopc.run(G, np, r), tuple(offs)))
    if any(p[0] not in own.preR for p in own.prePR) or any(p[0] not in own.postR for p in own.postPR):
        raise No('own pointer run cells')
    if I.loop_params(k)[0] != 0:
        raise No('counter not 0')
    cs = {}
    for s in body[:-2]:
        if s[0] != 'call':
            continue
        f = s[1]
        Gf = S.get(STABLE.get(f, f)) or S.get(f)
        if Gf is None:
            raise No('callee without mode signature')
        if I.callee(f) == k:
            raise No('recursive')
        # `CoreMode.fitBL`: no self cell, loop runs or pointer-based products
        if Gf['self'] != ('id', 'none') or Gf['postL'] or Gf['postLP']:
            raise No('callee self')
        h = callc.callee_sig(Gf, len(s[2]), len(s[3]))
        if h.preP or h.postP:
            raise No('callee pointer base')
        callc.exp_bounds(h, s[2], body)
        # `CoreMode.fitBL`: a callee's pointer run's run is a run it guarantees written
        for r, _ in Gf['postP']:
            try:
                q = callc.runX(r, len(s[2]) + len(s[3]))
            except No:
                continue
            if q not in h.postR:
                h.postR.append(q)
        if h.postP or any(p[0] not in h.postR for p in h.postPR):
            raise No('callee pointer run cells')
        if f in cs and cs[f].key() != h.key():
            raise No('callee arity')
        cs[f] = h
    I.SIGS.clear()
    for f, h in cs.items():
        I.SIGS[I.callee(f)] = h
    G0 = own.clone()
    I.SIGS[k] = G0
    P = I.Pass(k, G0).run()
    if G0.pre != own.pre or G0.preR != own.preR or G0.prePR != own.prePR or G0.preP != own.preP:
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
    if H.res:
        raise No('residuals')
    return dict(cert=H, cs=hs)


def results(verbose=False):
    I.F.clear()
    I.F.update({'ptr', 'pfr'})
    S = route.sigs()
    out, why = {}, collections.Counter()
    cs = candidates()
    for k in cs:
        try:
            out[k] = infer_one(k, S)
            out[k]['text'] = callc.ldata(k, out[k])
        except No as e:
            why[str(e).split(':')[0]] += 1
            if verbose and '--why' in ARGV:
                print(k, e)
    if verbose:
        print('loops with calls: %d of %d candidates' % (len(out), len(cs)), dict(why.most_common()))
    return out, why


# ---- the certificates in `heapOkC`'s format: `Gen/<pack>/DataLC.lean`

GEN = callc.GEN
HEADER = """/-
  LeanVM.Guest.CoreMode.Gen.«{pack}».DataLC

  Generated by `scripts/core-mode/loopcc.py --emit`; do not edit.
  The heap certificates of `{first}` and {more} more (loop helpers with calls), their callees' heap signatures.
-/

module

public import LeanVM.Guest.CoreMode.Defs

set_option maxRecDepth 100000
set_option linter.all false
"""


def emit(R, check):
    import heap, glob
    po = heap.pack_of()
    packs = collections.defaultdict(list)
    for k in sorted(R):
        packs[po[k][0]].append(k)
    files = {}
    for pack, ks in sorted(packs.items()):
        out = [HEADER.format(pack=pack, first=ks[0], more=len(ks) - 1)]
        for k in ks:
            out.append(f'\nnamespace LeanVM.Guest.Fn.«{k}»\n\n@[expose] public section\n\n{R[k]["text"]}'
                       f'\nend\nend LeanVM.Guest.Fn.«{k}»\n')
        files[os.path.join(GEN, pack, 'DataLC.lean')] = ''.join(out)
    stale = []
    for path in sorted(set(glob.glob(os.path.join(GEN, '*', 'DataLC.lean'))) - set(files)):
        stale.append(path)
        if not check:
            os.remove(path)
    for path, text in sorted(files.items()):
        old = open(path, encoding='utf-8').read() if os.path.exists(path) else None
        if old != text:
            stale.append(path)
            if not check:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                open(path, 'w', encoding='utf-8').write(text)
    print('loopcc: %d functions, %d files, %d lines' % (len(R), len(files), sum(t.count('\n') for t in files.values())) +
          ((', stale: %d' % len(stale)) if check else ''))
    if check and stale:
        sys.exit(1)


if __name__ == '__main__':
    if '--emit' in ARGV:
        R, _ = results(True)
        emit(R, '--check' in ARGV)
    elif '--fn' in ARGV:
        k = ARGV[ARGV.index('--fn') + 1]
        I.F.clear()
        I.F.update({'ptr', 'pfr'})
        try:
            r = infer_one(k, route.sigs())
            print('ok', k, callc.ldata(k, r))
        except No as e:
            print('no', k, e)
    else:
        results(True)
