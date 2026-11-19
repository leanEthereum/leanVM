"""The core route's leaf loop helpers (`formal/notes/core-mode.md`, `CoreMode/CoreLoop.lean`'s `LoopOk`): bodies of
atoms, their tail call to themselves and `ret []`, checked by `heapOkC`'s loop rules with the function's heap
signature its mode signature's translated (`CoreMode.sigOkL`: bounds over the parameters' exponents, the loop's runs
`postL` among `postR`). The certificate's witnesses come from `infer.py`'s pass (`heapOkC`'s format, no extra feature)
run once at that signature, which must not grow.

`results()` returns `{name: dict(pass_, sig)}` for the functions whose certificate is complete, and the reasons of the
others. Usage (a census): python3 -I scripts/core-mode/loopc.py [--fn NAME] [--emit [--check]]"""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)
import route, callc  # noqa: E402

CORE, STABLE = I.CORE, I.STABLE
No = callc.No


def candidates():
    """Leaf loop helpers: atoms, the tail `callIf` to itself with a word per parameter, `ret []`."""
    out = []
    for k in sorted(I.IS_LOOP):
        params, body = CORE[k]
        if len(body) < 2 or body[-1] != ('ret', []) or body[-2][0] != 'callIf':
            continue
        t = body[-2]
        if I.callee(t[2]) != k or len(t[3]) != len(params):
            continue
        import callcres
        if all(s[0] == 'a' for s in body[:-2]) and k not in callcres.LEAF_FAM:
            out.append(k)
    return out


def par_cell(G, np, o):
    return 2 <= o and o - 2 < np and o < 2 ** 28 and o in G['entry']


def idx(G, np, i):
    """`CoreMode.idxT`: a constant below `2^62`, or a parameter's exponent."""
    if i[0] == 'num':
        if i[1] >= 2 ** 62:
            raise No('bound')
        return I.num(i[1])
    if i[0] == 'ex' and i[1][0] == 'fr' and i[2] == 0 and par_cell(G, np, i[1][1]):
        return I.base(i[1][1] - 2)
    raise No('bound')


def idx_k(G, i):
    """`CoreMode.idxK`: a constant or one of the termination fact's exponents."""
    return i[0] == 'num' or any(p[0] == i or p[1] == i for p in G['term'])


def mono(G, np, m):
    """`CoreMode.monoT`: a product over the parameters' entry cells."""
    return callc.cell(m, np, lambda o: o in G['entry'])


def exp_cells(G):
    """`CoreMode.expCells`: the frame cells the entry runs (`preR`, `preP`) bound by exponent."""
    return [b[1][1] for r in list(G['preR']) + [p[0] for p in G['preP']] for b in (r[1], r[2])
            if b[0] == 'ex' and b[1][0] == 'fr']


def idx_kx(G, ps, i):
    """`CoreMode.idxKX`: `idx_k`, or an entry run's bound cell's exponent among `ps`."""
    if idx_k(G, i):
        return True
    return (i[0] == 'ex' and i[1][0] == 'fr' and i[2] == 0 and i[1][1] in exp_cells(G) and i[1][1] in ps and
            i[1][1] in G['entry'] and i[1][1] < 2 ** 28)


def run_h(r, np, gl):
    """`CoreMode.rngH`: a run over one linked caller's cell `[d]` (`.hp 1 d`, `d != 0`, linked to a slot with no power
    of `g`), of a constant lower bound and an upper bound `hiH` (a constant, or the exponent of a linked caller's cell
    `d' != 0`, `idxL`), below `2^62`, as the heap run over that slot; else `None`."""
    q, lo, hi, S, d = r
    fp, k, bs = q
    if not gl or fp != 0 or len(bs) != 1 or bs[0][1] != 1 or bs[0][0][0] != 'hp' or bs[0][0][1] != 1:
        return None
    dd = bs[0][0][2]
    if dd == 0 or dd not in gl or gl[dd][1] != 0 or lo[0] != 'num' or not lo[1] < 2 ** 62:
        return None
    if hi[0] == 'num':
        if not hi[1] < 2 ** 62:
            return None
        h = I.num(hi[1])
    elif hi[0] == 'ex' and hi[1][0] == 'hp' and hi[1][1] == 1 and hi[2] == 0 and hi[1][2] != 0 and hi[1][2] in gl:
        sl, kk = gl[hi[1][2]]
        h = I.mk(((callc.gslot(sl, np), 1),), kk)
    else:
        return None
    return (I.mk(((callc.gslot(gl[dd][0], np), 1),), k + d), S, I.num(lo[1]), h)


def run(G, np, r, ps=None, gl=None):
    """`CoreMode.rngT`, its bounds `rngK` (`rngKX` with the cells `ps`, if given), constant bounds `rngC`'s normal form;
    with links `gl`, `rngTG`: a run over a linked caller's cell first (`run_h`)."""
    h = run_h(r, np, gl)
    if h is not None:
        return h
    q, lo, hi, S, d = r
    ok = (lambda i: idx_k(G, i)) if ps is None else (lambda i: idx_kx(G, ps, i))
    if not (ok(lo) and ok(hi)):
        raise No('run bound')
    R = (I.shift(mono(G, np, q), d), S, idx(G, np, lo), idx(G, np, hi))
    if R[2][0] or R[3][0]:
        return R
    # constant bounds (`CoreMode.rngT`'s `rngC`): a wrapped offset starts at the run's first cell
    if not R[3][1] - R[2][1] < 2 ** 62:
        raise No('run bound')
    return callc.norm_run(R, R[0][1])


def addr_runs(np, gl):
    """`CoreMode.addrRs`: for each linked caller's cell `d` (but the frame's address `0`), the one cell at the caller's
    frame address (its slot `glFs`) times `g^d`."""
    return [(I.mk(((callc.gslot(gl[0][0], np), 1),), d), 1, I.num(0), I.num(1)) for d in gl if d != 0]


def own_sig(G, np, ps=None, gl=None):
    """`sigOkL`: the loop's heap signature, its mode signature's translated field by field (`sigOkLP`'s bounds
    with the cells `ps` the tail call passes on, if given)."""
    for f in ('ret', 'postP', 'postLP', 'preP', 'retV', 'postT', 'postC'):
        if G[f]:
            raise No('own ' + f)
    if len(G['term']) != 1:
        raise No('term')
    lo, hi = G['term'][0]
    if lo != ('ex', ('fr', 2), 0) or not par_cell(G, np, 2):
        raise No('counter')
    ei = idx(G, np, hi)
    h = I.Sig(np)
    h.term = [(I.base(0), ei)]
    h.ctr, h.bnd = 0, (('num', ei[1]) if not ei[0] else 1)
    h.pre = [mono(G, np, m) for m in G['pre']]
    post_ps = None if ps is None else exp_cells(G)
    h.preR = [run(G, np, r, ps, gl) for r in G['preR']] + (addr_runs(np, gl) if gl else [])
    if gl:
        # the caller's cells linked to ghosts (`CoreMode.loopGl`) or to parameters the tail call passes on (`sigOkLP`),
        # the caller's frame address the last ghost; each cell a run's base or upper bound (`dsIn`)
        h.ghosts = [('link', d) for d, (b, _) in gl.items() if d != 0 and b >= np] + [('fp',)]
        if gl[0][0] != np + len(h.ghosts) - 1:
            raise No('frame slot')
        if any(not any(r[0][2] == [(('hp', 1, d), 1)] or r[2] == ('ex', ('hp', 1, d), 0) for r in G['preR'])
               for d in gl if d != 0):
            raise No('link not a base')
        if any(b < np and (ps is None or 2 + b not in ps) for d, (b, _) in gl.items()):
            raise No('link not passed on')
    h.post = [mono(G, np, m) for m in G['post']]
    h.postR = [run(G, np, r, post_ps) for r in G['postR'] + G['postL']]
    if len(set(h.pre)) != len(h.pre) or len(set(h.preR)) != len(h.preR):
        raise No('duplicate precondition')
    return h


def infer_one(k, S):
    params, body = CORE[k]
    np = len(params)
    G = S.get(k)
    if G is None:
        raise No('no mode signature')
    if G['self'] == ('id', 'none'):
        raise No('no self cell')
    if 0 not in G['entry'] or 1 not in G['entry']:
        raise No('header')
    own = own_sig(G, np)
    if I.loop_params(k)[0] != 0:
        raise No('counter not 0')
    I.SIGS.clear()
    G0 = own.clone()
    I.SIGS[k] = G0
    P = I.Pass(k, G0).run()
    if G0.pre != own.pre or G0.preR != own.preR:
        raise No('own precondition grows')
    if P.unc:
        raise No('uncovered: ' + ','.join(sorted({u[0] for u in P.unc})))
    if I.misses(P):
        raise No('unwitnessed')
    if P.res:
        raise No('residuals')
    return dict(pass_=P, sig=own)


def results(verbose=False):
    I.F.clear()
    S = route.sigs()
    out, why = {}, collections.Counter()
    cs = candidates()
    for k in cs:
        try:
            out[k] = infer_one(k, S)
        except No as e:
            why[str(e).split(':')[0]] += 1
            if verbose and '-v' in sys.argv:
                print(k, e)
    if verbose:
        print('loops: %d of %d candidates' % (len(out), len(cs)), dict(why.most_common()))
    return out, why


# ---- the certificates in `heapOkC`'s format: `Gen/<pack>/DataL.lean`

GEN = callc.GEN
HEADER = """/-
  LeanVM.Guest.CoreMode.Gen.«{pack}».DataL

  Generated by `scripts/core-mode/loopc.py --emit`; do not edit.
  The heap certificates of `{first}` and {more} more (leaf loop helpers).
-/

module

public import LeanVM.Guest.CoreMode.Defs

set_option maxRecDepth 100000
set_option linter.all false
"""


def lsig(G, ind='    '):
    import inferprint as E
    f = []
    if G.pre:
        f.append(f'pre := [{E.wrap(map(E.lcell, G.pre), ind + "  ")}]')
    if G.post:
        f.append(f'post := [{E.wrap(map(E.lcell, G.post), ind + "  ")}]')
    if G.preR:
        f.append(f'preR := [{E.wrap(map(E.lrun, G.preR), ind + "  ")}]')
    if G.postR:
        f.append(f'postR := [{E.wrap(map(E.lrun, G.postR), ind + "  ")}]')
    f.append(f'term := [({E.lidx(G.term[0][0])}, {E.lidx(G.term[0][1])})]')
    return '{ ' + (',\n' + ind + '  ').join(f) + ' }'


def lcert(r):
    import inferprint as E
    P = r['pass_']
    P.wren = {}
    by_d = collections.defaultdict(list)
    for (d, p, off), w in sorted(P.reads.items()):
        by_d[d].append(f'({p}, {off}, {E.lwit(P, w)})')
    reads = E.wrap(f'({d}, [{", ".join(rs)}])' for d, rs in sorted(by_d.items()))
    calls = E.wrap('[' + ', '.join(E.lwit(P, w) for _, w in ws) + ']' for f, ws in P.calls)
    rets = E.wrap('[' + ', '.join(E.lwit(P, w) for _, w in ws) + ']' for ws in P.ret_wits)
    return (f'  sig :=\n    {lsig(r["sig"])}\n  reads := [{reads}]\n  res := []\n  calls := [{calls}]\n'
            f'  rets := [{rets}]\n')


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
            out.append(f'\nnamespace LeanVM.Guest.Fn.«{k}»\n@[expose] public section\n'
                       f'def hcert : CoreMode.HCert where\n{lcert(R[k])}\n'
                       f'end\nend LeanVM.Guest.Fn.«{k}»\n')
        files[os.path.join(GEN, pack, 'DataL.lean')] = ''.join(out)
    stale = []
    for path in sorted(set(glob.glob(os.path.join(GEN, '*', 'DataL.lean'))) - set(files)):
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
    print('loopc: %d functions, %d files, %d lines' % (len(R), len(files), sum(t.count('\n') for t in files.values())) +
          ((', stale: %d' % len(stale)) if check else ''))
    if check and stale:
        sys.exit(1)


if __name__ == '__main__':
    if '--emit' in sys.argv:
        R, _ = results(True)
        emit(R, '--check' in sys.argv)
    elif '--fn' in sys.argv:
        k = sys.argv[sys.argv.index('--fn') + 1]
        I.F.clear()
        try:
            r = infer_one(k, route.sigs())
            P = r['pass_']
            print('ok', k, 'reads', len(P.reads), 'calls', P.calls, 'rets', P.ret_wits)
        except No as e:
            print('no', k, e)
    else:
        results(True)
