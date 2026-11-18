"""The core route's functions on heap contracts (`CoreMode.heapCtr`, `CFun.hc`): leaves milestone 1's check leaves
uncovered (atoms, branches and `match`es, one final `ret`), checked by `heapOkC` at their own heap signature, inferred
freely (preconditions only, no translation of their mode signature), every caller a body with calls (`callc.py`)
re-inferred with that signature as its callee's (`CFun.hcs`). A leaf joins only when every caller then passes.

`extend(out, why, S)` adds them to `callc.results()`'s and replaces their callers'. Usage (a census):
python3 -I scripts/core-mode/callc.py"""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)


def kinds(body, acc):
    for s in body:
        acc[s[0]] += 1
        if s[0] == 'ite':
            kinds(s[2], acc); kinds(s[3], acc)
        if s[0] == 'match':
            for a in s[2]:
                kinds(a, acc)
    return acc


def callees_of(body, acc):
    for s in body:
        if s[0] == 'call':
            acc.add(s[1])
        elif s[0] == 'callIf':
            acc.add(s[2])
        elif s[0] == 'dispatch':
            acc.update(s[2])
        elif s[0] == 'ite':
            callees_of(s[2], acc); callees_of(s[3], acc)
        elif s[0] == 'match':
            for a in s[2]:
                callees_of(a, acc)
    return acc


def m1_pre(k, S):
    """Milestone 1's check passes on `k` and its mode signature names each of its preconditions (`route.py`)."""
    import heap, route
    f = heap.Fn(k).run()
    if f.fail is not None:
        return False
    G, np = S.get(k), len(I.CORE[k][0])
    return G is not None and all(any(route.mono_cell(G, np, m) == c for m in G['pre']) or c in route.run_points(G, np)
                                 for c in f.pre)


def candidates(out, S):
    """Leaves of atoms, branches and `match`es with one final `ret`, not loop helpers nor `main`, not already in `out`,
    milestone 1's route not taking them for their preconditions."""
    res = []
    for k, (params, body) in sorted(I.CORE.items()):
        if k in out or k in I.IS_LOOP or k == 'main':
            continue
        acc = kinds(body, collections.Counter())
        if not set(acc) <= {'a', 'ret', 'ite', 'match'} or acc['ret'] != 1 or body[-1][0] != 'ret':
            continue
        if not (acc['ite'] or acc['match']):
            continue
        if m1_pre(k, S):
            continue
        res.append(k)
    return res


def infer_hc(k):
    """`k`'s certificate at its own heap signature, inferred from no precondition."""
    import callc
    EM = callc._em()
    params, body = I.CORE[k]
    np = len(params)
    I.SIGS.clear()
    G0 = I.Sig(np)
    I.SIGS[k] = G0
    P = I.Pass(k, G0).run()
    if G0.ghosts or G0.preR or G0.prePR or G0.preP or G0.term:
        raise callc.No('own runs')
    dr = []
    sigs = {k: EM.sig_of(G0, np, dr)}
    if dr:
        raise callc.No('own signature dropped')
    sigOf = lambda g: sigs.get(I.callee(g), EM.C.EMPTY)
    H, Sv, pas = EM.solve(k, P, sigs, sigOf)
    if pas.fails or Sv.miss:
        raise callc.No('unwitnessed')
    if EM.check(k, H, sigOf) is not None:
        raise callc.No('recheck')
    if H.res:
        raise callc.No('residuals')
    return dict(cert=H, cs={}, dsp=None, hc=True, hcs=[]), G0


def reinfer(c, S, hcsig):
    """Caller `c` again, its heap-contract callees at their signatures: as `callc`, else as `callcres`."""
    import callc, callcres
    try:
        return callc.infer_one(c, S, hcsig=hcsig)
    except callc.No:
        pass
    saved = set(I.F)
    EM = callc._em()
    base, EM.Solver.pt = callcres.cs_reads(EM)
    try:
        I.F.clear()
        I.F.update(callcres.FEATURES)
        return callc.infer_one(c, S, allow=lambda k, res: callcres.res_ok(k, res, S), hcsig=hcsig)
    finally:
        I.F.clear()
        I.F.update(saved)
        EM.Solver.pt = base


def extend(out, why, S, verbose=False):
    import callc
    callers = collections.defaultdict(set)
    for k, (params, body) in I.CORE.items():
        for f in callees_of(body, set()):
            callers[I.callee(f)].add(k)
    hcsig, got = {}, {}
    lost = collections.Counter()
    cands = candidates(out, S)
    for k in cands:
        cs = callers.get(k, set())
        if not cs or not all(c in out and c not in I.IS_LOOP for c in cs):
            lost['callers'] += 1
            continue
        try:
            r, G0 = infer_hc(k)
        except callc.No as e:
            lost[str(e)] += 1
            continue
        trial = dict(hcsig)
        trial[k] = G0
        new = {}
        try:
            for c in sorted(cs):
                new[c] = reinfer(c, S, trial)
        except callc.No as e:
            lost['caller ' + str(e).split(':')[0]] += 1
            continue
        hcsig = trial
        got[k] = r
        for c, rc in new.items():
            out[c] = rc
    for k, r in got.items():
        out[k] = r
    # every caller's text at the final signatures
    for k, r in out.items():
        if k in got or r.get('hcs') or 'text' not in r:
            r['text'] = callc.ldata(k, r)
    if verbose:
        print('heap contracts: %d of %d candidates' % (len(got), len(cands)), dict(lost.most_common()))
    return got
