"""The core route's functions on heap contracts (`CoreMode.heapCtr`, `CFun.hc`): leaves the check without calls leaves
uncovered (atoms, branches and `match`es, one final `ret`), checked by `heapOkC` at their own heap signature, inferred
freely (preconditions only, no translation of their mode signature), every caller a body with calls (`callc.py`)
re-inferred with that signature as its callee's (`CFun.hcs`). A leaf joins only when every caller then passes.

`extend(out, why, S)` adds them to `callc.results()`'s and replaces their callers'."""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)


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
    """The check without calls passes on `k` and its mode signature names each of its preconditions (`route.py`)."""
    import heap, route
    f = heap.Fn(k).run()
    if f.fail is not None:
        return False
    G, np = S.get(k), len(I.CORE[k][0])
    return G is not None and all(any(route.mono_cell(G, np, m) == c for m in G['pre']) or c in route.run_points(G, np)
                                 for c in f.pre)


def candidates(out, S):
    """Leaves of atoms, branches and `match`es with one final `ret`, not loop helpers nor `main`, not already in `out`,
    the route without calls not taking them for their preconditions."""
    import callc
    res = []
    for k, (params, body) in sorted(I.CORE.items()):
        if k in out or k in I.IS_LOOP or k == 'main':
            continue
        acc = callc.kinds(body, collections.Counter())
        if not set(acc) <= {'a', 'ret', 'ite', 'match'} or acc['ret'] != 1 or body[-1][0] != 'ret':
            continue
        if not (acc['ite'] or acc['match']):
            continue
        if m1_pre(k, S):
            continue
        res.append(k)
    return res


def eq_candidates(out, S):
    """Leaves of atoms and one final `ret`, not loop helpers nor `main`, not in `out`, whose mode signature has orders at
    return (`postT`, `postC`), which no mode contract on the core route states: on a heap contract with their equations
    at return (`retEq`) instead, joined with their callers."""
    import callc
    res = []
    for k, (params, body) in sorted(I.CORE.items()):
        if k in out or k in I.IS_LOOP or k == 'main' or k not in S:
            continue
        acc = callc.kinds(body, collections.Counter())
        if set(acc) <= {'a', 'ret'} and acc['ret'] == 1 and body[-1][0] == 'ret' and (S[k]['postT'] or S[k]['postC']):
            res.append(k)
    return res


def infer_hc(k, eqs=False):
    """`k`'s certificate at its own heap signature, inferred from no precondition; with `eqs`, its guarantees and
    equations at return (`I.infer` with `div`)."""
    import callc
    EM = callc._em()
    params, body = I.CORE[k]
    np = len(params)
    I.SIGS.clear()
    if eqs:
        saved = set(I.F)
        try:
            I.F.add('div')
            I.infer(k)
        finally:
            I.F.clear()
            I.F.update(saved)
        G0 = I.SIGS[k]
        if G0.pre or G0.post or G0.postR or G0.retM or G0.postV or not G0.retEq:
            raise callc.No('own guarantees')
        I.SIGS.clear()
        I.SIGS[k] = G0
    else:
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


def arity(body, f):
    """The argument and returned word counts of `body`'s first call of `f`."""
    for st in body:
        if st[0] == 'call' and st[1] == f:
            return len(st[2]), len(st[3])
        if st[0] == 'callIf' and st[2] == f:
            return len(st[3]), 0
        if st[0] == 'dispatch' and f in st[2]:
            return len(st[3]), len(st[4])
        for sub in (st[2:4] if st[0] == 'ite' else st[2] if st[0] == 'match' else []):
            r = arity(sub, f)
            if r:
                return r
    return None


def call_candidates(out):
    """`callc.py`'s candidates (straight-line bodies with calls) not already in `out`."""
    import callc
    return [k for k in callc.candidates() if k not in out]


def infer_hc_calls(k, S, hcsig):
    """`k`, a body with calls, at its own heap signature: the inference's (`I.infer`, its guarantees, returned words
    and equations, conditional loops' runs pushed), its callees at their heap contracts (`hcsig`) or their mode
    signatures translated; then each precondition the emitter's solver does not need dropped."""
    import callc
    EM = callc._em()
    params, body = I.CORE[k]
    np = len(params)
    cs, hcs = {}, set()
    for f in sorted(callees_of(body, set())):
        na, nr = arity(body, f)
        if I.callee(f) in hcsig:
            cs[f] = hcsig[I.callee(f)].clone()
            hcs.add((f, na, nr))
        else:
            Gf = S.get(I.STABLE.get(f, f)) or S.get(f)
            if Gf is None:
                raise callc.No('callee without mode signature')
            cs[f] = callc.callee_sig(Gf, na, nr)
    # a callee run's bound an argument a constant power of `g` (`CFun.xc` is empty for a heap contract)
    for st in body:
        calls = ([(st[1], st[2])] if st[0] == 'call' else [(st[2], st[3])] if st[0] == 'callIf' else
                 [(f, st[3]) for f in st[2]] if st[0] == 'dispatch' else [])
        for f, args in calls:
            if f == k:
                raise callc.No('recursive')
            callc.exp_bounds(cs[f], args, body, np, set())
    saved = set(I.F)
    try:
        I.F.add('callIfR')
        I.SIGS.clear()
        for f, h in cs.items():
            I.SIGS[I.callee(f)] = h
        I.infer(k)
        G0 = I.SIGS[k]
    finally:
        I.F.clear()
        I.F.update(saved)
    if G0.ghosts or G0.term or G0.preP or G0.prePR:
        raise callc.No('own ghosts or pointer preconditions')
    sigs = {}
    for f, h in cs.items():
        dr = []
        sigs[I.callee(f)] = EM.sig_of(h, len(I.CORE[I.callee(f)][0]), dr)
        if dr:
            raise callc.No('callee signature dropped')

    def solve(G):
        I.SIGS.clear()
        for f, h in cs.items():
            I.SIGS[I.callee(f)] = h
        I.SIGS[k] = G.clone()
        P = I.Pass(k, I.SIGS[k]).run()
        dr = []
        sg = dict(sigs)
        sg[k] = EM.sig_of(G, np, dr)
        if dr:
            return None
        sigOf = lambda g: sg.get(I.callee(g), EM.C.EMPTY)
        H, Sv, pas = EM.solve(k, P, sg, sigOf)
        if pas.fails or Sv.miss or EM.check(k, H, sigOf) is not None or H.res:
            return None
        return H
    H = solve(G0)
    if H is None:
        raise callc.No('unwitnessed')
    for fld in ('pre', 'preR'):
        i = 0
        while i < len(getattr(G0, fld)):
            G1 = G0.clone()
            del getattr(G1, fld)[i]
            H1 = solve(G1)
            if H1 is not None:
                G0, H = G1, H1
            else:
                i += 1
    return dict(cert=H, cs={f: sigs[I.callee(f)] for f in cs}, dsp=callc.dsp_of(k, body), hc=True,
                hcs=sorted(hcs)), G0


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
        err = None
        for feats in (callcres.FEATURES,) + callcres.VT_FEATS.get(c, ()):
            I.F.clear()
            I.F.update(feats)
            try:
                return callc.infer_one(c, S, allow=lambda k, res: callcres.res_ok(k, res, S), hcsig=hcsig)
            except callc.No as e:
                err = err or e
        raise err
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
    leaves = candidates(out, S)
    eqs = eq_candidates(out, S)
    cands = [(k, False) for k in leaves] + [(k, True) for k in call_candidates(out)] + [(k, 'eq') for k in eqs]
    for k, calls in cands:
        cs = callers.get(k, set())
        if not cs or not all((c in out or calls == 'eq') and c not in I.IS_LOOP for c in cs):
            lost['callers'] += 1
            continue
        try:
            r, G0 = infer_hc_calls(k, S, hcsig) if calls is True else infer_hc(k, calls == 'eq')
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
            try:
                r['text'] = callc.ldata(k, r)
            except callc.No:
                # a callee's copy with auxiliary declarations: named only by the emission's shared copies
                r['text'] = None
    if verbose:
        print('heap contracts: %d of %d candidates' % (len(got), len(cands)), dict(lost.most_common()))
    return got
