"""The core route's functions whose heap certificates need residuals (`CoreMode/CoreRes.lean`): `callc.py`'s check
with calls, on the bodies it does not close without residuals (its own candidates, and the straight-line bodies
milestone 1's check leaves uncovered), with the inference's index rules (`idx`, `rules`) on, each certificate's
residuals of a family the honest instances make true (`CoreMode.resFam`, sound in `EndExecCoreRes.lean`).

`extend(out, why, S)` adds them to `callc.results()`'s. Usage (a census): python3 -I scripts/core-mode/callcres.py"""
import os, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
sys.modules.setdefault('infer', I)

CAPE = 2 ** 62
FEATURES = {'ptr', 'pfr', 'idx', 'rules'}


def top_atoms(body):
    """`Res.topAtoms`: the top-level atoms before the first statement that may return."""
    out = []
    for s in body:
        if s[0] == 'a':
            out.append(s[1])
        elif s[0] == 'ret' or has_ret(s):
            break
    return out


def has_ret(s):
    if s[0] == 'ret':
        return True
    if s[0] == 'ite':
        return any(has_ret(t) for t in s[2] + s[3])
    if s[0] == 'match':
        return any(has_ret(t) for a in s[2] for t in a)
    return False


def rc_bound(atoms, v):
    """`Res.rcBound`: the first range check of `v` against a constant `g^(N - 1)` among the atoms, `N`."""
    consts = {}
    for a in atoms:
        if a[0] == 'const' and a[1] not in consts:
            consts[a[1]] = a[2]
    for a in atoms:
        if a[0] == 'rangeCheck' and a[1] == v:
            c = consts.get(a[5])
            if c is None or c[1] != 0 or c[0] not in I.POWS:
                return None
            e = I.POWS[c[0]]
            return e + 1 if e + 1 <= 2 ** 33 else None
    return None


def res_fam(body, r):
    """`CoreMode.resFam`: an exponent bound of a range checked value (`rc`), a residual of a family under branch
    conditions. (Top-level selectors, `sel`, are not emitted by the solver.)"""
    if r[0] == 'under':
        return res_fam(body, r[2])
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num':
        n = r[2][1]
        N = rc_bound(top_atoms(body), r[1][1])
        return n < CAPE and N is not None and N <= n
    return False


def res_ok(k, res):
    body = I.CORE[k][1]
    return all(res_fam(body, r) for r in res)


def straight(body):
    return all(s[0] in ('a', 'ret') for s in body) and sum(1 for s in body if s[0] == 'ret') == 1 and \
        body[-1][0] == 'ret'


def leaf_candidates():
    """Straight-line bodies without calls milestone 1's check leaves uncovered."""
    import heap
    return sorted(k for k in heap.scope_fns() if straight(I.CORE[k][1]) and heap.Fn(k).run().fail is not None)


def extend(out, why, S, verbose=False):
    """`callc`'s results, with the bodies it closes only with residuals of families."""
    import callc
    saved = set(I.F)
    I.F.clear()
    I.F.update(FEATURES)
    got, lost = {}, collections.Counter()
    try:
        cands = [k for k in callc.candidates() if k not in out] + [k for k in leaf_candidates() if k not in out]
        for k in cands:
            try:
                r = callc.infer_one(k, S, allow=res_ok)
            except callc.No as e:
                lost[str(e).split(':')[0]] += 1
                continue
            r['text'] = callc.ldata(k, r)
            got[k] = r
    finally:
        I.F.clear()
        I.F.update(saved)
    for k, r in got.items():
        out[k] = r
    if verbose:
        print('calls with residuals: %d of %d candidates' % (len(got), len(cands)), dict(lost.most_common()))
    return got


if __name__ == '__main__':
    import callc, route
    I.F.clear()
    I.F.update({'ptr', 'pfr'})
    out, why, S = {}, collections.Counter(), route.sigs()
    for k in callc.candidates():
        try:
            out[k] = callc.infer_one(k, S)
        except callc.No:
            pass
    got = extend(out, why, S, True)
    for k in sorted(got):
        print(k, len(got[k]['cert'].res))
