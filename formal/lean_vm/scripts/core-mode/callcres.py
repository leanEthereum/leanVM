"""The core route's functions whose heap certificates need residuals (`CoreMode/CoreRes.lean`): `callc.py`'s check
with calls, on the bodies it does not close without residuals (its own candidates, and the straight-line bodies
milestone 1's check leaves uncovered), with the inference's index rules (`idx`, `rules`) on, each certificate's
residuals of a family the honest instances make true (`CoreMode.resFam`, sound in `EndExecCoreRes.lean`).

`extend(out, why, S)` adds them to `callc.results()`'s. Usage (a census): python3 -I scripts/core-mode/callcres.py"""
import os, re, sys, collections
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


def cs_kappa(k):
    """`κ` for `column_selector__L{κ}`, `κ < 31` (`B1.Tables.lName`)."""
    m = re.fullmatch(r'column_selector__L(\d+)', k)
    return int(m.group(1)) if m and int(m.group(1)) < 31 else None


def cs_sub(kap):
    """`CoreMode.csSub κ`: the lowest digit's read `[sel_eq]·[digit₀]·g^off` in its strided table."""
    w = 4 * (kap // 4) + 4 - kap
    off = 64 * (kap // 4) + 16 * (w - 1)
    return ('sub', (((1, 1), (3, 1)), off), ((((1, 1),), off), 2 ** (4 - w), ('num', 0), ('num', 2 ** w)))


def exp_diff(atoms, x):
    """`CoreMode.expDiff`: `q = b·x` (or `x·b`) with `DEREF`s through `b` and `q` at offset `0` among the atoms."""
    lds = {a[2] for a in atoms if a[0] == 'load' and a[3] == 0}
    return any(a[0] == 'mul' and a[1] in lds and ((a[3] == x and a[2] in lds) or (a[2] == x and a[3] in lds))
               for a in atoms)


def res_fam(k, r, G):
    """`CoreMode.resFam` at the mode signature `G`: an exponent bound of a range checked value (`rc`), of a parameter an
    entry run bounds and the quotient of two dereferenced addresses (`exp`), `column_selector`'s lowest digit in its
    strided table (`cs`), a residual of a family under branch conditions. (Top-level selectors, `sel`, are not emitted
    by the solver.)"""
    import callc
    params, body = I.CORE[k]
    if r[0] == 'under':
        return res_fam(k, r[2], G)
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num':
        x, n = r[1][1], r[2][1]
        if not n < CAPE:
            return False
        N = rc_bound(top_atoms(body), x)
        if N is not None and N <= n:
            return True
        return 2 ** 28 <= n and x < len(params) and 2 + x in callc.exp_cells(G) and exp_diff(top_atoms(body), x)
    if r[0] == 'sub':
        kap = cs_kappa(k)
        return kap is not None and r == cs_sub(kap)
    return False


def res_ok(k, res, S):
    return all(res_fam(k, r, S[k]) for r in res)


def cs_reads(EM):
    """The solver's read witnesses also from the `cs` family: `column_selector__L{κ}`'s lowest digit's read, a cell of
    its strided table's run in scope by the residual `csSub κ`."""
    base = EM.Solver.pt

    def pt(self, st, c, want=None, depth=0):
        w = base(self, st, c, want, depth)
        kap = cs_kappa(self.k)
        if w is not None or want is not None or kap is None:
            return w
        r = cs_sub(kap)
        if c != r[1]:
            return None
        R = EM.C.runF(st.env, r[2])
        for n, R2 in sorted(st.rs.items()):
            if R2 == R:
                return ('run', n, [self.use(('cs', kap), r)])
        return None
    return base, pt


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
    EM = callc._em()
    base, EM.Solver.pt = cs_reads(EM)
    got, lost = {}, collections.Counter()
    try:
        cands = [k for k in callc.candidates() if k not in out] + [k for k in leaf_candidates() if k not in out]
        for k in cands:
            try:
                try:
                    r = callc.infer_one(k, S, allow=lambda k, res: res_ok(k, res, S))
                except callc.No:
                    # the check with calls' own features (`ptr`, `pfr`), its residuals of families
                    I.F.clear()
                    I.F.update(saved)
                    try:
                        r = callc.infer_one(k, S, allow=lambda k, res: res_ok(k, res, S))
                    finally:
                        I.F.clear()
                        I.F.update(FEATURES)
            except callc.No as e:
                lost[str(e).split(':')[0]] += 1
                continue
            r['text'] = callc.ldata(k, r)
            got[k] = r
    finally:
        I.F.clear()
        I.F.update(saved)
        EM.Solver.pt = base
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
