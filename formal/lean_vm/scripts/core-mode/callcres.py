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


# `Res.expFacts` (`Res/SelDefs.lean`): function, parameter, offset (`None`: its word; `k`: the word at
# `[parameter]·g^k`), bound; `Res.dimFacts` (`Res/TermDefs.lean`): function, base parameter, bound parameter, pairs
# `(k, c)` (`busPairs`, `tabPairs`: `CLAIM_KAPPA_SRC` with `CLAIM_KAPPA_ADJ`, a subset suffices here)
EXP_FACTS = [('check_opening_terminal', 7, None, 31), ('check_opening_terminal', 8, 0, 1)] + \
    [('check_opening_terminal', 8, j + 1, 31) for j in range(7)] + \
    [('verify_tables', 9, None, 33), ('verify_tables', 10, 0, 33)]
DIM_FACTS = [('check_opening_terminal', 8, 4, {(1, 0), (0, 19)}),
             ('check_opening_terminal', 8, 5, {(j, 0) for j in range(2, 8)})]


def _consts(atoms):
    out = {}
    for a in atoms:
        if a[0] == 'const' and a[1] not in out:
            out[a[1]] = a[2]
    return out


def expq1(k, x):
    """`CoreMode.expQ1`: `x` a listed parameter, or loaded at a listed parameter's `[p]·g^k` by a top-level `load`:
    its fact's bound."""
    params, body = I.CORE[k]
    atoms = top_atoms(body)
    for f, pi, off, b in EXP_FACTS:
        if f != k or pi >= len(params):
            continue
        p = params[pi]
        if off is None and x == p:
            return b
        if off is not None and ('load', x, p, off) in atoms:
            return b
    return None


def deref_at(atoms, p):
    """`CoreMode.derefAt`: a `load` at offset `0` or a `touch` through `p`."""
    return any((a[0] == 'load' and a[2] == p and a[3] == 0) or (a[0] == 'touch' and a[2] == p) for a in atoms)


def mul_of(atoms, x):
    """`CoreMode.mulOf`: the first product `x = a·b`."""
    for a in atoms:
        if a[0] == 'mul' and a[1] == x:
            return a[2], a[3]
    return None


def pow_of(c):
    """`Res.powOf`."""
    return I.POWS.get(c[0]) if c is not None and c[1] == 0 else None


def bit_pow(atoms, x):
    """`CoreMode.bitPow`: `x = 1 + b·w`, `b·b = b`, `w = 1 + g^m`: `m`."""
    cs = _consts(atoms)
    for a in atoms:
        if a[0] == 'add' and a[1] == x and cs.get(a[2]) == (1, 0):
            m = mul_of(atoms, a[3])
            if m is None or ('mul', m[0], m[0], m[0]) not in atoms or m[1] not in cs:
                continue
            c = cs[m[1]]
            e = pow_of((c[0] ^ 1, c[1]))
            if e is not None:
                return e
    return None


EXP_FUEL = 6


def exp_m(atoms, f, x):
    """`CoreMode.expM`: `x = g^e`, `e` at most the result (`addr`)."""
    if f == 0:
        return None
    if deref_at(atoms, x):
        return 2 ** 28 - 1
    m = mul_of(atoms, x)
    if m is not None:
        a, b = exp_m(atoms, f - 1, m[0]), exp_m(atoms, f - 1, m[1])
        return a + b if a is not None and b is not None else None
    e = bit_pow(atoms, x)
    if e is not None:
        return e
    return pow_of(_consts(atoms).get(x))


def addr_bound(k, x):
    """`e(x) < expM + 1` (`addr`)."""
    M = exp_m(top_atoms(I.CORE[k][1]), EXP_FUEL, x)
    return M + 1 if M is not None else None


def expq_bound(k, x):
    """`CoreMode.expQB`: `expq1`, or a top-level product `x = a·w` of such a value `a` and a constant `g^c`: bound
    plus `c`."""
    b = expq1(k, x)
    if b is not None:
        return b
    # `check_opening_terminal`'s `gmv = g^sl`, `sl <= 30` (`CoreMode.termGm`)
    if k == 'check_opening_terminal' and len(I.CORE[k][0]) > 19 and x == I.CORE[k][0][19]:
        return 31
    atoms = top_atoms(I.CORE[k][1])
    cs = _consts(atoms)
    for a in atoms:
        if a[0] == 'mul' and a[1] == x:
            b1, c = expq1(k, a[2]), cs.get(a[3])
            e = I.POWS.get(c[0]) if c is not None and c[1] == 0 else None
            return b1 + e if b1 is not None and e is not None else None
    return None


def dim_ok(k, x, t, p, u):
    """`CoreMode.dimLt`: `x` loaded at the listed base parameter's `[kb]·g^j` by a top-level `load`, `p` the listed
    bound parameter, a pair `(j, c)`, `t < c + u`."""
    params, body = I.CORE[k]
    atoms = top_atoms(body)
    for f, kbi, gbi, pairs in DIM_FACTS:
        if f != k or max(kbi, gbi) >= len(params) or params[gbi] != p or not u < 2 ** 33:
            continue
        for j, c in pairs:
            if ('load', x, params[kbi], j) in atoms and t < c + u:
                return True
    return False


def expq_facts(EM):
    """The solver's exponent facts also from the instance's exponent and dimension facts (`expQ`, `dim`): `x·g^c`
    below `g^n`, `g^k` below `x·g^c` (`k < c`), and a loaded `kappa_base` word times `g^t` below `p·g^u`."""
    base = EM.Solver.fact

    def one(c):
        return len(c[0]) == 1 and c[0][0][1] == 1

    def fact(self, st, a, b):
        f = base(self, st, a, b)
        if f is not None:
            return f
        C = EM.C
        if one(a) and C.idxF(st.env, ('val', a[0][0][0])) != ((a[0][0],), 0):
            return None
        if one(b) and C.idxF(st.env, ('val', b[0][0][0])) != ((b[0][0],), 0):
            return None
        if one(a) and not b[0] and b[1] < CAPE:
            B = expq_bound(self.k, a[0][0][0])
            if B is not None and B + a[1] <= b[1]:
                ra = ('val', a[0][0][0]) if a[1] == 0 else ('mono', a)
                return [self.use(('expq', a, b), ('lt', ra, ('num', b[1])))]
        if not a[0] and one(b) and a[1] < b[1]:
            B = expq_bound(self.k, b[0][0][0])
            if B is not None and B + b[1] < CAPE:
                return [self.use(('expq', a, b), ('lt', ('num', a[1]), ('mono', b)))]
        if one(a) and a[1] == 0 and not b[0] and b[1] < CAPE:
            # `addr`: `x = g^e`, `e` at most `expM`
            B = addr_bound(self.k, a[0][0][0])
            if B is not None and B <= b[1]:
                return [self.use(('addr', a, b), ('lt', ('val', a[0][0][0]), ('num', b[1])))]
        if one(a) and a[1] == 0 and one(b) and b[1] == 1 and \
                ('rangeCheck', a[0][0][0], b[0][0][0]) in {(t[0], t[1], t[5]) for t in top_atoms(I.CORE[self.k][1]) if t[0] == 'rangeCheck'}:
            # `rcv`: `x` range checked against `p`
            return [self.use(('rcv', a, b), ('lt', ('val', a[0][0][0]), ('mono', b)))]
        if one(a) and one(b) and dim_ok(self.k, a[0][0][0], a[1], b[0][0][0], b[1]):
            ra = ('val', a[0][0][0]) if a[1] == 0 else ('mono', a)
            return [self.use(('dim', a, b), ('lt', ra, ('mono', b)))]
        return None
    return base, fact


def sub_rc(q, r):
    """`CoreMode.subRC`: a run of constant bounds inside one of the same bases."""
    (qb, qo), S, ql, qh = q
    (rb, ro), S2, rl, rh = r
    if not (ql[0] == qh[0] == rl[0] == rh[0] == 'num'):
        return False
    if tuple(qb) != tuple(rb) or S != S2 or not 0 < S or ro > qo or (qo - ro) % S:
        return False
    k = (qo - ro) // S
    return rl[1] <= ql[1] + k and qh[1] + k <= rh[1] and all(x < CAPE for x in (ql[1], qh[1], rl[1], rh[1]))


def res_fam(k, r, G):
    """`CoreMode.resFam` at the mode signature `G`: an exponent bound of a range checked value (`rc`), of a parameter an
    entry run bounds and the quotient of two dereferenced addresses (`exp`), `column_selector`'s lowest digit in its
    strided table (`cs`), an exponent bound `p·g` of a value range checked against `p` (`rcv`), a residual of a family
    under branch conditions; a top-level selector's word times `g^c` below `n` (`sel`, the solver's run bounds, `sel_facts`).
    (Top-level selectors' own `sel` residuals come from `callc`'s own guarantees only.)"""
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
        if any(x2 == x and m <= n for x2, m in callc.top_sels(body)):
            return True
        B = expq_bound(k, x)
        if B is not None and B <= n:
            return True
        B = addr_bound(k, x)
        if B is not None and B <= n:
            return True
        return 2 ** 28 <= n and x < len(params) and 2 + x in callc.exp_cells(G) and exp_diff(top_atoms(body), x)
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'mono':
        # `rcv`: `x` range checked against the value `p`, the bound `p·g`
        c = r[2][1]
        if len(c[0]) == 1 and c[0][0][1] == 1 and dim_ok(k, r[1][1], 0, c[0][0][0], c[1]):
            return True
        if len(c[0]) != 1 or c[0][0][1] != 1 or c[1] != 1:
            return False
        return any(a[0] == 'rangeCheck' and a[1] == r[1][1] and a[5] == c[0][0][0] for a in top_atoms(body))
    if r[0] == 'lt' and r[1][0] == 'mono' and r[2][0] == 'num':
        # `sel` of a selector's word times `g^c`: `e(x·g^c) < n`, `x` a top-level selector of `m` arms, `m + c <= n`
        c, n = r[1][1], r[2][1]
        if len(c[0]) != 1 or c[0][0][1] != 1 or not n < CAPE:
            return False
        if any(x == c[0][0][0] and m + c[1] <= n for x, m in callc.top_sels(body)):
            return True
        # `rc` likewise: `x` range checked against `g^(N - 1)`, `N + c <= n`
        N = rc_bound(top_atoms(body), c[0][0][0])
        if N is not None and N + c[1] <= n:
            return True
        B = expq_bound(k, c[0][0][0])
        return B is not None and B + c[1] <= n
    if r[0] == 'lt' and r[1][0] == 'num' and r[2][0] == 'mono':
        # `expQ`: `g^j` below `x·g^c`, `j < c`, `x` of an exponent fact of bound `b`, `b + c < 2^62`
        c, j = r[2][1], r[1][1]
        if len(c[0]) != 1 or c[0][0][1] != 1 or not j < c[1]:
            return False
        # `sel`: `x` a top-level selector of `m` arms, `m + c < 2^62`
        if any(x == c[0][0][0] and m + c[1] < CAPE for x, m in callc.top_sels(body)):
            return True
        B = expq_bound(k, c[0][0][0])
        return B is not None and B + c[1] < CAPE
    if r[0] == 'lt' and r[1][0] == 'mono' and r[2][0] == 'mono':
        # `dim`: a loaded `kappa_base` word times `g^t` below `p·g^u`
        a, c = r[1][1], r[2][1]
        return len(a[0]) == 1 and a[0][0][1] == 1 and len(c[0]) == 1 and c[0][0][1] == 1 and \
            dim_ok(k, a[0][0][0], a[1], c[0][0][0], c[1])
    if r[0] == 'subR':
        return sub_rc(r[1], r[2])
    if r[0] == 'sub':
        kap = cs_kappa(k)
        return kap is not None and r == cs_sub(kap)
    return False


def vals(r):
    """`CRes.vals`: the value numbers a residual names."""
    def cell(c):
        return [b for b, _ in c[0]]

    def idx(i):
        return [] if i[0] == 'num' else ([i[1]] if i[0] == 'val' else cell(i[1]))

    def run(q):
        return cell(q[0]) + idx(q[2]) + idx(q[3])
    if r[0] == 'lt':
        return idx(r[1]) + idx(r[2])
    if r[0] == 'sub':
        return cell(r[1]) + run(r[2])
    if r[0] == 'subR':
        return run(r[1]) + run(r[2])
    if r[0] == 'under':
        return [c[1] for c in r[1]] + vals(r[2])
    if r[0] == 'subP':
        return cell(r[1]) + [b for c in r[2] for b in cell(c)]
    return []


def ml_sub(k, c):
    """`CoreMode.mlSub`: `child_claim_list_mono_last__L{k}`'s read of claim `jj`'s entry `c`, the run of its caller's
    table (its ghost, stride 4, below the exponent of its parameter `3`), or None."""
    import callc
    kk = callc.ml_k(k)
    bs, off = c
    jj = off // 4
    if kk is None or jj >= kk or tuple(bs) != ((5, 1),) + tuple((6 + 10 * i, 4) for i in range(jj + 1)):
        return None
    return ('sub', c, ((((I.GB, 1),), off % 4), 4, ('num', 0), ('val', 3)))


def res_ok(k, res, S):
    """`CoreMode.resFamG`: a ghost-free residual of a family, or the ghost family's."""
    return all((res_fam(k, r, S[k]) and all(v < I.GB for v in vals(r))) or
               (r[0] == 'sub' and ml_sub(k, r[1]) == r) for r in res)


def sel_facts(EM):
    """The solver's exponent facts `(x·g^c, g^n)` also from the `sel` family: `x` a top-level selector of `m` arms,
    `m + c <= n`, stated as the residual `e(x·g^c) < n` (`CoreMode.resFam`)."""
    import callc
    C = EM.C
    base = EM.Solver.fact

    def fact(self, st, a, b):
        f = base(self, st, a, b)
        if f is not None or b[0] or not b[1] < CAPE or len(a[0]) != 1 or a[0][0][1] != 1 or a[1] == 0:
            return f
        x = a[0][0][0]
        if C.idxF(st.env, ('val', x)) != (((x, 1),), 0):
            return None
        for x2, m in callc.top_sels(I.CORE[self.k][1]):
            if x2 == x and m + a[1] <= b[1]:
                return [self.use(('sel', x, a[1], b[1]), ('lt', ('mono', a), ('num', b[1])))]
        return None
    return base, fact


def cs_reads(EM):
    """The solver's read witnesses also from the `cs` family: `column_selector__L{κ}`'s lowest digit's read, a cell of
    its strided table's run in scope by the residual `csSub κ`; and from the ghost family `ml` (`ml_sub`)."""
    base = EM.Solver.pt

    def pt(self, st, c, want=None, depth=0):
        w = base(self, st, c, want, depth)
        if w is not None or want is not None:
            return w
        kap = cs_kappa(self.k)
        r = cs_sub(kap) if kap is not None else ml_sub(self.k, c)
        if r is None or c != r[1]:
            return None
        R = EM.C.runF(st.env, r[2])
        for n, R2 in sorted(st.rs.items()):
            if R2 == R:
                return ('run', n, [self.use(('cs', kap) if kap is not None else ('ml', c), r)])
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
    basef, EM.Solver.fact = sel_facts(EM)
    _, EM.Solver.fact = expq_facts(EM)
    got, lost = {}, collections.Counter()
    try:
        cands = [k for k in callc.candidates() if k not in out] + [k for k in leaf_candidates() if k not in out]
        for k in cands:
            # these features, then the check with calls' own (`ptr`, `pfr`), then the arms' growing blocks
            # (`armblock`, `ab`), each with residuals of families
            r, err = None, None
            for feats in (FEATURES, saved, FEATURES | {'armblock'}, FEATURES | {'dup'}):
                I.F.clear()
                I.F.update(feats)
                try:
                    r = callc.infer_one(k, S, allow=lambda k, res: res_ok(k, res, S))
                    break
                except callc.No as e:
                    err = err or e
            I.F.clear()
            I.F.update(FEATURES)
            if r is None:
                lost[str(err).split(':')[0]] += 1
                continue
            r['text'] = callc.ldata(k, r)
            got[k] = r
    finally:
        I.F.clear()
        I.F.update(saved)
        EM.Solver.pt = base
        EM.Solver.fact = basef
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
