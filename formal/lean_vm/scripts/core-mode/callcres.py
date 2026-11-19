"""The core route's functions whose heap certificates need residuals (`CoreMode/CoreRes.lean`): `callc.py`'s check
with calls, on the bodies it does not close without residuals (its own candidates, and the straight-line bodies
milestone 1's check leaves uncovered), with the inference's index rules (`idx`, `rules`) on, each certificate's
residuals of a family the honest instances make true (`CoreMode.resFam`, sound in `EndExecCoreRes.lean`).

`extend(out, why, S)` adds them to `callc.results()`'s. Usage (a census): python3 -I scripts/core-mode/callcres.py"""
import os, re, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
from pmap import pmap  # noqa: E402
sys.modules.setdefault('infer', I)

CAPE = 2 ** 62
FEATURES = {'ptr', 'pfr', 'idx', 'rules'}
# `verify_tables`: its arms' growing blocks, its buffers through its hinted order (`perm`), a run up to a bound over
# values before one up to a constant (`vthi`), the bounds its exponent family proves stated (`lastres`)
VT_FEATS = {'verify_tables': (FEATURES | {'armblock', 'perm', 'vthi', 'lastres'},),
            'certify_placement': (FEATURES | {'rcpts', 'perm'},)}


_SIGS = {}


def vs_ok(k, r):
    """A residual of a family at `verify_sub` (the pool's facts the solver may use there)."""
    if not _SIGS:
        import route
        _SIGS.update(route.sigs())
    return res_ok(k, [r], _SIGS)


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
    [('verify_tables', 9, None, 33), ('verify_tables', 10, 0, 33)] + \
    [('verify_tables', 10, j + 1, 31) for j in range(6)]
DIM_FACTS = [('check_opening_terminal', 8, 4, {(1, 0), (0, 19)}),
             ('check_opening_terminal', 8, 5, {(j, 0) for j in range(2, 8)})]


# `verify_tables`' value `g_zc_n` (`EndExec.VtQ`)
VT_ZC = 2545


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


def expq0(k, x):
    """`CoreMode.expQ0`: `expq1`, `check_opening_terminal`'s `gmv` (`termGm`), `verify_tables`' `g_zc_n` (`vtZc`)."""
    b = expq1(k, x)
    if b is not None:
        return b
    # `check_opening_terminal`'s `gmv = g^sl`, `sl <= 30` (`CoreMode.termGm`)
    if k == 'check_opening_terminal' and len(I.CORE[k][0]) > 19 and x == I.CORE[k][0][19]:
        return 31
    # `verify_tables`' `g_zc_n = g^n`, `n < 34` (`CoreMode.vtZc`)
    if k == 'verify_tables' and x == VT_ZC:
        return 34
    return None


def expq_bound(k, x):
    """`CoreMode.expQB`: `expq0`, or the first top-level atom defining `x` of a product `x = a·w` of such a value `a`
    and a constant `g^c` (bound plus `c`) or a copy of such a value."""
    b = expq0(k, x)
    if b is not None:
        return b
    b = vs_bound(k, x)
    if b is not None:
        return b
    atoms = top_atoms(I.CORE[k][1])
    cs = _consts(atoms)
    for a in atoms:
        if a[0] == 'mul' and a[1] == x:
            b1, c = expq0(k, a[2]), cs.get(a[3])
            e = I.POWS.get(c[0]) if c is not None and c[1] == 0 else None
            return b1 + e if b1 is not None and e is not None else None
        if a[0] == 'copy' and a[1] == x:
            return expq0(k, a[2])
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


def nz_atoms(c, body):
    """`CoreMode.nzAtoms`: the top-level atoms of the arm taken when `c` is nonzero (an `ite`'s second) of each top-level
    branch on `c` that does not return, before the first statement that may return."""
    out = []
    for s in body:
        if s[0] == 'ite' and s[1] == c and not has_ret(s):
            out += top_atoms(s[3])
        if s[0] == 'ret' or has_ret(s):
            break
    return out


def const_of(atoms, v):
    """`Res.constOf`: the first constant `v` gets among the atoms."""
    for a in atoms:
        if a[0] == 'const' and a[1] == v:
            return tuple(a[2])
    return None


def neg_pair(body, k, x, v, off, n):
    """`CoreMode.negPair`: `e(x·v·g^off) < n` where `k` is nonzero."""
    top = top_atoms(body)
    if not off < 2 ** 33 or rc_bound(top, x) is None:
        return False
    if not any(a[0] == 'const' and a[1] == v and a[2][1] == 0 and I.gf_mulx(a[2][0], 1) == 1 for a in nz_atoms(k, body)):
        return False
    for a in top:
        if a[0] != 'add' or a[1] != k:
            continue
        y, o = a[2], a[3]
        for b in top:
            if b[0] == 'mul' and b[1] == y and b[2] == x:
                w, w2 = const_of(top, o), const_of(top, b[3])
                N = rc_bound(top, y)
                if w is not None and w == w2 and w == (I.gf_mulx(1, off), 0) and N is not None and N <= n + 1:
                    return True
    return False


def neg_fam(k, conds, r):
    """`CoreMode.negFam`: under a condition `c ≠ 0`, `e(x·v·g^off) < n`, either base first (`neg_pair`)."""
    if r[0] != 'lt' or r[1][0] != 'mono' or r[2][0] != 'num' or not r[2][1] < CAPE:
        return False
    (bs, off), n = r[1][1], r[2][1]
    if len(bs) != 2 or bs[0][1] != 1 or bs[1][1] != 1:
        return False
    body = I.CORE[k][1]
    (a, _), (b, _) = bs
    return any(c[0] == 'nonzero' and (neg_pair(body, c[1], a, b, off, n) or neg_pair(body, c[1], b, a, off, n))
               for c in conds)


def res_fam(k, r, G):
    """`CoreMode.resFam` at the mode signature `G`: an exponent bound of a range checked value (`rc`), of a parameter an
    entry run bounds and the quotient of two dereferenced addresses (`exp`), `column_selector`'s lowest digit in its
    strided table (`cs`), an exponent bound `p·g` of a value range checked against `p` (`rcv`), a residual of a family
    under branch conditions; a top-level selector's word times `g^c` below `n` (`sel`, the solver's run bounds, `sel_facts`).
    (Top-level selectors' own `sel` residuals come from `callc`'s own guarantees only.)"""
    import callc
    params, body = I.CORE[k]
    if r[0] == 'under':
        return res_fam(k, r[2], G) or neg_fam(k, r[1], r[2])
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
    if r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'val':
        # `rcn`: `x` range checked against `k = p·w`, `w` the constant `g⁻¹`
        x, p = r[1][1], r[2][1]
        top = top_atoms(body)

        def inv(w):
            c = const_of(top, w)
            return c is not None and c[1] == 0 and I.gf_mulx(c[0], 1) == 1
        return any(a[0] == 'rangeCheck' and a[1] == x and
                   any(b[0] == 'mul' and b[1] == a[5] and b[2] == p and inv(b[3]) for b in top) for a in top)
    if r[0] == 'subR':
        return sub_rc(r[1], r[2])
    if r[0] == 'sub':
        kap = cs_kappa(k)
        return (kap is not None and r == cs_sub(kap)) or r == vt_st_sub(k, r[1])
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


# `CoreMode.stLoops`: the loops reading the proof stream past a cursor, by stable name: (caller's cell `D` holding
# the stream, the cursor value `v`, the words `S` read past it an iteration)
ST_LOOPS = {
    'keccak_layer__L0_loop0': (17, 20, 16), 'keccak_layer__L1_loop0': (17, 20, 16),
    'keccak_layer__L0_loop1': (17, 14, 2), 'keccak_layer__L1_loop1': (17, 14, 2),
    'verify_bus_gkr_loop0_loop0': (11, 13, 8), 'verify_tables_loop0': (22, 11, 3),
}


def st_sub(k, c):
    """`CoreMode.stSub`: a stream-cursor loop's read `[v]·g^c`, `c < S`, a cell of the run `[ghost₀]·[0, 8192)`, or
    None."""
    p = ST_LOOPS.get(I.callee(k)) or ST_LOOPS.get(k)
    if p is None or tuple(c[0]) != ((p[1], 1),) or not c[1] < p[2]:
        return None
    return ('sub', c, ((((I.GB, 1),), 0), 1, ('num', 0), ('num', 8192)))


# `CoreMode.vsPows`, `vsMuls`, `vsLes`, `vsCurs`: `verify_sub`'s exponent family (`EndExec.VsQ`): its values' exponent
# bounds, the products naming one, the orders `e(x) <= e(y) + c`, the cursors in its stream `[25]·[0, 8192)` with
# room for `207` words
VS_POWS = {86: (0, 30), 87: (0, 30), 88: (0, 30), 89: (0, 30), 90: (0, 30), 91: (9, 24), 583: (9, 24),
           253: (20, 33), 579: (9, 33), 276: (20, 30), 278: (0, 10)}
VS_MULS = {(276, 277): 278}
VS_LES = [(91, 579, 0), (583, 579, 0), (276, 278, 20)]
VS_CURS = [567, 578, 595]
VS_STREAM, VS_ROOM = 25, 207


def vs_iv(i):
    """`CoreMode.vsIv`: an index's base (or None), offset and exponent bounds."""
    if i[0] == 'num':
        return (None, i[1], i[1], i[1])
    if i[0] == 'val':
        bs, off = ((i[1], 1),), 0
    else:
        bs, off = i[1]
    if len(bs) == 1 and bs[0][1] == 1:
        x = bs[0][0]
    elif len(bs) == 2 and bs[0][1] == 1 and bs[1][1] == 1 and (bs[0][0], bs[1][0]) in VS_MULS:
        x = VS_MULS[(bs[0][0], bs[1][0])]
    else:
        return None
    if x not in VS_POWS:
        return None
    lo, hi = VS_POWS[x]
    return (x, off, lo + off, hi + off)


def vs_exp(k, r):
    """`CoreMode.vsExp`: a residual of `verify_sub`'s exponent family."""
    if k != 'verify_sub':
        return False
    if r[0] == 'under':
        return vs_exp(k, r[2])
    if r[0] == 'lt':
        a, b = vs_iv(r[1]), vs_iv(r[2])
        if a is None or b is None or not (a[3] < CAPE and b[3] < CAPE):
            return False
        return a[3] < b[2] or (a[0] is not None and b[0] is not None and
                               any(x == a[0] and y == b[0] and a[1] + c < b[1] for x, y, c in VS_LES))
    if r[0] == 'sub':
        c, q = r[1], r[2]
        return q == ((((VS_STREAM, 1),), 0), 1, ('num', 0), ('num', 8192)) and len(c[0]) == 1 and \
            c[0][0][0] in VS_CURS and c[0][0][1] == 1 and c[1] < VS_ROOM
    return False


def vs_bound(k, x):
    """`verify_sub`'s exponent bound of `x` (`vsExp`), plus one."""
    return VS_POWS[x][1] + 1 if k == 'verify_sub' and x in VS_POWS else None


# `CoreMode.cpRanks`: `certify_placement`'s ranks' group values (`B1.Tables.cpRB`)
CP_RANKS = [138] + [131 + 18 * r for r in range(1, 9)]


def cp_perm(k, r):
    """`CoreMode.cpPerm`: `certify_placement`'s cell `[137]·g^j`, `j < 9`, one of `[137]·[v]` over its ranks' groups."""
    return k == 'certify_placement' and r[0] == 'subP' and r[1][0] == ((137, 1),) and r[1][1] < 9 and \
        tuple(r[2]) == tuple((((137, 1), (v, 1)), 0) for v in CP_RANKS)


def rc_pts(k, r):
    """`CoreMode.rcPts`: a cell `[B]·[J]·g^o`, `J` range checked below `g^N` at the top level (`Res.rcBound`), one of
    the points `[B]·g^(o + t)`, `t < N`."""
    if r[0] != 'subP' or len(r[1][0]) != 2 or any(e != 1 for _, e in r[1][0]):
        return False
    (a, _), (b, _) = r[1][0]
    atoms = top_atoms(I.CORE[k][1])
    for B, J in ((a, b), (b, a)):
        N = rc_bound(atoms, J)
        if N is not None and N <= 64 and all((((B, 1),), r[1][1] + t) in r[2] for t in range(N)):
            return True
    return False


# `CoreMode.splitsC`: a function's `g`-power `n = q^S·r` split from hinted bits, on every returning path `q` (a
# monomial) names `g^a`, the selector `rv` and the monomial `r` name `g^b`, `a < A`, `b < S`
SPLITS = {
    'rs_eq_run': (((27, 1), (31, 1), (36, 1)), ((13, 1), (17, 1), (22, 1)), 23, 3, 8, 8),
    'shared_selector_tables': (((24, 1), (28, 1), (33, 1), (38, 1)), ((15, 1), (19, 1)), 20, 5, 4, 16),
}


def pow_b(k, bs):
    return tuple((b, k * e) for b, e in bs)


def split_res(sp, cs, r):
    """`CoreMode.splitRes`: under the branch conditions `cs`, an exponent bound of `q^k·g^c` (`k` one or `S`) or of
    `r·g^c` below a constant; `q^S·g^c` below `n` under the arm `j > c` of `rv`; the stride-`S` run `[b·g^i]` over
    `[0, e(q))`, `i < S`, inside `[b]·[0, e(n))`."""
    q, rb, rv, n, S, A = sp
    if r[0] == 'under':
        return split_res(sp, cs + list(r[1]), r[2])
    if r[0] == 'lt' and r[1][0] == 'mono' and r[2][0] == 'num':
        (bs, off), N = r[1][1], r[2][1]
        return N < CAPE and ((bs == q and A - 1 + off < N) or (bs == pow_b(S, q) and S * (A - 1) + off < N) or
                             (bs == rb and S - 1 + off < N))
    if r[0] == 'lt' and r[1][0] == 'mono' and r[2] == ('val', n):
        bs, off = r[1][1]
        return bs == pow_b(S, q) and any(c[0] == 'arm' and c[1] == rv and off < c[2] < CAPE for c in cs)
    if r[0] == 'subR':
        (Q, S1, lo, hi), (R, S2, lo2, hi2) = r[1], r[2]
        return S1 == S and lo == ('num', 0) and hi == ('mono', (q, 0)) and Q[1] < S and R == (Q[0], 0) and \
            S2 == 1 and lo2 == ('num', 0) and hi2 == ('val', n)
    return False


def split_fam(k, r):
    """`CoreMode.splitFam`."""
    sp = SPLITS.get(k)
    return sp is not None and split_res(sp, [], r)


def res_ok(k, res, S):
    """`CoreMode.resFamG`: a ghost-free residual of a family, or the ghost family's."""
    import vtexp
    return all(((res_fam(k, r, S[k]) or split_fam(k, r) or vtexp.vt_perm(k, r) or vs_exp(k, r) or cp_perm(k, r) or
                 rc_pts(k, r)) and all(v < I.GB for v in vals(r))) or
               (r[0] == 'sub' and (ml_sub(k, r[1]) == r or st_sub(k, r[1]) == r)) or vtexp.vt_exp(k, r) for r in res)


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


# `verify_tables`' last table sumcheck record's cursor and its stream parameter (`CoreMode.vtStC`)
VT_ST, VT_STREAM = 2652, 20


def vt_st_sub(k, c):
    """`CoreMode.vtStC`: `verify_tables`' read `c` words past its table sumcheck's last cursor, `c < 153`, one of its
    stream's `[20]·[0, 8192)`."""
    if k == 'verify_tables' and c[0] == ((VT_ST, 1),) and c[1] < 153:
        return ('sub', c, ((((VT_STREAM, 1),), 0), 1, ('num', 0), ('num', 8192)))
    return None


def vt_facts(EM):
    """The solver's exponent facts also from `verify_tables`' exponent family (`vtexp`, `CoreMode.vtExp`): `e(a) <
    e(b)` stated under the site's path when the family proves it there."""
    import vtexp
    base = EM.Solver.fact
    EM.RES_FILTER[0] = lambda k, r: (k != 'verify_tables' or 'lastres' not in I.F or vtexp.vt_exp(k, r) or
                                     vtexp.vt_perm(k, r) or (r[0] == 'sub' and vt_st_sub(k, r[1]) == r)) and \
        (k != 'verify_sub' or vs_ok(k, r))

    def fact(self, st, a, b):
        f = base(self, st, a, b)
        if f is not None or self.k != 'verify_tables':
            return f
        g = tuple(dict.fromkeys(self.X.path))
        r = ('lt', self.idx(st, a), self.idx(st, b))
        wr = ('under', g, r) if g else r
        if not vtexp.vt_exp(self.k, wr):
            return None
        return [self.use(('vtexp', a, b, g), wr)]
    return base, fact


def cs_reads(EM):
    """The solver's read witnesses also from the `cs` family: `column_selector__L{κ}`'s lowest digit's read, a cell of
    its strided table's run in scope by the residual `csSub κ`; and from the ghost families `ml` (`ml_sub`), `st`
    (`st_sub`)."""
    base = EM.Solver.pt

    def pt(self, st, c, want=None, depth=0):
        w = base(self, st, c, want, depth)
        if w is not None or want is not None:
            return w
        kap = cs_kappa(self.k)
        r = cs_sub(kap) if kap is not None else (ml_sub(self.k, c) or st_sub(self.k, c) or vt_st_sub(self.k, c))
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
    """Straight-line bodies without calls milestone 1's check leaves uncovered, or whose mode signature guarantees
    pointer runs (`postP`), which milestone 1's does not state."""
    import heap, route
    S = route.sigs()
    import callc
    return sorted(k for k in heap.scope_fns() if straight(I.CORE[k][1]) and
                  (heap.Fn(k).run().fail is not None or (k in S and S[k]['postP']) or callc.has_fa(I.CORE[k][1])))


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
    _, EM.Solver.fact = vt_facts(EM)
    got, lost = {}, collections.Counter()
    def one(k):
        # these features, then the check with calls' own (`ptr`, `pfr`), then the arms' growing blocks
        # (`armblock`, `ab`), each with residuals of families; `nohs`: no upper bound met by its next's fact, whose
        # residual is of no family; a dispatch's returned pointer (`retP`, `retM`: `vp`) with a loop's runs at its
        # conditional entry (`callIfR`)
        r, err = None, None
        for feats in (FEATURES, saved, FEATURES | {'armblock'}, FEATURES | {'dup'}, FEATURES | {'jt'},
                      FEATURES | {'dup', 'nohs'}, FEATURES | {'retP', 'retM', 'callIfR'}) + VT_FEATS.get(k, ()):
            I.F.clear()
            I.F.update(feats)
            try:
                r = callc.infer_one(k, S, allow=lambda k, res: res_ok(k, res, S))
                break
            except callc.No as e:
                err = err or e
        I.F.clear()
        I.F.update(FEATURES)
        if r is not None:
            r['text'] = callc.ldata(k, r)
        return r, err
    try:
        cands = [k for k in callc.candidates() if k not in out] + [k for k in leaf_candidates() if k not in out]
        # each candidate on its own, in worker processes (`pmap.py`)
        for k, (r, err) in zip(cands, pmap(one, cands)):
            if r is None:
                lost[str(err).split(':')[0]] += 1
                continue
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
