"""The core route's functions whose heap certificates need residuals (`CoreMode/CoreRes.lean`): `callc.py`'s check
with calls, on the bodies it does not close without residuals (its own candidates, and the straight-line bodies
the check without calls leaves uncovered), with the inference's index rules (`idx`, `rules`) on, each certificate's
residuals of a family the honest instances make true (`CoreMode.resFam`, sound in `EndExecCoreRes.lean`).

`extend(out, why, S)` adds them to `callc.results()`'s."""
import os, re, sys, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import infer as I  # noqa: E402
import fnrules as R  # noqa: E402
import heapc  # noqa: E402
from pmap import pmap  # noqa: E402
sys.modules.setdefault('infer', I)

CAPE = 2 ** 62
FEATURES = {'ptr', 'pfr', 'idx', 'rules'}
# each function's own feature sets, tried after the generic ones (its rule file's `FEATURES`)
VT_FEATS = {k: tuple(FEATURES | s for s in v) for k, v in R.table('FEATURES').items()}


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
    return not heapc.noret(s)


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


def exp_diff(atoms, x):
    """`CoreMode.expDiff`: `q = b·x` (or `x·b`) with `DEREF`s through `b` and `q` at offset `0` among the atoms."""
    lds = {a[2] for a in atoms if a[0] == 'load' and a[3] == 0}
    return any(a[0] == 'mul' and a[1] in lds and ((a[3] == x and a[2] in lds) or (a[2] == x and a[3] in lds))
               for a in atoms)


# `Res.expFacts`: function, parameter, offset (`None`: its word; `k`: the word at `[parameter]·g^k`), bound;
# `Res.dimFacts`: function, base parameter, bound parameter, pairs `(k, c)`; `CoreMode.expVals`: function, value,
# bound: each function's own (its rule file's)
EXP_FACTS = R.table('EXP_FACTS') or []
DIM_FACTS = R.table('DIM_FACTS') or []
EXP_VALS = R.table('EXP_VALS') or []


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
    """`CoreMode.expQ0`: `expq1`, or a listed value's bound (`CoreMode.expVal`)."""
    b = expq1(k, x)
    if b is not None:
        return b
    return next((b for f, v, b in EXP_VALS if f == k and v == x), None)


def expq_bound(k, x):
    """`CoreMode.expQB`: `expq0`, or the first top-level atom defining `x` of a product `x = a·w` of such a value `a`
    and a constant `g^c` (bound plus `c`) or a copy of such a value."""
    b = expq0(k, x)
    if b is not None:
        return b
    b = R.first('exp_bound', k, x)
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
    if not all(x < CAPE for x in (ql[1], qh[1], rl[1], rh[1])):
        return False
    if tuple(qb) != tuple(rb) or not 0 < S2 or S % S2 or not 0 < S or ro > qo or (qo - ro) % S2:
        return False
    k, m = (qo - ro) // S2, S // S2
    if m == 1:
        return rl[1] <= ql[1] + k and qh[1] + k <= rh[1]
    # stride a multiple: cell `j` of `q` is cell `k + m·j` of `r`
    return rl[1] <= k + m * ql[1] and k + m * max(qh[1] - 1, 0) < rh[1]


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


def arm_m(k, c, x):
    """`CoreMode.armM`: `x`'s exponent bound in the arm `c ≠ 0` takes: a range check's `N - 1`, else `exp_m`."""
    at = nz_atoms(c, I.CORE[k][1])
    N = rc_bound(at, x)
    return N - 1 if N is not None else exp_m(at, EXP_FUEL, x)


def top_prod(body, bs):
    """`CoreMode.topProd`: `Σ a·M` over the bases `(x, a)`, `M` the bound the top-level atoms give (`exp_m`)."""
    t = 0
    for x, a in bs:
        M = exp_m(top_atoms(body), EXP_FUEL, x)
        if M is None:
            return None
        t += a * M
    return t


def arm_prod(k, c, bs):
    """`CoreMode.armProd`: `Σ a·armM` over the bases `(x, a)`."""
    t = 0
    for x, a in bs:
        M = arm_m(k, c, x)
        if M is None:
            return None
        t += a * M
    return t


def neg_fam(k, conds, r):
    """`CoreMode.negFam`: under a condition `c ≠ 0`, `e(x·v·g^off) < n`, either base first (`neg_pair`); `e(x) < n` and
    `e(Π x^a·g^off) < n` from the arm `c ≠ 0` takes (`arm_m`, `arm_prod`)."""
    if r[0] != 'lt' or r[2][0] != 'num' or not r[2][1] < CAPE:
        return False
    n = r[2][1]
    if r[1][0] == 'val':
        return any(c[0] == 'nonzero' and (lambda M: M is not None and M < n)(arm_m(k, c[1], r[1][1])) for c in conds)
    if r[1][0] != 'mono':
        return False
    (bs, off) = r[1][1]
    if any(c[0] == 'nonzero' and (lambda M: M is not None and M + off < n)(arm_prod(k, c[1], bs)) for c in conds):
        return True
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
        # `addr` of a product: `Σ a·M` over the bases `(x, a)`, `M` the bound the top-level atoms give (`topProd`)
        M = top_prod(body, c[0])
        if n < CAPE and M is not None and M + c[1] < n:
            return True
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


# `CoreMode.stLoops`: the loops reading the proof stream past a cursor, by stable name: (caller's cell `D` holding
# the stream, the cursor value `v`, the words `S` read past it an iteration), each its function's own
ST_LOOPS = R.table('ST_LOOPS') or {}
# `CoreMode.cmK`: `child_claim_list_mono`'s frame loops, their claims a frame
CM_LOOPS = R.table('CM_LOOPS') or {}


def st_sub(k, c):
    """`CoreMode.stSub`: a stream-cursor loop's read `[v]·g^c`, `c < S`, a cell of the run `[ghost₀]·[0, 8192)`, or
    None."""
    p = ST_LOOPS.get(I.callee(k)) or ST_LOOPS.get(k)
    if p is None or tuple(c[0]) != ((p[1], 1),) or not c[1] < p[2]:
        return None
    return ('sub', c, ((((I.GB, 1),), 0), 1, ('num', 0), ('num', 8192)))


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
SPLITS = R.table('SPLITS') or {}


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
    """`CoreMode.resFamG`: a ghost-free residual of a family, generic or the function's own (`fam`), or of a ghost
    family, the stream-cursor loops' (`st_sub`) or the function's own (`ghost`)."""
    return all(((res_fam(k, r, S[k]) or split_fam(k, r) or rc_pts(k, r) or rc_tab(k, r) or R.some('fam', k, r)) and
                all(v < I.GB for v in vals(r))) or
               (r[0] == 'sub' and st_sub(k, r[1]) == r) or R.some('ghost', k, r) for r in res)


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


def tab_of(k, x):
    """`CoreMode.tabOf`: `x` loaded at offset `0` through a top-level product `T·J`, `J` range checked below `g^N`:
    `(T, J, N)`."""
    atoms = top_atoms(I.CORE[k][1])
    p = next((a[2] for a in atoms if a[0] == 'load' and a[1] == x and a[3] == 0), None)
    tj = next((a[2:4] for a in atoms if a[0] == 'mul' and a[1] == p), None) if p is not None else None
    N = rc_bound(atoms, tj[1]) if tj is not None else None
    return None if N is None else (tj[0], tj[1], N)


def tab_k(k, T, t):
    """`CoreMode.tabK`: the exponent of the top-level constant a top-level `load` stores at `T·g^t`."""
    atoms = top_atoms(I.CORE[k][1])
    c = next((a[1] for a in atoms if a[0] == 'load' and a[2] == T and a[3] == t), None)
    w = next((a[2] for a in atoms if a[0] == 'const' and a[1] == c), None) if c is not None else None
    return pow_of(w)


def tab_ev(ev, i):
    """`CoreMode.tabEv`: an index's exponent, each value's by `ev`."""
    if i[0] == 'num':
        return i[1]
    if i[0] == 'val':
        return ev(i[1])
    acc = i[1][1]
    for b, e in i[1][0]:
        x = ev(b)
        if x is None:
            return None
        acc += e * x
    return acc


def tab_row_ev(k, J, t):
    """`CoreMode.tabRowEv`: the index `J`'s exponent `t`, a table read over `J` its table's row `t` entry."""
    def ev(v):
        if v == J:
            return t
        tab = tab_of(k, v)
        if tab is None or tab[1] != J:
            return None
        return tab_k(k, tab[0], t)
    return ev


def ivals(i):
    return [] if i[0] == 'num' else [i[1]] if i[0] == 'val' else [b for b, _ in i[1][0]]


def rc_tab(k, r):
    """`CoreMode.rcTab`: an order over table reads of one index, the index and constants, at every row of the first
    read's table."""
    if r[0] == 'under':
        return rc_tab(k, r[2])
    if r[0] != 'lt':
        return False
    for x in ivals(r[1]) + ivals(r[2]):
        tab = tab_of(k, x)
        if tab is None:
            continue
        _, J, N = tab

        def row(t):
            ev = tab_row_ev(k, J, t)
            u, v = tab_ev(ev, r[1]), tab_ev(ev, r[2])
            return u is not None and v is not None and u < v < CAPE
        if all(row(t) for t in range(N)):
            return True
    return False


def fn_facts(EM):
    """The solver's exponent facts also from the functions' own families (their rule files' `fact`), and the residuals
    it may state there (`res_filter`)."""
    base = EM.Solver.fact
    hooks = [h(EM, base) for h in R.hooks('fact')]
    filters = R.hooks('res_filter')
    EM.RES_FILTER[0] = lambda k, r: all(f(k, r) for f in filters)

    def fact(self, st, a, b):
        f = base(self, st, a, b)
        if f is not None:
            return f
        for h in hooks:
            f = h(self, st, a, b)
            if f is not None:
                return f
        return None
    return base, fact


def cs_reads(EM):
    """The solver's read witnesses also from the families of reads: a cell of a run in scope by a residual `sub c R`
    of the stream-cursor loops' (`st_sub`) or of the function's own (its rule file's `sub`: `column_selector`'s lowest
    digit, the ghost families, the stream's cursors)."""
    base = EM.Solver.pt

    def pt(self, st, c, want=None, depth=0):
        w = base(self, st, c, want, depth)
        if w is not None or want is not None:
            return w
        r = R.first('sub', self.k, c) or st_sub(self.k, c)
        if r is None or c != r[1]:
            return None
        R2 = EM.C.runF(st.env, r[2])
        for n, R3 in sorted(st.rs.items()):
            if R3 == R2:
                return ('run', n, [self.use(('rd', r), r)])
        return None
    return base, pt


# ---- values a body pins to powers of `g` (`CoreMode.valExpB`), carried down to callees (`CoreMode.carryExpB`)

def spine_atoms(ss):
    """`Memory.spineE`'s atoms: the top-level atoms up to the first statement that may return."""
    out = []
    for s in ss:
        if s[0] == 'a':
            out.append(s[1])
        elif s[0] in ('call', 'callIf', 'dispatch'):
            continue
        elif s[0] in ('ite', 'match') and heapc.noret(s):
            continue
        else:
            break
    return out


def pow1(c):
    """`Res.powOf1`: the exponent of a constant word `g^e`, `1` at `0`."""
    if c is None or c[1] != 0:
        return None
    return 0 if c[0] == 1 else I.POWS.get(c[0])


def const_exp(v, lo, hi, sp):
    """`CoreMode.constExpS`."""
    return any(a[0] == 'const' and a[1] == v and pow1(a[2]) is not None and lo <= pow1(a[2]) < hi for a in sp)


def copy_exp(v, lo, hi, sp):
    """`CoreMode.copyExpS`."""
    return any(a[0] == 'copy' and a[1] == v and const_exp(a[2], lo, hi, sp) for a in sp)


def arm_exp(v, lo, hi, ss):
    """`CoreMode.armExpB`."""
    for s in ss:
        if s[0] == 'match' and s[2] and all(copy_exp(v, lo, hi, spine_atoms(a)) for a in s[2]):
            return True
        if not heapc.noret(s):
            return False
    return False


def val_exp(body, v, lo, hi):
    """`CoreMode.valExpB`: `v` is `g^e`, `lo <= e < hi`, on every returning path of `body`."""
    return const_exp(v, lo, hi, spine_atoms(body)) or arm_exp(v, lo, hi, body)


def carry_misses(L):
    """`CoreMode.carryExpB` over the whole program: the call sites of a listed `(callee, parameter, lo, hi)` whose argument
    its caller does not pin so."""
    out = []
    for k, (params, body) in sorted(I.CORE.items()):
        for s in I.stmts(body):
            sites = [(s[1], s[2])] if s[0] == 'call' else [(s[2], s[3])] if s[0] == 'callIf' else \
                [(f, s[3]) for f in s[2]] if s[0] == 'dispatch' else []
            for f, args in sites:
                for g, p, lo, hi in L:
                    if g == f and not (p < len(args) and val_exp(body, args[p], lo, hi)):
                        out.append((k, f, p))
    return out


def straight(body):
    return all(s[0] in ('a', 'ret') for s in body) and sum(1 for s in body if s[0] == 'ret') == 1 and \
        body[-1][0] == 'ret'


def leaf_candidates():
    """Straight-line bodies the check without calls leaves uncovered, or whose mode signature guarantees
    pointer runs (`postP`), which that check does not state."""
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
    _, EM.Solver.fact = fn_facts(EM)
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
        callc.fa_past_all(cands)
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

