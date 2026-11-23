"""`verify_tables`' rules: its features, exponent and stream facts, its exponent family (`CoreMode.vtExp`,
`EndExec.vtExp_inst`), mirrored, and its buffers through its hinted order (`CoreMode.vtPerm`).

Its exponent family:

At an honest instance of `verify_tables` the exponents of its words are linear forms over nine slacks `s` (`a = mu - 19`,
`b = mu - n`, `c_t = n - tau_t`, `d = mu - lm`), each in a box `[0, ub]` (`EndExec.vt_exps`): `g_bus_mu`
`19 + a`, `g_zc_n` `19 + a - b`, `dims_g[1 + t]` (its copy `kb[2 + t]`, ghost `GB + 1 + t`) `19 + a - b - c_t`,
`dims_g[0]` (`kb[1]`, ghost `GB`) `19 + a - d`. A word the top-level atoms make of such words has the form they give
(`vtF`): a constant `g^k`, a product, a copy, or a quotient (`a = x·b`) whose form is nonnegative on the box. A residual
holds when, after each arm condition `x = g^j` is added as an equation (a multiple of `F_x - j` subtracted), the forms
it needs nonnegative are on the whole box: `lt a b` (`F_b - F_a - 1`), `subR q r` (stride 1, `q`'s base `r`'s times a
product `m`: `r`'s bounds hold `F_m + q.off - r.off + q`'s), under branch conditions (the arms used, the others
dropped)."""
import fnrules
from fnrules import I, val, lean_def


# its arms' growing blocks, its buffers through its hinted order (`perm`), a run up to a bound over values before one up
# to a constant (`vthi`), the bounds its exponent family proves stated (`lastres`)
FEATURES = {'verify_tables': [{'armblock', 'perm', 'vthi', 'lastres'}]}

# `g_bus_mu`'s exponent below `33`, `dims_g[0]`'s too and `dims_g[1..6]`'s below `31` (`Res.expFacts`, `EndExec.VtPQ`), as
# its Lean data says
EXP_FACTS = lean_def('verify_tables', 'Data', 'expFacts')

# its value `g_zc_n = g^n`, `n < 34` (`CoreMode.expVals`, `EndExec.VtQ`), as its Lean data says
VT_ZC = val('verify_tables', 'g_zc_n')
EXP_VALS = lean_def('verify_tables', 'Data', 'expVals')

# its rounds loop reads the proof stream past its cursor (`CoreMode.stLoops`), as its Lean data says
ST_LOOPS = {e[0]: e[1:] for e in lean_def('verify_tables', 'Data', 'stLoops')}

# its last table sumcheck record's cursor and its stream parameter (`CoreMode.vtStC`)
VT_ST, VT_STREAM = val('verify_tables', 'cursor@5'), val('verify_tables', 'stream')


def vt_st_sub(k, c):
    """`CoreMode.vtStC`: a read `c` words past its table sumcheck's last cursor, `c < 153`, one of its stream's
    `[stream]·[0, 8192)`."""
    if k == 'verify_tables' and c[0] == ((VT_ST, 1),) and c[1] < 153:
        return ('sub', c, ((((VT_STREAM, 1),), 0), 1, ('num', 0), ('num', 8192)))
    return None


def sub(k, c):
    return vt_st_sub(k, c)


def fam(k, r):
    """`CoreMode.vtStC`, `CoreMode.vtPerm`."""
    return (r[0] == 'sub' and vt_st_sub(k, r[1]) == r) or vt_perm(k, r)


def ghost(k, r):
    """`CoreMode.vtExp`."""
    return vt_exp(k, r)


def res_filter(k, r):
    """With `lastres`, the residuals the solver states are of its families."""
    return k != 'verify_tables' or 'lastres' not in I.F or vt_exp(k, r) or vt_perm(k, r) or \
        (r[0] == 'sub' and vt_st_sub(k, r[1]) == r)


def fact(EM, base):
    """The solver's exponent facts also from its exponent family: `e(a) < e(b)` stated under the site's path when the
    family proves it there."""
    def f(self, st, a, b):
        if self.k != 'verify_tables':
            return None
        g = tuple(dict.fromkeys(self.X.path))
        r = ('lt', self.idx(st, a), self.idx(st, b))
        wr = ('under', g, r) if g else r
        if not vt_exp(self.k, wr):
            return None
        return [self.use(('vtexp', a, b, g), wr)]
    return f

NS = 9                       # slacks: a, b, c0..c5, d
UB = (13, 32) + (32,) * 6 + (32,)
CAPE = 2 ** 62
FUEL = 4


def lin(c, **kw):
    v = [0] * NS
    for k, x in kw.items():
        v[{'a': 0, 'b': 1, 'd': 8}[k] if k in ('a', 'b', 'd') else 2 + int(k[1:])] = x
    return (c, tuple(v))


def add(f, g, k=1):
    return (f[0] + k * g[0], tuple(x + k * y for x, y in zip(f[1], g[1])))


def minv(f):
    return f[0] + sum(min(0, x * u) for x, u in zip(f[1], UB))


def maxv(f):
    return f[0] + sum(max(0, x * u) for x, u in zip(f[1], UB))


# `g_bus_mu`, and `dims_g`'s words' copies `kb[1 + j]`, `j < 7` (consecutive values)
VT_MU, VT_KB = val('verify_tables', 'g_bus_mu'), val('verify_tables', 'kb[1]')


def base(x):
    """`CoreMode.vtBaseN`: the words of the slacks."""
    GB = I.GB
    if x >= GB:
        x = x - GB + VT_KB if x - GB < 7 else None
        if x is None:
            return None
    if x == VT_MU:
        return lin(19, a=1)
    if x == VT_ZC:
        return lin(19, a=1, b=-1)
    if x == VT_KB:
        return lin(19, a=1, d=-1)
    if VT_KB + 1 <= x < VT_KB + 7:
        return lin(19, a=1, b=-1, **{'c%d' % (x - VT_KB - 1): -1})
    return None


def pow1(w):
    """`Res.powOf1`."""
    w = tuple(w)
    if w == (1, 0):
        return 0
    return I.POWS.get(w[0]) if w[1] == 0 else None


_FC = {}


def form(atoms, fuel, x):
    """`CoreMode.vtF` (memoized per atom list)."""
    key = (id(atoms), fuel, x)
    if key not in _FC:
        _FC[key] = form0(atoms, fuel, x)
    return _FC[key]


def form0(atoms, fuel, x):
    if fuel == 0:
        return None
    b = base(x)
    if b is not None:
        return b
    for a in atoms:
        r = None
        if a[0] == 'const' and a[1] == x:
            k = pow1(a[2])
            r = None if k is None else (k, (0,) * NS)
        elif a[0] == 'copy' and a[1] == x:
            r = form(atoms, fuel - 1, a[2])
        elif a[0] == 'mul' and a[1] == x:
            p, q = form(atoms, fuel - 1, a[2]), form(atoms, fuel - 1, a[3])
            r = add(p, q) if p is not None and q is not None else None
        elif a[0] == 'mul' and (a[2] == x or a[3] == x):
            o = a[3] if a[2] == x else a[2]
            p, q = form(atoms, fuel - 1, a[1]), form(atoms, fuel - 1, o)
            if p is not None and q is not None:
                d = add(p, q, -1)
                r = d if minv(d) >= 0 else None
        if r is not None:
            return r
    return None


def mono(atoms, c):
    """`CoreMode.vtM`: a cell's form, `None` if a base has none."""
    f = (c[1], (0,) * NS)
    for b, e in c[0]:
        g = form(atoms, FUEL, b)
        if g is None:
            return None
        f = add(f, g, e)
    return f


def idx(atoms, i):
    if i[0] == 'num':
        return (i[1], (0,) * NS)
    if i[0] == 'val':
        return mono(atoms, (((i[1], 1),), 0))
    return mono(atoms, i[1])


def apply_arms(atoms, arms, f):
    """`CoreMode.vtArms`: each arm `x = g^j` with a form `F` whose first nonzero slack coefficient is `±1` (in slack
    order) removes that slack from `f` (`f - c·(F - j)`)."""
    for x, j in arms:
        F = form(atoms, FUEL, x)
        if F is None or not (j < CAPE and maxv(F) < CAPE):
            continue
        i = next((k for k in range(NS) if F[1][k] != 0), None)
        if i is None or F[1][i] not in (1, -1):
            continue
        k = f[1][i] * F[1][i]
        f = add(f, add(F, (j, (0,) * NS), -1), -k)
    return f


NNB = lean_def('verify_tables', 'Fam', 'vtNNB')


def nonneg(atoms, arms, f):
    """`CoreMode.vtNN`: on the box, or less a slacks' word's form (nonnegative) on it."""
    f2 = apply_arms(atoms, arms, f)
    return minv(f2) >= 0 or any(minv(add(f2, base(x), -1)) >= 0 for x in NNB)


def lt(atoms, arms, a, b):
    """`CoreMode.vtLt`."""
    A, B = idx(atoms, a), idx(atoms, b)
    return small(A) and small(B) and nonneg(atoms, arms, add(add(B, A, -1), (-1, (0,) * NS)))


def small(f):
    return f is not None and maxv(f) < CAPE


def holds(atoms, arms, r):
    """`CoreMode.vtExpR`."""
    if r[0] == 'lt':
        return lt(atoms, arms, r[1], r[2])
    if r[0] == 'subP':
        # `[B]·[J]·g^o` one of `[B]·g^(o + t)`, `t < |cs|`, by `e(J) < |cs|` (`vtSubP`), either base the index
        c, cs = r[1], {(tuple(tuple(b) for b in x[0]), x[1]) for x in r[2]}
        bs = tuple(tuple(b) for b in c[0])
        if len(bs) != 2 or bs[0][1] != 1 or bs[1][1] != 1:
            return False
        n = len(r[2])
        return any(all((((B, 1),), c[1] + t) in cs for t in range(n)) and lt(atoms, arms, ('val', J), ('num', n))
                   for B, J in ((bs[0][0], bs[1][0]), (bs[1][0], bs[0][0])))
    if r[0] == 'subR':
        q, R = r[1], r[2]
        if q[1] != 1 or R[1] != 1 or len(q[0][0]) < len(R[0][0]) or tuple(q[0][0][:len(R[0][0])]) != tuple(R[0][0]):
            return False
        m = mono(atoms, (tuple(q[0][0][len(R[0][0]):]), q[0][1] - R[0][1]))
        ql, qh, rl, rh = idx(atoms, q[2]), idx(atoms, q[3]), idx(atoms, R[2]), idx(atoms, R[3])
        if m is None or not all(small(x) for x in (ql, qh, rl, rh)) or not small(m):
            return False
        return nonneg(atoms, arms, add(add(m, ql), rl, -1)) and nonneg(atoms, arms, add(rh, add(m, qh), -1))
    if r[0] == 'under':
        arms = list(arms) + [(c[1], c[2]) for c in r[1] if c[0] == 'arm']
        return holds(atoms, arms, r[2])
    return False


_AT = {}
# the top-level atoms of `verify_tables` the family reads (`CoreMode.vtAtoms`, `EndExec.vtAtoms_top`)
ATOMS = lean_def('verify_tables', 'Fam', 'vtAtoms')


def vt_exp(k, r):
    """`CoreMode.vtExp` (the ghost slots `verify_tables`' own words `dims_g[j]`, `vtGw`, checked in Lean)."""
    if k != 'verify_tables':
        return False
    if k not in _AT:
        import callcres
        _AT[k] = ATOMS if ATOMS is not None else callcres.top_atoms(I.CORE[k][1])
    try:
        key = hash(r), r
        if key not in _HC:
            _HC[key] = holds(_AT[k], [], r)
        return _HC[key]
    except TypeError:
        return holds(_AT[k], [], r)


_HC = {}


def rv(v0, r):
    """`CoreMode.vtRvC`."""
    return v0 if r == 0 else v0 + 13 + 20 * (r - 1)


SIDES = [([rv(val('verify_tables', 'gi@1'), r) for r in range(9)], 0, 9),
         ([rv(val('verify_tables', 'gi@10'), r) for r in range(6)], 18, 24)]


def vt_perm(k, r):
    """`CoreMode.vtPerm`."""
    if k != 'verify_tables' or r[0] != 'subP':
        return False
    c, cs = r[1], set(tuple(x) for x in r[2])
    cs = {(tuple(tuple(b) for b in x[0]), x[1]) for x in cs}
    for vs, lo, hi in SIDES:
        bs = tuple(tuple(b) for b in c[0])
        if len(bs) == 2 and bs[0][1] == 1 and bs[1][1] == 1:
            B, v = bs[0][0], bs[1][0]
            if c[1] == 0 and v in vs and all((((B, 1),), e) in cs for e in range(lo, hi)):
                return True
        elif len(bs) == 1 and bs[0][1] == 1:
            B = bs[0][0]
            if lo <= c[1] < hi and all((((B, 1), (v, 1)), 0) in cs for v in vs):
                return True
    return False


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `W` family (`kcVtW`)
COUNT_SHAPE = {'verify_tables': 'W'}


def count_walk(C, k, n):
    """Its instructions (`B1.VerifySub.vtWB` at `Count.vsWords`): its body, its rounds or copy loop `32` times."""
    import vscount
    if n != vscount.L('verify_tables'):
        return None
    lps = (vscount.L('verify_tables_loop0'), vscount.Lopt('verify_tables_loop1'))

    def call_if(f):
        assert f in lps, f
        return 32 * C.loop(k, f)
    return C.walk(k, n, call_if)


def count_words_by_name(g):
    """`vtPairs` (`Count/Words.lean`): its callees, directly or not, but those `Count/VsWords` bounds apart."""
    import vscount, ratio
    L, Lopt = vscount.L, vscount.Lopt
    VT_APART = [f for f in [L('verify_tables_loop0'), Lopt('verify_tables_loop1'), L('shared_selector_tables_loop0'),
                            L('shared_selector_tables')] if f]
    n = L('verify_tables')
    vt = sorted(g.closure([n]) - {n} - set(VT_APART))
    return ('/-- `verify_tables`\' callees, directly or not, with their core indices, but those\n'
            '`Count/VsWords` bounds apart (`VT_APART`). -/\n'
            + ratio.wrap('def vtPairs : List (String × ℕ) := [', ['("%s", %d)' % (m, g.by[m]) for m in vt]) + '\n')


def count_parts(g, OPS):
    """`VsCountData`'s `kcVtW`."""
    import vscount
    C = vscount.cnt(g, 'V')
    return [dict(mod='VsCountData', key=3, tables=[vscount.opdef(
        OPS, 'kcVtW', '`verify_tables`\' instructions (`B1.VerifySub.vtWB Count.vsWords`).',
        lambda k: C.weight(k, vscount.L('verify_tables')))])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/B1/Tables/VtWords*.lean',
    'LeanVM/Guest/Count/Fn/verify_tables.lean',
    'LeanVM/Guest/B1/Tables/Vt/**',
    'LeanVM/Guest/B1/Tables/VtC/**',
    'LeanVM/Guest/B1/Tables/Kids/**',
    'LeanVM/Guest/B1/Exact/VerifyTables.lean',
    'LeanVM/Guest/B1/Exact/VtOwn.lean',
]
