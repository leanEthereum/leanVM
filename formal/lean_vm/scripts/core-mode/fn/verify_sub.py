"""`verify_sub`'s rules: its exponent family (`CoreMode.vsExp`, `EndExec.VsQ`)."""
from fnrules import val, lean_def

CAPE = 2 ** 62

# its values' exponent bounds, the products naming one, the orders `e(x) <= e(y) + c`, the cursors in its stream
# with room for `207` words (`CoreMode.vsPows`, `vsMuls`, `vsLes`, `vsCurs`), as its Lean data says
VS_POWS = {v: (lo, hi) for v, lo, hi in lean_def('verify_sub', 'Fam', 'vsPows')}
VS_MULS = {ab: x for ab, x in lean_def('verify_sub', 'Fam', 'vsMuls')}
VS_LES = lean_def('verify_sub', 'Fam', 'vsLes')
VS_CURS = lean_def('verify_sub', 'Fam', 'vsCurs')
VS_STREAM, VS_ROOM = val('verify_sub', 'stream'), 207


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


def fam(k, r):
    """`CoreMode.vsExp`: a residual of its exponent family."""
    if k != 'verify_sub':
        return False
    if r[0] == 'under':
        return fam(k, r[2])
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


def exp_bound(k, x):
    """Its exponent bound of `x` (`vsExp`), plus one."""
    return VS_POWS[x][1] + 1 if k == 'verify_sub' and x in VS_POWS else None


arg_bound_mono = exp_bound

_SIGS = {}


def res_filter(k, r):
    """The residuals the solver states at it are of a family (the pool's facts the solver may use there)."""
    if k != 'verify_sub':
        return True
    import callcres
    if not _SIGS:
        import route
        _SIGS.update(route.sigs())
    return callcres.res_ok(k, [r], _SIGS)


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family; its frame weight in `VsCountData`: module, order
COUNT_SHAPE = {'verify_sub': 'V'}
COUNT_OM = {'verify_sub': ('VsCountData', 0)}


def vs_st(g):
    """Its statically bounded callees but its opening arm: its static calls, then the arms of its other dispatches
    (`squeeze_point_from`'s by the stack log, `bus_grind_check`'s by the grinding bits), each once, in order; not the
    callees counted otherwise (ratio-bounded or by their trees' shapes, `vscount`)."""
    import vscount
    skip = set(vscount.shaped()) | set(vscount.ratio_words())
    osN = g.os_names()
    calls, arms = [], []
    for st in g.fns[g.by[vscount.L('verify_sub')]]['body']:
        if st[0] == 'call' and st[1] not in skip and st[1] not in calls:
            calls.append(st[1])
        elif st[0] == 'dispatch' and st[2] != osN:
            arms += [f for f in st[2] if f not in arms]
    return calls + arms


def vs_counts(C, k):
    """Its instructions at each opening arm, at the opcode index `k`, from the `V` counts."""
    import vscount
    n, osN = vscount.L('verify_sub'), C.g.os_names()
    return [C.walk(k, n, dispatch=lambda fs: C.stat(k, osN[c]) if fs == osN else None) for c in range(len(osN))]


def count_parts(g, OPS):
    """`VsCountData`'s tables of its callees and its counts at each opening arm."""
    import vscount
    C, lst, opdefl = vscount.cnt(g, 'V'), vscount.lst, vscount.opdefl
    osN, VS_ST = g.os_names(), vs_st(g)
    A = len(osN)
    rw = vscount.ratio_words()
    rb = [rw[st[1]] for st in g.fns[g.by[vscount.L('verify_sub')]]['body'] if st[0] == 'call' and st[1] in rw]
    assert len(rb) == 2, rb
    T = [vs_counts(C, k) for k in range(6)]

    def out():
        for c in range(A): print('vscount: arm %d: %s' % (c, [T[k][c] for k in range(6)]))
    return [
        dict(mod='VsCountData', key=0,
             names=['/-- The core indices of `open_stacked__L{c}`, `c < %d`. -/\ndef osJ : List ℕ := %s\n'
                    % (A, lst(g.by[n] for n in osN)),
                    '/-- `verify_sub`\'s statically bounded callees but its opening arm. -/\ndef vsStNames : List String := [%s]\n'
                    % ', '.join('"%s"' % n for n in VS_ST),
                    '/-- Their core indices. -/\ndef vsStJ : List ℕ := %s\n' % lst(g.by[n] for n in VS_ST)],
             tables=[opdefl(OPS, 'kcOsT', '`open_stacked__L{c}`\'s instructions, by `c`.', lambda k: [C.stat(k, n) for n in osN]),
                     opdefl(OPS, 'kcVsStT', 'The instructions of `vsStNames`.', lambda k: [C.stat(k, n) for n in VS_ST])],
             check=['  (List.range %d).all (fun c => kvOkB op (osJ.getD c 0) ("open_stacked__L" ++ B1.Whir.natStr c) &&\n'
                    '    kvSBJ op (osJ.getD c 0) == (kcOsT op).getD c 0)' % A,
                    '  (List.range %d).all (fun i => kvOkB op (vsStJ.getD i 0) (vsStNames.getD i "") &&\n'
                    '    kvSBJ op (vsStJ.getD i 0) == (kcVsStT op).getD i 0)' % len(VS_ST)]),
        dict(mod='VsCountData', key=5, out=out,
             tables=[opdefl(OPS, 'vsCountT', '`verify_sub`\'s instructions at the arm `c`, its two ratio-bounded callees '
                            'within `%d`, `%d` words.' % tuple(rb), lambda k: T[k])])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/Budget/VsCount.lean',
    'LeanVM/Guest/Count/VsBound.lean',
    'LeanVM/Guest/Count/VsWords.lean',
    'LeanVM/Guest/Count/VsWB.lean',
]
