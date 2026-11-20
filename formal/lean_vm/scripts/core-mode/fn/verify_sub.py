"""`verify_sub`'s rules: its exponent family (`CoreMode.vsExp`, `EndExec.VsQ`)."""

CAPE = 2 ** 62

# its values' exponent bounds, the products naming one, the orders `e(x) <= e(y) + c`, the cursors in its stream
# `[25]·[0, 8192)` with room for `207` words (`CoreMode.vsPows`, `vsMuls`, `vsLes`, `vsCurs`)
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

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResVs.lean',
    'LeanVM/Guest/CoreMode/Fn/verify_sub/*.lean',
]
