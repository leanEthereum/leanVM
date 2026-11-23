"""`da_pad`'s rules."""
import fnrules

CAPE = 2 ** 62


def sel_bound(k, x):
    """`CoreMode.daGap`: its gap, its parameter `gap_g`, below `g^DA_MAX_ROWS` (`EndExec.DaPadQ`)."""
    import infer as I
    if I.callee(k) == 'da_pad' and x == fnrules.val('da_pad', 'gap_g'):
        return fnrules.guest_const('DA_MAX_ROWS')
    return None


def fam(k, r):
    """`CoreMode.daGap`: a residual `e(x) < m`, `sel_bound(k, x) <= m`, under branch conditions."""
    if r[0] == 'under':
        return fam(k, r[2])
    if not (r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num'):
        return False
    B = sel_bound(k, r[1][1])
    return B is not None and B <= r[2][1] < CAPE


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family (`da_verify`'s); its frame weight in `MvCountData`
COUNT_SHAPE = {'da_pad': 'V'}
COUNT_OM = {'da_pad': ('MvCountData', 1)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
