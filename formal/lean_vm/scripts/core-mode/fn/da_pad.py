"""`da_pad`'s rules."""
import fnrules

CAPE = 2 ** 62


def sel_bound(k, x):
    """`CoreMode.daGap`: its gap, its parameter `2`, below `g^DA_MAX_ROWS` (`EndExec.DaPadQ`)."""
    import infer as I
    if I.callee(k) == 'da_pad' and x == 2:
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

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/EndExecCoreDa.lean',
    'LeanVM/Guest/CoreMode/Fn/da_pad/*.lean',
]
