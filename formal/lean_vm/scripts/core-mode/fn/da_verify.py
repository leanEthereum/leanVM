"""`da_verify`'s rules."""
import fnrules

# runs made up for its reads and its callees' runs (`der`)
FEATURES = {'da_verify': [{'der'}]}

CAPE = 2 ** 62


def sel_bound(k, x):
    """`CoreMode.daGap`: its blob count `n_blob_g`, at most `g^DA_MAX_ROWS`, and gap `gap_g`, below it
    (`EndExec.daV_inst`)."""
    import infer as I
    nb, gap = fnrules.val('da_verify', 'n_blob_g'), fnrules.val('da_verify', 'gap_g')
    if I.callee(k) == 'da_verify' and x in (nb, gap):
        return fnrules.guest_const('DA_MAX_ROWS') + (1 if x == nb else 0)
    return None


def fam(k, r):
    """`CoreMode.daGap`: a residual `e(x) < m`, `sel_bound(k, x) <= m`, under branch conditions."""
    if r[0] == 'under':
        return fam(k, r[2])
    if not (r[0] == 'lt' and r[1][0] == 'val' and r[2][0] == 'num'):
        return False
    B = sel_bound(k, r[1][1])
    return B is not None and B <= r[2][1] < CAPE


# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
