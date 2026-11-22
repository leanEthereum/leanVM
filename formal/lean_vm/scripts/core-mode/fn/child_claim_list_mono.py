"""`child_claim_list_mono`'s rules: its frame loops (`CoreMode.cmK`), their claims a frame."""
from fnrules import I, lean_def

# its frame loops (`CoreMode.cmK`), as its Lean data says: their claims a frame, entry, first gap, the gaps' stride and
# the caller's cells linked (`CoreMode.cmGl`)
CM_LOOPS = {e[0]: e[1:] for e in lean_def('child_claim_list_mono', 'Data', 'cmLoops')}


def sub(k, c):
    """`CoreMode.cmSub`: a frame loop's read of claim `jj`'s entry `c`, the run of its caller's table (ghost `0`,
    stride 4, below the exponent of ghost `1`, its caller's `limit`), or None."""
    e = CM_LOOPS.get(I.callee(k))
    if e is None:
        return None
    m, ent, gap, stride, _ = e
    bs, off = c
    jj = off // 4
    if jj >= m or tuple(bs) != ((ent, 1),) + tuple((gap + stride * i, 4) for i in range(jj + 1)):
        return None
    return ('sub', c, ((((I.GB, 1),), off % 4), 4, ('num', 0), ('val', I.GB + 1)))


def ghost(k, r):
    """`CoreMode.cmSub`: a read (`sub`), or ghost `1`'s exponent `0 < e(limit)`."""
    if I.callee(k) not in CM_LOOPS:
        return False
    return (r[0] == 'sub' and sub(k, r[1]) == r) or r == ('lt', ('num', 0), ('val', I.GB + 1))


def gl(k, np):
    """`CFun.gl` (`CoreMode.cmGl`, `loopGl`): its caller's cells its first ghost slots, the caller's frame address the
    next, `{d: (slot, 0)}`, or None."""
    e = CM_LOOPS.get(I.callee(k))
    if e is None:
        return None
    g = {d: (np + j, 0) for j, d in enumerate(e[4])}
    g[0] = (np + len(e[4]), 0)
    return g


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family (`child_claim_list_digest`'s); its frame weight in `VsCountData`
COUNT_SHAPE = {'child_claim_list_mono': 'V'}
COUNT_OM = {'child_claim_list_mono': ('VsCountData', 4)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/MonoChain.lean',
]
