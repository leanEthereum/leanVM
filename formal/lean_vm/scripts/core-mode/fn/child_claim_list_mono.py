"""`child_claim_list_mono`'s rules: its frame loops (`CoreMode.cmK`), their claims a frame."""
from fnrules import I

CM_LOOPS = {'child_claim_list_mono_loop0': 136, 'child_claim_list_mono_loop1': 17}


def sub(k, c):
    """`CoreMode.cmSub`: a frame loop's read of claim `jj`'s entry `c`, the run of its caller's table (ghost `0`,
    stride 4, below the exponent of ghost `1`, its caller's `limit`), or None."""
    m = CM_LOOPS.get(I.callee(k))
    if m is None:
        return None
    bs, off = c
    jj = off // 4
    if jj >= m or tuple(bs) != ((12, 1),) + tuple((13 + 10 * i, 4) for i in range(jj + 1)):
        return None
    return ('sub', c, ((((I.GB, 1),), off % 4), 4, ('num', 0), ('val', I.GB + 1)))


def ghost(k, r):
    """`CoreMode.cmSub`: a read (`sub`), or ghost `1`'s exponent `0 < e(limit)`."""
    if I.callee(k) not in CM_LOOPS:
        return False
    return (r[0] == 'sub' and sub(k, r[1]) == r) or r == ('lt', ('num', 0), ('val', I.GB + 1))

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResM.lean',
    'LeanVM/Guest/CoreMode/Fam/ResMR.lean',
    'LeanVM/Guest/CoreMode/Fam/MonoReplay.lean',
    'LeanVM/Guest/CoreMode/Fam/MonoChain.lean',
    'LeanVM/Guest/CoreMode/Fam/MonoDefs.lean',
    'LeanVM/Guest/EndExecCoreMono.lean',
    'LeanVM/Guest/CoreMode/Fn/child_claim_list_mono/*.lean',
]
