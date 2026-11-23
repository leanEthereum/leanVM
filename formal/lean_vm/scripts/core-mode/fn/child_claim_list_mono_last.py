"""`child_claim_list_mono_last`'s rules: the ghost family `ml`."""
import re
from fnrules import I, lean_def

# its reads' shape (`CoreMode.mlSub`) and its links (`CoreMode.mlGl`), as its Lean data says: entry, first gap, the
# gaps' stride, the bound parameter, the caller's cells linked `(d, slot, k)`
ENT, GAP, STRIDE, LIMIT, GL = lean_def('child_claim_list_mono_last', 'Data', 'mlShape')


def ml_k(k):
    """`CoreMode.mlK`: `k` for `child_claim_list_mono_last__L{k}`, `1 ≤ k < 17`."""
    m = re.fullmatch(r'child_claim_list_mono_last__L(\d+)', k)
    return int(m.group(1)) if m and 1 <= int(m.group(1)) < 17 else None


def sub(k, c):
    """`CoreMode.mlSub`: its read of claim `jj`'s entry `c`, the run of its caller's table (its ghost, stride 4, below
    the exponent of its parameter `limit`), or None."""
    kk = ml_k(k)
    bs, off = c
    jj = off // 4
    if kk is None or jj >= kk or tuple(bs) != ((ENT, 1),) + tuple((GAP + STRIDE * i, 4) for i in range(jj + 1)):
        return None
    return ('sub', c, ((((I.GB, 1),), off % 4), 4, ('num', 0), ('val', LIMIT)))


def ghost(k, r):
    return r[0] == 'sub' and sub(k, r[1]) == r


def gl(k, np):
    """`CFun.gl` (`CoreMode.mlGl`): its caller's cells linked, `{d: (slot, k)}`, or None."""
    return {d: (b, c) for d, b, c in GL} if ml_k(k) is not None else None

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
