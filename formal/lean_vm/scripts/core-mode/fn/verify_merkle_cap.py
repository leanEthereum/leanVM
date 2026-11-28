"""`verify_merkle_cap`'s contracts (`sigc.py`): `verify_merkle_cap__L{d}(cap, flags)` reads `cap[g^k]`, `2 <= k < 4·2^d`,
and `flags[g^k]`, `2 <= k < 2^d`, the cap and flags its caller hints."""
from sigseed import sig, cell, num, run


def par(i, lo, hi):
    """Parameter `i`'s cells `[p]·g^k`, `lo <= k < hi`."""
    return run(cell(0, [(2 + i, 1)]), num(lo), num(hi), 1, 0)


def contract(d):
    rs = [par(0, 2, 4 * 2 ** d), par(1, 2, 2 ** d)]
    return sig(range(4), None, [4, 5], preR=rs, postR=rs)


# the cap depths a configuration reaches (the bus era's contract of depth `8` read its cap from `g^4`)
CONTRACTS = {'verify_merkle_cap__L%d' % d: contract(d) for d in range(2, 9)}

OWN = []
