"""`state_ends`'s contracts (`sigc.py`): `state_ends__L{w}(zeta, cbits)` reads `zeta[g^k]`, `cbits[g^k]`, `k < w`."""
from sigseed import sig, cell, num, run

# specialized on `w`
NS = range(0, 64)


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(4), None, [4, 5], preR=[par(0, n), par(1, n)], postR=[])


CONTRACTS = {'state_ends__L%d' % n: contract(n) for n in NS}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
