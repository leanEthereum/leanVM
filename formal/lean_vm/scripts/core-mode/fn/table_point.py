"""`table_point`'s contracts (`sigc.py`): `table_point__L{h}(theta, tau, chi, bits)` reads `tau[g^k]`, `chi[g^k]`, `k < h`,
and `bits[g^k]`, `k ≤ h`."""
from sigseed import sig, cell, num, run

# specialized on `h`
NS = range(0, 64)


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(6), None, [6, 7, 8], preR=[par(1, n), par(2, n), par(3, n + 1)], postR=[])


CONTRACTS = {'table_point__L%d' % n: contract(n) for n in NS}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
