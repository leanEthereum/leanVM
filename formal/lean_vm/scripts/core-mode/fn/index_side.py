"""`index_side`'s contracts (`sigc.py`): `index_side__L{w}(r, zeta, below)` reads `r[g^k]`, `zeta[g^k]`, `k < w`, and leaves
`below[g^k]`, `k ≤ w`, written."""
from sigseed import sig, cell, num, run

# specialized on `w`
NS = range(0, 64)


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(5), None, [5, 6, 7], preR=[par(0, n), par(1, n)], postR=[par(2, n + 1)])


CONTRACTS = {'index_side__L%d' % n: contract(n) for n in NS}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
