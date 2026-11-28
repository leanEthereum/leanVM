"""`one_plus_suffixes`'s contracts (`sigc.py`): `one_plus_suffixes__L{n}(chain, a)` reads `a[g^k]`, `k < n`, and leaves
`chain[g^k]`, `k ≤ n`, written."""
from sigseed import sig, cell, num, run

# specialized on `n`
NS = range(0, 64)


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(4), None, [4], preR=[par(1, n)], postR=[par(0, n + 1)])


CONTRACTS = {'one_plus_suffixes__L%d' % n: contract(n) for n in NS}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
