"""`ring_cols`'s contracts (`sigc.py`): `ring_cols__L{n}(row, scl, msk)` reads `row[g^k]`, `k < BASE_FIELD_BITS`, and
`scl[g^q]`, `msk[g^q]`, `q < n`."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

B = guest_const('BASE_FIELD_BITS')


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(5), None, [5], preR=[par(0, B), par(1, n), par(2, n)], postR=[])


CONTRACTS = {'ring_cols__L%d' % n: contract(n) for n in range(0, 64)}

OWN = []
