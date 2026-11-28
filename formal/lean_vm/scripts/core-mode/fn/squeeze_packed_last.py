"""`squeeze_packed_last`'s contracts (`sigc.py`): `squeeze_packed_last__L{k}(rec, end, cells)` reads the record
`rec[g^j]`, `j < FS_CELLS`, and leaves the record `end[g^j]`, `j < FS_CELLS`, and `cells[g^j]`, `j < 8k`, written."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

FS = guest_const('FS_CELLS')


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(k):
    return sig(range(5), None, [5], preR=[par(0, FS)], postR=[par(1, FS)] + ([par(2, 8 * k)] if k else []))


CONTRACTS = {'squeeze_packed_last__L%d' % k: contract(k) for k in range(0, 4)}

OWN = []
