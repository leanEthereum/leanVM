"""`table_size`'s contracts (`sigc.py`): `table_size__L{h}(rows, bits)` leaves the row count's certified bits
`bits[g^k]`, `k ≤ h`, written (its `hint_decompose_bits`, each then squared in place)."""
from fnrules import shapes
from sigseed import sig, cell, num, run


def contract(h):
    return sig(range(4), None, [4, 5, 6], postR=[run(cell(0, [(3, 1)]), num(0), num(h + 1), 1, 0)])


CONTRACTS = {'table_size__L%d' % s[0]: contract(s[0]) for s in shapes('table_size').values()}

OWN = []
