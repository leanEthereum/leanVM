"""`packed_message`'s contracts (`sigc.py`): `packed_message__L{n}(fs0, .., fs4, msg)` reads `msg[g^k]`, `k < n`."""
from sigseed import sig, cell, num, run


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


CONTRACTS = {'packed_message__L%d' % n: sig(range(8), None, range(8, 14), preR=[par(5, n)], postR=[])
             for n in range(1, 1024)}

OWN = []
