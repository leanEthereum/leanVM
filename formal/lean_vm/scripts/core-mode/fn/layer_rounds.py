"""`layer_rounds`'s contracts (`sigc.py`): `layer_rounds__L{n}(fs0, .., fs4, cursor, run, prev_point, point, tabs)` reads
`cursor[g^k]`, `k < 2n`, and `prev_point[g^q]`, `q < n`, leaves `point[g^q]`, `q < n`, written, and returns its cursor
`cursor·g^(2n)` (frame cell `17`)."""
from sigseed import sig, cell, num, run


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(12), None, range(12, 19), preR=[par(5, 2 * n), par(7, n)], postR=[par(8, n)],
               retV=['(17, %s)' % cell(2 * n, [(7, 1)])])


# specialized on `n`; `n = 0` reads and writes nothing
CONTRACTS = {'layer_rounds__L%d' % n: contract(n) for n in range(1, 64)}

OWN = []
