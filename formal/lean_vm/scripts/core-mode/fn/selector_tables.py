"""`selector_tables`'s contracts (`sigc.py`): `selector_tables__L{n}(point, point1)` reads `point[g^k]`, `point1[g^k]`,
`k < 4n`, and leaves written, in the table it returns, each nibble `j < n`'s eq tables: level `w < 4` at
`g^(SEL_EQ_STRIDE·j + SEL_EQ_OFF[w])`, `2^(w + 1)` entries `2^(3 - w)` apart."""
from fnrules import guest_const, guest_arr
from sigseed import sig, cell, num, run

STRIDE = guest_const('SEL_EQ_STRIDE')
OFF = guest_arr('SEL_EQ_OFF')


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    post = [run(cell(0, [(4, 1)]), num(0), num(2 ** (w + 1)), 2 ** (3 - w), STRIDE * j + OFF[w])
            for j in range(n) for w in range(4)]
    return sig(range(4), None, [4], preR=[par(0, 4 * n), par(1, 4 * n)], postR=post)


CONTRACTS = {'selector_tables__L%d' % n: contract(n) for n in range(0, 16)}

OWN = []
