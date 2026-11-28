"""`stack_selectors`'s contracts (`sigc.py`): `stack_selectors__L{n}(offs, kaps, point, point1, g_squares)` reads
`offs[g^b]`, `kaps[g^b]`, `b < N_STK_BLOCKS`, `point[g^k]`, `point1[g^k]`, `k < 4n` (`selector_tables`), and
`g_squares[g^(34 + k)]`, `k < 16n` (the nibble shares `column_selector` reads at `sel_g = g_squares·g^34`), and leaves
the `N_STK_BLOCKS` selectors it returns written."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

N = guest_const('N_STK_BLOCKS')
SB = guest_const('SIZE_BITS')


def par(i, n, d=0):
    """Parameter `i`'s cells `[p]·g^(d + k)`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, d)


def contract(n):
    return sig(range(7), None, [7], preR=[par(0, N), par(1, N), par(2, 4 * n), par(3, 4 * n), par(4, 16 * n, SB)],
               postR=[run(cell(0, [(7, 1)]), num(0), num(N), 1, 0)])


CONTRACTS = {'stack_selectors__L%d' % n: contract(n) for n in range(0, 16)}

OWN = []
