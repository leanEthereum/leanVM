"""`decode_query_windows`' contracts (`sigc.py`): `decode_query_windows__L{d}_L{c}(word, positions_out, win_ptrs_out,
tabs)` reads `tabs[g^n]`, `n < 2^w`, for its windows' widths `w <= 7`, and writes `FIELD_BITS // d` positions and
window pointers, each pointing at its query's `n_win` windows."""
from fnrules import guest_const
from sigseed import sig, cell, num, run, ptrs

F, QW = guest_const('FIELD_BITS'), guest_const('QW')


def par(i, hi, lo=0):
    """Parameter `i`'s cells `[p]·g^k`, `lo <= k < hi`."""
    return run(cell(0, [(2 + i, 1)]), num(lo), num(hi), 1, 0)


TABS = [par(3, 2), par(3, 64), par(3, 128)]


def contract(d, c):
    pw, n_win = F // d, (d - c + QW - 1) // QW + 2
    return sig(range(6), None, [], preR=TABS, postR=[par(1, pw), par(2, pw)] + TABS,
               postP=[ptrs(par(2, pw), range(n_win))])


# the tree and cap depths whose windows cross a limb, whose contracts the bus era did not write
CONTRACTS = {'decode_query_windows__L%d_L%d' % dc: contract(*dc) for dc in [(9, 3), (10, 4), (11, 5), (14, 2), (14, 8)]}

OWN = []
