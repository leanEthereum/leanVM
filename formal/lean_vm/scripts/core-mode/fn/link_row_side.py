"""`link_row_side`'s contracts (`sigc.py`): `link_row_side__L{d}(fs0, .., fs4, cursor, claim, chi, q_point, g_n, tabs)`
runs `link_rounds__L{d+1}_L{b1}` over `count_g = g_n` from `cursor`, then `link_rounds__L{d}_L{b2}` over
`g^LINK_Q_VARS` from the cursor the first returns, `cursor·g_n^W1` (its `retV`): it reads the `W1` residue runs
`[cursor]·g^r·[0, e(g_n))` of stride `W1`, then the `W2` residue runs `[cursor·g_n^W1]·g^r·[0, LINK_Q_VARS)`, with a grind
the windows table `tabs`, returns the cursor `cursor·g_n^W1·g^(W2·LINK_Q_VARS)`, and leaves the points
`chi[g^i]`, `i < e(g_n)`, and `q_point[g^i]`, `i < LINK_Q_VARS`, written."""
from fnrules import guest_const, guest_arr, shapes
from sigseed import sig, cell, num, run

WIN = 2 ** guest_const('WIN_TAB_BITS')
Q = guest_const('LINK_Q_VARS')
ROW, PTR = guest_arr('LINK_ROW_GRIND'), guest_arr('LINK_PTR_GRIND')
# frame cells: `cursor`, `g_n`, `tabs`
CUR, GN, TABS = 7, 11, 12
# frame cells: `chi`, `q_point`
CHI, QP = 9, 10


def contract(d):
    W1 = d + 2 + (1 if ROW[d] else 0)
    W2 = d + 1 + (1 if PTR[d] else 0)
    runs = [run(cell(0, [(CUR, 1)]), num(0), '(.ex (.fr %d) 0)' % GN, W1, r) for r in range(W1)] + \
        [run(cell(0, [(CUR, 1), (GN, W1)]), num(0), num(Q), W2, r) for r in range(W2)]
    tabs = [run(cell(0, [(TABS, 1)]), num(0), num(WIN), 1, 0)] if ROW[d] or PTR[d] else []
    # the points its two `link_rounds` write (their `postR`): `chi[g^i]`, `i < e(g_n)`; `q_point[g^i]`, `i < Q`
    pts = [run(cell(0, [(CHI, 1)]), num(0), '(.ex (.fr %d) 0)' % GN, 1, 0),
           run(cell(0, [(QP, 1)]), num(0), num(Q), 1, 0)]
    return sig(range(13), None, range(13, 20), preR=runs + tabs, postR=pts,
               retV=['(18, %s)' % cell(W2 * Q, [(CUR, 1), (GN, W1)])])


CONTRACTS = {'link_row_side__L%d' % s[0]: contract(s[0]) for s in shapes('link_row_side').values()}

OWN = []
