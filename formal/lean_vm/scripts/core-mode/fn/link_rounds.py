"""`link_rounds`' rules (`sigc.py`, `callcres.py`): `link_rounds__L{t}_L{b}(fs0, .., fs4, cursor, claim, point, count_g,
tabs)` reads the `count = log(count_g)` rounds' words past `cursor`, `W = t + 1 + [b > 0]` a round, as the `W` residue
runs `[cursor]·g^d·[0, count)` of stride `W`, and with a grind the windows table `tabs`, and leaves its challenges
`point[g^i]`, `i < count`, written: the contract of every specialization. Its loop
`link_rounds__L{t}_L{b}_loop0(x, h_g, recs, point, tabs)` runs four rounds an iteration from the record
`recs·x^7`, reading `4W` words past the record's cursor (its value `v`): a cursor-run loop (`CoreMode.stLoops`), its
caller's cells `7` (`cursor`) and `10` (`count_g`) linked to its first two ghost slots."""
from fnrules import guest_const, shapes, lean_def
from sigseed import sig, cell, num, run

REC = guest_const('LINK_REC')
WIN = 2 ** guest_const('WIN_TAB_BITS')
# `link_rounds`' frame cells of `cursor` and `count_g`
CUR, CNT = 7, 10
# its frame cell of `point`
PT = 9

ST_LOOPS = {e[0]: e[1:] for e in lean_def('link_rounds', 'Data', 'stLoops')}


def lin(d, W):
    """Residue `d` of the run past the caller's cell `CUR`, below the exponent of its cell `CNT`, stride `W`."""
    return '⟨⟨0, 0, [((.hp 1 %d), 1)]⟩, (.num 0), (.ex (.hp 1 %d) 0), %d, %d⟩' % (CUR, CNT, W, d)


def ex(o):
    return '(.ex (.fr %d) 0)' % o


def loop_contract(t, b):
    W = t + 1 + (1 if b else 0)
    # the record at `recs·x^7` (`x` cell 2, `recs` cell 4), the windows table (`tabs`, cell 6) with a grind
    pre = [cell(k, [(2, 7), (4, 1)]) for k in range(REC)]
    tabs = [run(cell(0, [(6, 1)]), num(0), num(WIN), 1, 0)] if b else []
    # the challenges at `point·g^(4i + d)` (`point` cell 5) and the next records at `recs·g^(7i + 7 + d)`, over the
    # iterations `[e(x), e(h_g))` (`h_g` cell 3)
    postL = [run(cell(0, [(5, 1)]), ex(2), ex(3), 4, d) for d in range(4)] + \
        [run(cell(0, [(4, 1)]), ex(2), ex(3), REC, REC + d) for d in range(REC)]
    return sig(range(7), 7, [], pre=pre, preR=[lin(d, W) for d in range(W)] + tabs, term=['(%s, %s)' % (ex(2), ex(3))],
               postL=postL)


def contract(t, b):
    W = t + 1 + (1 if b else 0)
    # `cursor` (cell 7) past which the rounds read, below the exponent of `count_g` (cell 10); the windows table `tabs`
    # (cell 11) with a grind; the cursor returned (cell 17) `W·count` words on
    runs = [run(cell(0, [(CUR, 1)]), num(0), ex(CNT), W, d) for d in range(W)]
    tabs = [run(cell(0, [(11, 1)]), num(0), num(WIN), 1, 0)] if b else []
    # the challenges `point[g^i]`, `i < e(count_g)` (`point` cell 9): the loop's four residue runs merged at `h_g^4`
    # (`split_count`'s kept equation `count_g = h_g^4·r_g`), then the tail arm's block
    return sig(range(12), None, range(12, 19), preR=runs + tabs, postR=[run(cell(0, [(PT, 1)]), num(0), ex(CNT), 1, 0)],
               retV=['(17, %s)' % cell(0, [(CUR, 1), (CNT, W)])])


CONTRACTS = {}
# the returned cursor, the word `link_rounds_last` stored at `out·g^5` (value `73`), is `cursor·count_g^W` (values `5`,
# `8`): an equation residual its own family proves (`CoreMode/Fn/link_rounds/Fam.lean`)
RES_EQ = {}
for s in shapes('link_rounds').values():
    CONTRACTS['link_rounds__L%d_L%d_loop0' % s] = loop_contract(*s)
    CONTRACTS['link_rounds__L%d_L%d' % s] = contract(*s)
    RES_EQ['link_rounds__L%d_L%d' % s] = [((((73, 1),), 0), (((5, 1), (8, s[0] + 1 + (1 if s[1] else 0))), 0))]


def fam(k, r):
    """Its equation residuals (`RES_EQ`)."""
    return r[0] == 'eq' and (r[1], r[2]) in RES_EQ.get(k, ())


OWN = []
