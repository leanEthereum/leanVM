"""`link_rounds_last`'s contracts (`sigc.py`): `link_rounds_last__L{t}_L{b}_L{k}(rd, out, pts, tabs)` reads the record
`rd[g^j]`, `j < LINK_REC`, and leaves the record `out[g^j]`, `j < LINK_REC`, written; for `k > 0` rounds it also reads
`k·W` words past the record's cursor `rd[g^5]` (its value `9`), `W = t + 1 + [b > 0]` a round, with a grind (`b > 0`) the
windows table `tabs`, and leaves `pts[g^q]`, `q < k`, written. Those reads lie in its caller's run: a cursor-run arm
(`CoreMode.stLoops`, as `link_rounds`' loops), `link_rounds`' cells `7` (`cursor`) and `10` (`count_g`) linked to its
first two ghost slots, its precondition the `W` residue runs `[cursor]·g^d·[0, e(count_g))` of stride `W`."""
from fnrules import guest_const, lean_def
from sigseed import sig, cell, num, run

REC = guest_const('LINK_REC')
# the grind's windows table `tabs[g^w]`, `w < 2^WIN_TAB_BITS`
WIN = 2 ** guest_const('WIN_TAB_BITS')
# `link_rounds`' frame cells of `cursor` and `count_g`
CUR, CNT = 7, 10

ST_LOOPS = {e[0]: e[1:] for e in lean_def('link_rounds_last', 'Data', 'stLoops')}


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def lin(d, W):
    """Residue `d` of the run past the caller's cell `CUR`, below the exponent of its cell `CNT`, stride `W`."""
    return '⟨⟨0, 0, [((.hp 1 %d), 1)]⟩, (.num 0), (.ex (.hp 1 %d) 0), %d, %d⟩' % (CUR, CNT, W, d)


def contract(t, b, k):
    if k == 0:
        return sig(range(6), None, [6], preR=[par(0, REC)], postR=[par(1, REC)])
    W = t + 1 + (1 if b else 0)
    tabs = [par(3, WIN)] if b else []
    return sig(range(6), None, [6], preR=[par(0, REC)] + [lin(d, W) for d in range(W)] + tabs,
               postR=[par(1, REC), par(2, k)])


# specialized on `n_tail`, `bits` and `k`
CONTRACTS = {'link_rounds_last__L%d_L%d_L%d' % (t, b, k): contract(t, b, k)
             for t in range(0, 16) for b in range(0, 4) for k in range(0, 4)}

OWN = []
