"""`aggregate_claims`' contract (`sigc.py`): `aggregate_claims(n_children_g, child_pi, child_fresh, child_carried,
defer_stmt, tabs)` reads, for each child `c < e(n_children_g)`, its statement's two words `child_pi·g^(2c + d)`, its
fresh claim `child_fresh·g^(DEFER_SIZE·c + d)`, `d < DEFER_SIZE`, and its carried one
`child_carried·g^(DEFER_STMT_CELLS·c + d)`, `d < DEFER_STMT_CELLS`, and the windows table `tabs[g^w]`,
`w < 2^WIN_TAB_BITS`; it leaves those written and the node's deferred claim `defer_stmt[g^d]`, `d < DEFER_STMT_CELLS`."""
from fnrules import guest_const
from sigseed import sig, cell, num, ex, run

DSZ = guest_const('DEFER_SIZE')
DS = guest_const('DEFER_STMT_CELLS')
WIN = 2 ** guest_const('WIN_TAB_BITS')


def per_child(o, S):
    return [run(cell(0, [(o, 1)]), num(0), ex(2), S, d) for d in range(S)]


_KEEP = per_child(3, 2) + per_child(4, DSZ) + per_child(5, DS) + [run(cell(0, [(7, 1)]), num(0), num(WIN), 1, 0)]
CONTRACTS = {'aggregate_claims': sig(range(8), None, [], preR=_KEEP,
                                     postR=_KEEP + [run(cell(0, [(6, 1)]), num(0), num(DS), 1, 0)])}

# ---- its four loops over `xc = g^c`, `c < e(n_children_g)` (cells `2`, `3`; `term` `e(xc) < e(n)`)
PS = guest_const('PEND_SLOTS')
PAIR = guest_const('PAIR_SLOTS')
BL = guest_const('BYTECODE_LOG')
NSP = guest_const('N_SPLIT')
BV = guest_const('BYTECODE_VARS')
BCV = guest_const('DEFER_STMT_BC_VALUE')
TERM = ['(%s, %s)' % (ex(2), ex(3))]


def over(o, S, d):
    """Cells `[o]·g^(S·c + d)` over the loop's range."""
    return run(cell(0, [(o, 1)]), ex(2), ex(3), S, d)


def row(o, S, ds):
    """The current row's cells `[xc]^S·[o]·g^d` (written by the caller, then by the previous iteration)."""
    return [cell(d, [(2, S), (o, 1)]) for d in ds]


def ptrs(r, cells):
    return '(%s, [%s])' % (r, ', '.join(map(str, cells)))


# `loop0(xc, n, absorb, child_fresh, fresh_row, child_carried, carried_row, child_pi)`: the transcript's rows, one per
# child, its words read; the rows' pointers to each child's claims kept
CONTRACTS['aggregate_claims_loop0'] = sig(
    range(10), 10, [], pre=row(4, PS, range(PS)),
    preR=[over(5, DSZ, d) for d in range(DSZ)] + [over(7, DS, d) for d in range(DS)] + [over(9, 2, d) for d in range(2)],
    term=TERM, postL=[over(4, PS, PS + d) for d in range(PS)] + [over(6, 1, 0), over(8, 1, 0)],
    postLP=[ptrs(over(6, 1, 0), range(DSZ)), ptrs(over(8, 1, 0), range(DS))])
# `loop1(xc, n, fresh_row, eq_col, fresh_val)`: each fresh claim's split values folded
CONTRACTS['aggregate_claims_loop1'] = sig(
    range(7), 7, [], pre=[cell(0, [(5, 1)])], preR=[over(4, 1, 0), run(cell(0, [(5, 1)]), num(0), num(NSP), 1, 0)],
    term=TERM, postL=[over(6, 1, 0)], preP=[ptrs(over(4, 1, 0), range(BL, BL + NSP))])
# `loop2(xc, n, bc_chain, fresh_row, carried_row, lam_sq, fresh_val, lam)`: the batching chain's rows
CONTRACTS['aggregate_claims_loop2'] = sig(
    range(10), 10, [], pre=row(4, PAIR, range(PAIR)),
    preR=[over(5, 1, 0), over(6, 1, 0), over(8, 1, 0)], term=TERM, postL=[over(4, PAIR, PAIR + d) for d in range(PAIR)],
    preP=[ptrs(over(6, 1, 0), [BCV])])
# `loop3(xc, n, fresh_row, carried_row, bc_point1, bc_chain, bc_wsum, eq_cols, lam)`: the weights' running sum
CONTRACTS['aggregate_claims_loop3'] = sig(
    range(11), 11, [], pre=[cell(0, [(2, 1), (8, 1)]), cell(0, [(6, 1)])],
    preR=[over(4, 1, 0), over(5, 1, 0), run(cell(0, [(6, 1)]), num(0), num(BV), 1, 0), over(7, PAIR, 0)],
    term=TERM, postL=[over(8, 1, 1)],
    preP=[ptrs(over(4, 1, 0), range(BL)), ptrs(over(5, 1, 0), range(BV))])

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
