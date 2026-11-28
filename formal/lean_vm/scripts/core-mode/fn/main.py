"""`main`'s rules: its long loop `main_loop2` checked in windows of its own sizes (`windows.py`)."""

# instructions per code window (`core.py`), per pairing window (`pair.py`), per frame walk window (`frame_gen.py`)
CORE_WIN = {'main_loop2': 6144}
PAIR_WIN = {'main_loop2': 2048}
FRAME_WIN = {'main_loop2': 4000}


# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/B1/Main/**',
]


# ---- its loop `main_loop4`'s contract (`sigc.py`), the children's loop: over `xc = g^c`, `c < e(n_children_g)` (cells
# `2`, `3`), it reads `written[xc]` and the claim tables' four-word records up to their counts, and the exponent tables
# `g_squares[g^i]`, `i < WIN_TAB_AT + WIN_TAB_LEN` (`exponent_tables`'), and leaves written each child's `written` entry,
# carried claim (`DEFER_STMT_CELLS` cells), DA digest (`2`), statement (`2`) and fresh claim (`DEFER_SIZE` cells).
def _ml4():
    from fnrules import guest_const
    from sigseed import sig, cell, num, ex, run
    DSZ, DS = guest_const('DEFER_SIZE'), guest_const('DEFER_STMT_CELLS')
    TAB = guest_const('WIN_TAB_AT') + guest_const('WIN_TAB_LEN')

    def over(o, S, d):
        return run(cell(0, [(o, 1)]), ex(2), ex(3), S, d)
    return sig(range(18), 18, [], pre=[cell(0, [(2, 1), (4, 1)]), cell(0, [(16, 1)])],
               preR=[run(cell(0, [(5, 1)]), num(0), ex(7), 4, d) for d in range(4)] +
               [run(cell(0, [(8, 1)]), num(0), ex(10), 4, d) for d in range(4)] + [run(cell(0, [(16, 1)]), num(0), num(TAB), 1, 0)],
               term=['(%s, %s)' % (ex(2), ex(3))],
               postL=[over(4, 1, 1)] + [over(11, DS, d) for d in range(DS)] + [over(12, 2, d) for d in range(2)] +
               [over(15, 2, d) for d in range(2)] + [over(17, DSZ, d) for d in range(DSZ)])


CONTRACTS = {'main_loop4': _ml4()}
