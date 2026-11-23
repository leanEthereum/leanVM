"""`selector_tables`' contract (`sigc.py`): the opening point's coordinates read, each nibble's eq tables written."""
from sigseed import sig, cell, num, run
from fnrules import guest_const, guest_arr

SEL_EQ_STRIDE, SEL_NIBBLES, SEL_EQ_OFF = guest_const('SEL_EQ_STRIDE'), guest_const('SEL_NIBBLES'), guest_arr('SEL_EQ_OFF')

# `selector_tables(point, point1)` reads the point's coordinates and their complements, `4·SEL_NIBBLES` each, and
# returns `sel_eq`: nibble `j`'s level-`w` table, `2^(w + 1)` entries `2^(3 - w)` apart from `SEL_EQ_STRIDE·j + SEL_EQ_OFF[w]`
# (the runs `column_selector` reads).
CONTRACTS = {'selector_tables': sig(
    range(4), None, [4],
    pre=[cell(t, [(c, 1)]) for t in range(4 * SEL_NIBBLES) for c in (2, 3)],
    postR=[run(cell(0, [(4, 1)]), num(0), num(2 ** (w + 1)), 2 ** (3 - w), SEL_EQ_STRIDE * j + SEL_EQ_OFF[w])
           for j in range(SEL_NIBBLES) for w in range(4)])}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
