"""`eq_prefix_chain_rev`'s contract (`sigc.py`)."""
from sigseed import sig, cell, num, ex, run

# `eq_prefix_chain_rev(chain, out, src, b1, count_g)`: as `eq_prefix_chain`, `out` written below `count_g`.
CONTRACTS = {'eq_prefix_chain_rev': sig(
    range(7), None, [],
    preR=[run(cell(0, [(o, 1)]), num(0), ex(6), 1, 0) for o in (4, 5)],
    postR=[run(cell(0, [(2, 1)]), num(0), ex(6, 1), 1, 0), run(cell(0, [(2, 1)]), num(0), num(1), 1, 0)] +
    [run(cell(0, [(o, 1)]), num(0), ex(6), 1, 0) for o in (3, 4, 5)])}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
