"""`statement_digest`'s rules: its contract (`sigc.py`):
`statement_digest(seed_0, seed_1, xd_0, xd_1, sd_0, sd_1, da_0, da_1, defer)` reads `defer[g^i]`, `i < DEFER_STMT_CELLS`,
and returns its two words (the bus era's contract named `24` cells)."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

DS = guest_const('DEFER_STMT_CELLS')
CONTRACTS = {'statement_digest': sig(range(11), None, [11, 12], preR=[run(cell(0, [(10, 1)]), num(0), num(DS), 1, 0)],
                                     postR=[run(cell(0, [(10, 1)]), num(0), num(DS), 1, 0)])}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
