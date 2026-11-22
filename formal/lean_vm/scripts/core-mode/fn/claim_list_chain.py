"""`claim_list_chain`'s rules: its contract, the claims' cells it writes, `[0, n)` (`n_g = g^n`); its count by its tree's
shape (`claim_list_digest`'s)."""
from sigseed import cell, num, ex, run, sig

CONTRACTS = {'claim_list_chain': sig(range(7), None, [7, 8], postR=[run(cell(0, [(2, 1)]), num(0), ex(3), 4, d) for d in range(4)])}

# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family (`claim_list_digest`'s); its frame weight in `MvCountData`
COUNT_SHAPE = {'claim_list_chain': 'V'}
COUNT_OM = {'claim_list_chain': ('MvCountData', 3)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
