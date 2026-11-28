"""`claim_list_chain`'s rules: its contract, the claims' cells it writes, `[0, n)` (`n_g = g^n`)."""
from sigseed import cell, num, ex, run, sig

CONTRACTS = {'claim_list_chain': sig(range(7), None, [7, 8], postR=[run(cell(0, [(2, 1)]), num(0), ex(3), 4, d) for d in range(4)])}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
