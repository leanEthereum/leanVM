"""`verify_bus_gkr`'s rules."""
from sigseed import sig, cell, ex, run

# a loop's runs where it is not entered (`join`), point runs (`ptsrun`), range-checked point indices (`rcpts`), a run
# made up of pieces in scope (`chain`)
FEATURES = {'verify_bus_gkr': [{'join', 'ptsrun', 'rcpts', 'chain'}]}

# the point triangle's loop, whose run preconditions may be over its counter (`infer.py`)
CTR_PRE = {'verify_bus_gkr_loop0'}

# its point copy: `zeta[x] = row[x]` from `x` below `bound`
CONTRACTS = {'verify_bus_gkr_loop0': sig(
    range(6), 6, [],
    preR=[run(cell(0, [(5, 1)]), ex(2), ex(3), 1, 0)], term=['(%s, %s)' % (ex(2), ex(3))],
    postL=[run(cell(0, [(4, 1)]), ex(2), ex(3), 1, 0)])}


# ---- its counts (`scripts/count`)

# counted within a ratio of these words (`verify_sub`'s `vsCountT`) and its ratios checked (`Count/RatioV`): order,
# Lean name
RATIO_WORDS = {'verify_bus_gkr': 39767}
RATIOV = {'verify_bus_gkr': (0, 'Vbg')}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/Count/Fn/verify_bus_gkr.lean',
    'LeanVM/Guest/B1/Gkr/**',
    'LeanVM/Guest/B1/Sumcheck/Gkr.lean',
]
