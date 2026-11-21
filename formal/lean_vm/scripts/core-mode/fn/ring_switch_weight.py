"""`ring_switch_weight`'s rules: its count within a ratio of its words (`scripts/count`)."""
from fnrules import lean_def_at

# counted within a ratio of its frame, its chain and its callee's words as its caller bounds them (the terminal's
# `termRswChain` and `rswBrsCap`, read from there) and its ratios checked (`Count/RatioV`): order, Lean name
_WORDS = (lean_def_at('B1/Terminal/TermCompleteB.lean', 'termRswChain')
          + lean_def_at('Count/Fn/check_opening_terminal.lean', 'rswBrsCap'))
RATIO_WORDS = {'ring_switch_weight': lambda C, n: C.fs(n) + _WORDS}
RATIOV = {'ring_switch_weight': (3, 'Vrsw')}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
