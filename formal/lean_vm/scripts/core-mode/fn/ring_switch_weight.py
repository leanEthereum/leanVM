"""`ring_switch_weight`'s rules: its count within a ratio of its words (`scripts/count`)."""

# counted within a ratio of its frame and `2240 + 16433` words (the terminal's `kcTermW`) and its ratios checked
# (`Count/RatioV`): order, Lean name
RATIO_WORDS = {'ring_switch_weight': lambda C, n: C.fs(n) + 2240 + 16433}
RATIOV = {'ring_switch_weight': (3, 'Vrsw')}

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = []
