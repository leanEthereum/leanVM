"""`rs_eq_run`'s rules: its `count = q^8·r` split from hinted bits (`CoreMode.splitsC`: `q`, `r`, the selector `rv`,
`n`, `S`, `A`)."""

SPLITS = {'rs_eq_run': (((27, 1), (31, 1), (36, 1)), ((13, 1), (17, 1), (22, 1)), 23, 3, 8, 8)}

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fn/rs_eq_run/*.lean',
]
