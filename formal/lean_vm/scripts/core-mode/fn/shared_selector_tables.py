"""`shared_selector_tables`' rules: its `len = q^4·r` split from hinted bits (`CoreMode.splitsC`)."""

SPLITS = {'shared_selector_tables': (((24, 1), (28, 1), (33, 1), (38, 1)), ((15, 1), (19, 1)), 20, 5, 4, 16)}

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fn/shared_selector_tables/*.lean',
]
