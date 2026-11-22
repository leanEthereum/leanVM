"""`statement_digest`'s rules: its constant count (`scripts/count`)."""

# its constant bound in `Count/Static.lean`: order, kind, Lean name (`gen.py static`)
STATIC = {'statement_digest': (1, 'const', 'Sd')}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
