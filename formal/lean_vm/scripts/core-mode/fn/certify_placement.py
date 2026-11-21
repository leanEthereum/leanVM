"""`certify_placement`'s rules."""

# range-checked point indices (`rcpts`), its buffers through its hinted order (`perm`)
FEATURES = {'certify_placement': [{'rcpts', 'perm'}]}

# its ranks' group values (`CoreMode.cpRanks`, `B1.Tables.cpRB`)
CP_RANKS = [138] + [131 + 18 * r for r in range(1, 9)]


def fam(k, r):
    """`CoreMode.cpPerm`: its cell `[137]·g^j`, `j < 9`, one of `[137]·[v]` over its ranks' groups."""
    return k == 'certify_placement' and r[0] == 'subP' and r[1][0] == ((137, 1),) and r[1][1] < 9 and \
        tuple(r[2]) == tuple((((137, 1), (v, 1)), 0) for v in CP_RANKS)

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResCp.lean',
    'LeanVM/Guest/CoreMode/Fn/certify_placement/*.lean',
]
