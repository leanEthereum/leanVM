"""`certify_placement`'s rules."""

# range-checked point indices (`rcpts`), its buffers through its hinted order (`perm`)
FEATURES = {'certify_placement': [{'rcpts', 'perm'}]}

from fnrules import val, lean_def

# its ranks' group values (`CoreMode.cpRanks`, `B1.Tables.cpRB`), as its Lean data says, and its `group_base`
CP_RANKS = lean_def('certify_placement', 'Fam', 'cpRanks')
CP_BASE = val('certify_placement', 'group_base')


def fam(k, r):
    """`CoreMode.cpPerm`: its cell `[group_base]·g^j`, `j < 9`, one of `[group_base]·[v]` over its ranks' groups."""
    return k == 'certify_placement' and r[0] == 'subP' and r[1][0] == ((CP_BASE, 1),) and r[1][1] < 9 and \
        tuple(r[2]) == tuple((((CP_BASE, 1), (v, 1)), 0) for v in CP_RANKS)

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
