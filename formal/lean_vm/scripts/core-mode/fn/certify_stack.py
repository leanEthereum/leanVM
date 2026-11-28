"""`certify_stack`'s contract (`sigc.py`): `certify_stack(kappa_base, g_squares)` reads `kappa_base[g^i]`,
`i < N_TABLES + 2`, and `g_squares`' cells `log2_ceil_in_the_exponent__L16_L34` reads (its exponent table `g^k`,
`k < SIZE_BITS`, among them, which the groups' sizes read at their kappas), and leaves the `2·N_STK_BLOCKS` words it
returns written: `g^offset`, then `g^kappa`, of each block."""
from fnrules import guest_const, lean_def

# range-checked point indices (`rcpts`), its buffers through its hinted order (`perm`), as `certify_placement`'s
FEATURES = {'certify_stack': [{'rcpts', 'perm'}]}
from sigseed import sig, cell, num, run

NT = guest_const('N_TABLES')
N = guest_const('N_STK_BLOCKS')
SB = guest_const('SIZE_BITS')


def gsq(lo, hi, d):
    return run(cell(0, [(3, 1)]), num(lo), num(hi), 1, d)


# `log2_ceil_in_the_exponent__L16_L34`'s preconditions on its table (its contract as written)
LOG2 = [gsq(0, 16, SB + 16 * t) for t in range(9)] + [gsq(0, SB, 0), gsq(1, SB, 2 ** 64 - 2)]

CONTRACTS = {'certify_stack': sig(range(4), None, [4, 5, 6],
                                  preR=[run(cell(0, [(2, 1)]), num(0), num(NT + 2), 1, 0)] + LOG2,
                                  postR=[run(cell(0, [(5, 1)]), num(0), num(2 * N), 1, 0),
                                         run(cell(0, [(6, 1)]), num(0), num(N), 1, 0)])}

# its `group_at` and its ranks' group values (`CoreMode.csAt`, `CoreMode.csRankVals`), as its Lean data says
CS_AT = lean_def('certify_stack', 'Fam', 'csAt')
CS_RANKS = lean_def('certify_stack', 'Fam', 'csRankVals')


def fam(k, r):
    """`CoreMode.csPerm`: its cell `[group_at]·g^j`, `j < 8`, one of `[group_at]·[v]` over its ranks' groups."""
    return k == 'certify_stack' and r[0] == 'subP' and tuple(r[1][0]) == ((CS_AT, 1),) and r[1][1] < 8 and \
        tuple(r[2]) == tuple((((CS_AT, 1), (v, 1)), 0) for v in CS_RANKS)

OWN = []
