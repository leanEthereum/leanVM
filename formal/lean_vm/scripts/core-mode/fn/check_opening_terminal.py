"""`check_opening_terminal`'s rules: its exponent and dimension facts (`Res.TermFront`)."""
import fnrules

_P = fnrules.param

# `tau_keccak_g`'s exponent below `31`; `kappa_base[0] = g^0`, `kappa_base[1..7]`'s below `31`; `gmv`'s below `31`
# (`Res.expFacts`); the loaded `kappa_base` words against the bounds `g_bus_mu`, `g_zc_n` at the pairs (`Res.dimFacts`:
# function, base parameter, bound parameter, pairs `(k, c)`, a subset of `busPairs`, `tabPairs` suffices here)
EXP_FACTS = [('check_opening_terminal', _P('check_opening_terminal', 'tau_keccak_g'), None, 31),
             ('check_opening_terminal', _P('check_opening_terminal', 'kappa_base'), 0, 1)] + \
    [('check_opening_terminal', _P('check_opening_terminal', 'kappa_base'), j + 1, 31) for j in range(7)] + \
    [('check_opening_terminal', _P('check_opening_terminal', 'gmv'), None, 31)]
DIM_FACTS = [('check_opening_terminal', 8, 4, {(1, 0), (0, 19)}),
             ('check_opening_terminal', 8, 5, {(j, 0) for j in range(2, 8)})]

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResE.lean',
    'LeanVM/Guest/CoreMode/Fam/TermQ.lean',
    'LeanVM/Guest/CoreMode/Fam/TermDefs.lean',
    'LeanVM/Guest/CoreMode/Fn/check_opening_terminal/*.lean',
    'LeanVM/Guest/Count/Fn/check_opening_terminal.lean',
]
