"""`check_opening_terminal`'s rules: its exponent and dimension facts (`Res.TermFront`)."""
import fnrules

_P = fnrules.param

# `tau_keccak_g`'s exponent below `31`; `kappa_base[0] = g^0`, `kappa_base[1..7]`'s below `31`; `gmv`'s below `31`
# (`Res.expFacts`); the loaded `kappa_base` words against the bounds `g_bus_mu`, `g_zc_n` at the pairs (`Res.dimFacts`:
# function, base parameter, bound parameter, pairs `(k, c)`, a subset of `busPairs`, `tabPairs` suffices here)
EXP_FACTS = fnrules.lean_def('check_opening_terminal', 'Data', 'expFacts')
DIM_FACTS = [('check_opening_terminal', _P('check_opening_terminal', 'kappa_base'), _P('check_opening_terminal', 'g_bus_mu'),
              {(1, 0), (0, 19)}),
             ('check_opening_terminal', _P('check_opening_terminal', 'kappa_base'), _P('check_opening_terminal', 'g_zc_n'),
              {(j, 0) for j in range(2, 8)})]


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `W` family (`kcTermW`); its loop within a ratio of its words (`Count/RatioV`):
# order, Lean name
COUNT_SHAPE = {'check_opening_terminal': 'W'}
RATIOV = {'check_opening_terminal_loop0': (2, 'Vl15')}


def count_walk(C, k, n):
    """Its instructions (`B1.VerifySub.termWB` at `Count.vsWords`): its body, its loop within its ratio of `32 · 38`
    words or its frame."""
    import vscount
    if n != vscount.L('check_opening_terminal'):
        return None
    lp = vscount.L('check_opening_terminal_loop0')

    def call_if(f):
        assert f == lp, f
        return C.ratioA(f)[k] * max(C.fs(f), 32 * 38) // 1000
    return C.walk(k, n, call_if)


def count_parts(g, OPS):
    """`VsCountData`'s `kcTermW`."""
    import vscount
    C = vscount.cnt(g, 'V')
    return [dict(mod='VsCountData', key=4, tables=[vscount.opdef(
        OPS, 'kcTermW', 'The terminal\'s instructions (`B1.VerifySub.termWB Count.vsWords`).',
        lambda k: C.weight(k, vscount.L('check_opening_terminal')))])]

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/TermDefs.lean',
    'LeanVM/Guest/Count/Fn/check_opening_terminal.lean',
]
