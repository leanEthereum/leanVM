"""`rs_eq_run`'s rules: its `count = q^8·r` split from hinted bits (`CoreMode.splitsC`: `q`, `r`, the selector `rv`,
`n`, `S`, `A`)."""

from fnrules import lean_def


def _tup(x):
    return tuple(_tup(e) for e in x) if isinstance(x, (list, tuple)) else x


# as its Lean data says (`CoreMode.spRs`)
SPLITS = {'rs_eq_run': _tup(lean_def('rs_eq_run', 'Fam', 'spRs'))}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
