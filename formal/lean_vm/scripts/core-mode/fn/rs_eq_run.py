"""`rs_eq_run`'s rules: its `count = q^8·r` split from hinted bits (`CoreMode.splitsC`: `q`, `r`, the selector `rv`,
`n`, `S`, `A`)."""

from fnrules import lean_def
from sigseed import cell, num, ex, run, sig


def _tup(x):
    return tuple(_tup(e) for e in x) if isinstance(x, (list, tuple)) else x


# its chain is its own HeapBuf: it reads `z_vals` and `point1` over the count `count_g`, and returns the final row
CONTRACTS = {'rs_eq_run': sig(range(5), None, [5], preR=[run(cell(0, [(c, 1)]), num(0), ex(4), 1, 0) for c in (2, 3)],
                              postR=[run(cell(0, [(5, 1)]), num(0), num(64), 1, 0)])}

# as its Lean data says (`CoreMode.spRs`)
SPLITS = {'rs_eq_run': _tup(lean_def('rs_eq_run', 'Fam', 'spRs'))}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
