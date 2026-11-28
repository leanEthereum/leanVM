"""`rs_eq_run`'s contract (`sigc.py`): `rs_eq_run(z_vals, point1, count_g, seed)` reads `z_vals[g^i]`, `point1[g^i]`,
`i < log(count_g)`, and `seed[g^k]`, `k < BASE_FIELD_BITS`, and returns a row whose `BASE_FIELD_BITS` cells it leaves
written."""
from fnrules import guest_const, lean_def
from sigseed import sig, cell, num, ex, run

B = guest_const('BASE_FIELD_BITS')

CONTRACTS = {'rs_eq_run': sig(range(6), None, [6],
                              preR=[run(cell(0, [(2, 1)]), num(0), ex(4), 1, 0), run(cell(0, [(3, 1)]), num(0), ex(4), 1, 0),
                                    run(cell(0, [(5, 1)]), num(0), num(B), 1, 0)],
                              postR=[run(cell(0, [(6, 1)]), num(0), num(B), 1, 0)])}


def _tup(x):
    return tuple(_tup(e) for e in x) if isinstance(x, (list, tuple)) else x


# its `count = q^8·r` split from hinted bits (`CoreMode.splitsC`), as its Lean data says (`CoreMode.spRs`)
SPLITS = {'rs_eq_run': _tup(lean_def('rs_eq_run', 'Fam', 'spRs'))}

OWN = []
