"""`level_residual_sum`'s contracts (`sigc.py`): its specializations `level_residual_sum__L{queries}_L{prefix}_L{yr}_L{vanish}`
and their loops."""
from sigseed import sig, cell, num, ex, run
import fnrules


# `level_residual_sum(positions, fold_cs, tail_cs, lam)`: the challenges `fold_cs·g^t`, `t < prefix`, `tail_cs·g^j`,
# `j < yr`, and the positions `[0, queries)` read.
def _sum(q, p, y):
    return sig(range(6), None, [6],
               pre=[cell(t, [(3, 1)]) for t in range(p)] + [cell(j, [(4, 1)]) for j in range(y)],
               preR=[run(cell(0, [(2, 1)]), num(0), num(q), 1, 0)])


# its loop (`xq, g^queries, acc, pw, positions, fold_cs, tail_cs, lam`): `positions·xq`, `acc·xq`, `pw·xq` read,
# `acc·xq·g`, `pw·xq·g` written.
def _loop(p, y):
    return sig(range(10), 10, [],
               pre=[cell(t, [(7, 1)]) for t in range(p)] + [cell(j, [(8, 1)]) for j in range(y)] +
               [cell(0, [(2, 1), (4, 1)]), cell(0, [(2, 1), (5, 1)])],
               preR=[run(cell(0, [(6, 1)]), ex(2), ex(3), 1, 0)],
               term=['(%s, %s)' % (ex(2), ex(3))],
               postL=[run(cell(0, [(o, 1)]), ex(2), ex(3), 1, 1) for o in (4, 5)])


CONTRACTS = {}
for _k, (_q, _p, _y, _) in fnrules.shapes('level_residual_sum').items():
    CONTRACTS[_k] = _sum(_q, _p, _y)
    CONTRACTS[_k + '_loop0'] = _loop(_p, _y)

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
