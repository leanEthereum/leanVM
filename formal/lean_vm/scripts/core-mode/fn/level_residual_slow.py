"""`level_residual_slow`'s contracts (`sigc.py`): its specializations `level_residual_slow__L{queries}_L{prefix}_L{yr}_L{vanish}`."""
from sigseed import sig, cell, num, run
import fnrules

# `level_residual_slow(positions, fold_cs, tail_cs, lam, zero)`: at `zero ≠ 0` its sum's reads, the challenges
# `fold_cs·g^t`, `t < prefix`, `tail_cs·g^j`, `j < yr`, and the positions `[0, queries)`.
CONTRACTS = {k: sig(range(7), None, [7],
                    pre=[cell(t, [(3, 1)]) for t in range(p)] + [cell(j, [(4, 1)]) for j in range(y)],
                    preR=[run(cell(0, [(2, 1)]), num(0), num(q), 1, 0)])
             for k, (q, p, y, _) in fnrules.shapes('level_residual_slow').items()}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
