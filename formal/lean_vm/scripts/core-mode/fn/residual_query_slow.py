"""`residual_query_slow`'s contracts (`sigc.py`): its specializations `residual_query_slow__L{prefix}_L{yr}_L{vanish}`."""
from sigseed import sig, cell
import fnrules

# `residual_query_slow(x, fold_cs, tail_cs)`: the challenges `fold_cs·g^t`, `t < prefix`, and `tail_cs·g^j`, `j < yr`,
# read.
CONTRACTS = {k: sig(range(5), None, [5],
                    pre=[cell(t, [(3, 1)]) for t in range(p)] + [cell(j, [(4, 1)]) for j in range(y)])
             for k, (p, y, _) in fnrules.shapes('residual_query_slow').items()}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
