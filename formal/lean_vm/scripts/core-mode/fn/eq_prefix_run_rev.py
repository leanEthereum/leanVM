"""`eq_prefix_run_rev`'s contracts (`sigc.py`)."""
from sigseed import sig, cell, num, run

CONTRACTS = {}
# `eq_prefix_run_rev(chain, out, src, b1, n)`: reads `src`, `b1` below `g^n`, writes `chain` to `g^n` and `out` below.
for _n in range(33):
    CONTRACTS['eq_prefix_run_rev__L%d' % _n] = sig(
        range(6), None, [6],
        pre=[cell(k, [(o, 1)]) for k in range(_n) for o in (4, 5)],
        postR=[run(cell(0, [(2, 1)]), num(0), num(_n + 1), 1, 0)] +
        [run(cell(0, [(o, 1)]), num(0), num(_n), 1, 0) for o in (3, 4, 5) if _n])

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/B1/Eq/EqPrefixRev*.lean',
]
