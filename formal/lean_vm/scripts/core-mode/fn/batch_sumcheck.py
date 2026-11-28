"""`batch_sumcheck`'s contracts (`sigc.py`): `batch_sumcheck__L{n}(fs0, .., fs4, msgs, running, point, tabs)` reads its
rounds' words `msgs[g^k]`, `k < n·BC_ROUND_WORDS`, and, with a round's grind, the windows table `tabs[g^w]`,
`w < 2^WIN_TAB_BITS`, and leaves its challenges `point[g^r]`, `r < n`, written."""
from fnrules import guest_const
from sigseed import sig, cell, num, run

W = guest_const('BC_ROUND_WORDS')
WIN = 2 ** guest_const('WIN_TAB_BITS')
GRIND = guest_const('ROUND2_GRIND_BITS') > 0


def par(i, n):
    """Parameter `i`'s cells `[p]·g^k`, `k < n`."""
    return run(cell(0, [(2 + i, 1)]), num(0), num(n), 1, 0)


def contract(n):
    return sig(range(11), None, list(range(11, 17)), preR=[par(5, n * W)] + ([par(8, WIN)] if GRIND else []),
               postR=[par(7, n)])


CONTRACTS = {'batch_sumcheck__L%d' % n: contract(n) for n in range(1, 33)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []
