"""`check_stack_terminal`'s rules: the exponent facts on its kappa source `kappa_base[g^(2 + TABLE_KECCAK)]` (which bounds
`rs_eq_run`'s runs at `kq_g = kappa_base[g^7]·g^QKECCAK_SLOT_LOG`) and on `gmv`, `g_n`, `g_log_mem` (`Res.expFacts`), and
its dimension facts below `g_n` (`Res.dimFacts`: `kappa_base[g^(2 + t)]`, the sent targets' `kaps[g^b]`), all certified
by `verify_sub` (`CsQ`, `CstQ`); its contract (`sigc.py`): the runs it reads, `z_vals`' two points bounded by that word's
exponent plus `QKECCAK_SLOT_LOG` (`.ex (.hp 3 7) QKECCAK_SLOT_LOG`, the word a precondition cell)."""
import fnrules as _R
from fnrules import guest_const
from sigseed import sig, cell, num, ex, run

EXP_FACTS = _R.lean_def('check_stack_terminal', 'Data', 'expFacts')
DIM_FACTS = _R.lean_def('check_stack_terminal', 'Data', 'dimFacts')

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = []

QV = guest_const('QKECCAK_VARS_CAP')
QS = guest_const('QKECCAK_SLOT_LOG')
SB = guest_const('SIZE_BITS')
NB = guest_const('N_STK_BLOCKS')
NP = guest_const('N_POINTERS')
EQA = guest_const('EQ_Q_AT')
BF = guest_const('BASE_FIELD_BITS')
KB = 2 + guest_const('TABLE_KECCAK')


def par(i, lo, hi, d=0):
    """Parameter `i`'s cells `[p]·g^(d + k)`, `lo <= k < hi`."""
    return run(cell(0, [(2 + i, 1)]), lo, hi, 1, d)


# the Keccak table's height exponent plus the slot's bits: `kq_g`'s, the word at `kappa_base·g^KB` (`.hp 3 KB`)
KQ = '(.ex (.hp 3 %d) %d)' % (KB, QS)
CONTRACTS = {'check_stack_terminal': sig(range(25), None, [], pre=[cell(KB, [(3, 1)])], preR=[
    par(0, num(0), num(16 * 8), SB), par(1, num(0), num(KB + 1)), par(2, num(0), num(NB)), par(3, num(0), num(NB)),
    par(5, num(0), ex(8)), par(7, num(0), ex(10)), par(10, num(0), KQ), par(10, num(0), KQ, QV),
    par(11, num(0), num(NP), EQA), par(12, num(0), num(BF)), par(17, num(0), num(SB + QS)), par(18, num(0), num(SB + QS)),
    par(22, num(0), ex(6))])}
