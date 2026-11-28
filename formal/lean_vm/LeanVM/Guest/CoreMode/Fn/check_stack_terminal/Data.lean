/-
  LeanVM.Guest.CoreMode.Fn.check_stack_terminal.Data

  `check_stack_terminal`'s own routing data (`CoreMode/FnReg.lean`): the exponent bounds of its kappa source
  `kappa_base[g^(2 + TABLE_KECCAK)]` and of `gmv`, `g_n`, `g_log_mem`, and the dimension facts below `g_n`, which
  `verify_sub` certifies.
-/

module

public meta import LeanVM.Guest.CoreRef
public import LeanVM.Guest.Data.NameStrings
public import LeanVM.Guest.Renumber

namespace LeanVM.Guest.CoreMode.Own.check_stack_terminal

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **Its exponent facts**: the word at `kappa_base·g^7` (its parameter `1`) is `g^e`, `e < 25` (a table's log height,
at most `24`, `B1.VerifySub.SizesOk.heights24`); `gmv` (`4`) is `g^stackLog`, `stackLog ≤ 30`; `g_n` (`6`) is
`g^linkRows`, `linkRows ≤ 24`; `g_log_mem` (`8`) is `g^logMemory`, `logMemory ≤ 30`. -/
def expFacts : List (String × ℕ × Option ℕ × ℕ) :=
  [(name% «check_stack_terminal», 1, some 7, 25), (name% «check_stack_terminal», 4, none, 31),
    (name% «check_stack_terminal», 6, none, 25), (name% «check_stack_terminal», 8, none, 31)]

/-- The stack blocks some sent column of the link targets (`SENT_TARGET` below `N_STK_BLOCKS`). -/
def sentBlocks : List ℕ := [3, 4, 10, 11, 12, 13, 19, 20, 24, 25, 26, 27, 28, 34, 35, 36, 37, 38, 39, 40, 41, 42]

/-- **Its dimension facts**, both bounded by `g_n` (`6`, `g^linkRows`): each table's height source
`kappa_base[g^(2 + t)]` (`1`), and the kappas `kaps[g^b]` (`3`) of `sentBlocks`, each a table's column, of its log height. -/
def dimFacts : List (String × ℕ × ℕ × List (ℕ × ℕ)) :=
  [(name% «check_stack_terminal», 1, 6, [(2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)]),
    (name% «check_stack_terminal», 3, 6, [(3, 0), (4, 0), (10, 0), (11, 0), (12, 0), (13, 0), (19, 0), (20, 0), (24, 0), (25, 0), (26, 0), (27, 0), (28, 0), (34, 0), (35, 0), (36, 0), (37, 0), (38, 0), (39, 0), (40, 0), (41, 0), (42, 0)])]

end

end LeanVM.Guest.CoreMode.Own.check_stack_terminal
