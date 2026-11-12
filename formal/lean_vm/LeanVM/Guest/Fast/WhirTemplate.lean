/-
  LeanVM.Guest.Fast.WhirTemplate

  `open_stacked`'s template's `level_queries` dispatches at each size and rate, which
  `scripts/whir-tables.lean` writes as `Fast/WhirTables.lean` and `Fast/WhirCalls.lean` checks.
-/

module

public import LeanVM.Guest.B1.Whir.Witness

/-!
# `open_stacked`'s dispatches

`osQCalls c`: each level's `level_queries` dispatch of the template at the configuration `c`, with
the level's index and row, from the state before its queries (`osPreQ`, `osQCallOf`); `osCfgAt j`
the table's configuration `j`. This module imports the template alone, so that the tables'
generator runs before the tables are checked.
-/

namespace LeanVM.Guest.Fast

open LeanVM.Guest.Core LeanVM.Guest.B1 LeanVM.Guest.B1.Whir

@[expose] public section

/-- The levels' `level_queries` dispatches from level `lvl` on, with the levels' indices and
rows, the state threaded as `osLevelsW` threads it. -/
def osQCallsFrom (c : OsCfg) : ℕ → List OsLv → OsSt → List (ℕ × OsLv × List V × List V)
  | _, [], _ => []
  | lvl, lv :: rest, s =>
    (lvl, lv, osQCallOf c lvl lv (osPreQ c lvl lv s)) :: osQCallsFrom c (lvl + 1) rest (osLevel c lvl lv s).2

/-- **The levels' `level_queries` dispatches** of the template at the configuration `c`. -/
def osQCalls (c : OsCfg) : List (ℕ × OsLv × List V × List V) := osQCallsFrom c 0 c.levels (osHead c).2

/-- The configuration at the table's index `j`: the size `j % 11` at the rate index `j / 11`. -/
def osCfgAt (j : ℕ) : OsCfg := osCfgR (j % 11) (j / 11)

end
end LeanVM.Guest.Fast
