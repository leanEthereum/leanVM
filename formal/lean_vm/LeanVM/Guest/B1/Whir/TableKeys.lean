/-
  LeanVM.Guest.B1.Whir.TableKeys

  The helpers' tables' names are their entries' numbers: membership decided by numbers.
-/

module

public import LeanVM.Guest.B1.Whir.TableKeysLp
public import LeanVM.Guest.B1.Whir.TableKeysLq
public import LeanVM.Guest.B1.Whir.TableKeysLr

/-!
# The helpers' tables by numbers

Every entry of `lpTable`, `lqTable` and `lrTable` is named by its numbers (`lp_names`,
`lq_names`, `lr_names`, by the kernel, once, a module each), as the template names the
specialization a level calls (`osPositionsName_eq`, ...). So an entry of a level's name is in a table exactly when its
numbers are (`mem_name_key`), which the kernel decides without building a string.
-/

namespace LeanVM.Guest.B1.Whir

@[expose] public section

theorem osPositionsName_eq (lv : OsLv) :
    osPositionsName lv = keyStr "level_positions__L" [lv.squeezes, lv.depth, lv.capDepth] := rfl

theorem osResidualName_eq (lv : OsLv) :
    osResidualName lv = keyStr "level_residual__L" [lv.queries, lv.logCols, lv.folds, lv.highBits] :=
  rfl

theorem osQueriesName_eq (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    osQueriesName c lvl lv = keyStr "level_queries__L"
      [lv.queries, if lvl = 0 then 1 else 0, lv.folds, lv.leafCells, lv.depth, lv.capDepth,
        if lvl = c.yrLevel then lv.logCols else 0, if lvl = c.yrLevel then c.yrLen + lv.folds else 0,
        if lvl = c.yrLevel then c.yrLog + 1 else 0, if lvl = c.yrLevel then 1 else 0] := rfl

theorem lp_mem (lv : OsLv) (loop : String) :
    (osPositionsName lv, lv.squeezes, loop, lv.depth, lv.capDepth) ∈ lpTable ↔
      (lv.squeezes, loop, lv.depth, lv.capDepth) ∈ lpTable.map (·.2) := by
  rw [osPositionsName_eq]
  exact mem_name_key lpTable (keyStr "level_positions__L") lpKey lp_names
    (lv.squeezes, loop, lv.depth, lv.capDepth)

theorem lr_mem (lv : OsLv) (l1 l2 : String) :
    (osResidualName lv, lv.queries, lv.logCols, lv.folds, lv.highBits, l1, l2) ∈ lrTable ↔
      (lv.queries, lv.logCols, lv.folds, lv.highBits, l1, l2) ∈ lrTable.map (·.2) := by
  rw [osResidualName_eq]
  exact mem_name_key lrTable (keyStr "level_residual__L") lrKey lr_names
    (lv.queries, lv.logCols, lv.folds, lv.highBits, l1, l2)

theorem lq_mem (c : OsCfg) (lvl : ℕ) (lv : OsLv) :
    (osQueriesName c lvl lv, lv.queries, (if lvl = 0 then 1 else 0), lv.folds, lv.leafCells, lv.depth,
      lv.capDepth, (if lvl = c.yrLevel then lv.logCols else 0),
      (if lvl = c.yrLevel then c.yrLen + lv.folds else 0), (if lvl = c.yrLevel then c.yrLog + 1 else 0),
      (if lvl = c.yrLevel then 1 else 0)) ∈ lqTable ↔
    (lv.queries, (if lvl = 0 then 1 else 0), lv.folds, lv.leafCells, lv.depth, lv.capDepth,
      (if lvl = c.yrLevel then lv.logCols else 0), (if lvl = c.yrLevel then c.yrLen + lv.folds else 0),
      (if lvl = c.yrLevel then c.yrLog + 1 else 0), (if lvl = c.yrLevel then 1 else 0)) ∈
      lqTable.map (·.2) := by
  rw [osQueriesName_eq]
  exact mem_name_key lqTable (keyStr "level_queries__L") lqKey lq_names
    (lv.queries, (if lvl = 0 then 1 else 0), lv.folds, lv.leafCells, lv.depth, lv.capDepth,
      (if lvl = c.yrLevel then lv.logCols else 0), (if lvl = c.yrLevel then c.yrLen + lv.folds else 0),
      (if lvl = c.yrLevel then c.yrLog + 1 else 0), (if lvl = c.yrLevel then 1 else 0))

/-- A level's `level_positions` loop, by its numbers. -/
def lpLoopK (lv : OsLv) : String :=
  ((lpTable.find? fun e => lpKey e.2 == [lv.squeezes, lv.depth, lv.capDepth]).map (·.2.2.1)).getD ""

/-- A level's `level_residual` loops, by its numbers. -/
def lrLoopsK (lv : OsLv) : String × String :=
  ((lrTable.find? fun e => lrKey e.2 == [lv.queries, lv.logCols, lv.folds, lv.highBits]).map
    (·.2.2.2.2.2)).getD ("", "")

theorem lpLoopOf_eq (lv : OsLv) : lpLoopOf (osPositionsName lv) = lpLoopK lv := by
  unfold lpLoopOf lpLoopK
  rw [osPositionsName_eq, find_name_key_dec lpTable _ keyStr_inj lpKey lp_names]

theorem lrLoopsOf_eq (lv : OsLv) : lrLoopsOf (osResidualName lv) = lrLoopsK lv := by
  unfold lrLoopsOf lrLoopsK
  rw [osResidualName_eq, find_name_key_dec lrTable _ keyStr_inj lrKey lr_names]

end
end LeanVM.Guest.B1.Whir
