/-
  LeanVM.Guest.B1.Tables.Vt.SpecLayout

  The layout `verify_tables` runs against, from the specification's side: the bytecode's
  log-size, the tables' heights and the three sides' blocks, table by table, and their sizes.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.SelsAll
public import LeanVM.Guest.B1.Tables.Interface
public import LeanVM.Guest.B1.Tables.Vt.FormsPad

/-!
# The layout (V:957-997)

For the row counts `rows` (six of them) and a bytecode of `2^23` words, `layoutOf`'s bytecode
log-size is `19`, its heights are `vtHt rows`, and each side's blocks are the tables' flushes in
table order, each at its table's height and row count (`vt_layout_push`, …). The sides' sizes are
the guest's `vtSizesP` (push and pull) and `vtSizesC` (count).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Complete (refSide refSide_eq refSideC sideSizes refCountColumns)

@[expose] public section

/-- Table `t`'s height. -/
def vtHt (rows : List ℕ) (t : ℕ) : ℕ := (tableHeightsOf rows).getD t 0

/-- Table `t`'s row count. -/
def vtRw (rows : List ℕ) (t : ℕ) : ℕ := rows.getD t 0

/-- The push side's table blocks. -/
def vtPushBlocks (rows : List ℕ) : List BusBlock :=
  (List.ofFn fun t : Fin 6 ↦ (refSide t .push).map fun c ↦
    (⟨vtHt rows t, vtRw rows t, c, t⟩ : BusBlock)).flatten

/-- The pull side's table blocks. -/
def vtPullBlocks (rows : List ℕ) : List BusBlock :=
  (List.ofFn fun t : Fin 6 ↦ (refSide t .pull).map fun c ↦
    (⟨vtHt rows t, vtRw rows t, c, t⟩ : BusBlock)).flatten

/-- The count side's blocks. -/
def vtCountBlocks (rows : List ℕ) : List BusBlock :=
  (List.ofFn fun t : Fin 6 ↦ (tables.getD t default).countColumns.map fun l ↦
    (⟨vtHt rows t, vtRw rows t, [Form.col l], t⟩ : BusBlock)).flatten

theorem vt_tableHeightsOf_length {rows : List ℕ} (hr : rows.length = 6) :
    (tableHeightsOf rows).length = 6 := by
  simp [tableHeightsOf, hr, tableLogFloors]

theorem vt_zip_rows {rows : List ℕ} (hr : rows.length = 6) :
    List.zip tables (List.zip (tableHeightsOf rows) rows) =
      List.ofFn fun t : Fin 6 ↦ (tables.getD t default, vtHt rows t, vtRw rows t) := by
  apply List.ext_getElem
  · simp [vt_tableHeightsOf_length hr, hr, tables]
  · intro i h1 h2
    simp only [List.getElem_zip, List.getElem_ofFn, vtHt, vtRw]
    have hi : i < 6 := by simpa using h2
    rw [List.getD_eq_getElem _ _ (by simp [tables]; omega),
      List.getD_eq_getElem _ _ (by rw [vt_tableHeightsOf_length hr]; omega),
      List.getD_eq_getElem _ _ (by omega)]

/-- **`layoutOf`'s blocks.** -/
theorem vt_layout_blocks (bc : List K) (lm : ℕ) {rows : List ℕ} (hr : rows.length = 6) :
    (layoutOf bc lm rows).push = vtPushBlocks rows ∧ (layoutOf bc lm rows).pull = vtPullBlocks rows ∧
      (layoutOf bc lm rows).count = vtCountBlocks rows := by
  simp only [layoutOf, busBlocks, vt_zip_rows hr, List.flatMap, List.map_ofFn]
  refine ⟨?_, ?_, ?_⟩ <;> congr 1

theorem vt_layout_logBytecode (bc : List K) (lm : ℕ) (rows : List ℕ) (hbc : bc.length = 2 ^ 23) :
    (layoutOf bc lm rows).logBytecode = 19 := by
  simp only [layoutOf, hbc]
  rw [Nat.log2_two_pow]
  rfl

theorem vt_layout_logMemory (bc : List K) (lm : ℕ) (rows : List ℕ) :
    (layoutOf bc lm rows).logMemory = lm := rfl

theorem vt_countColumns (t : Fin 6) :
    (tables.getD t default).countColumns = vtCountCols.getD t [] := by
  rw [refCountColumns t]
  revert t
  decide +kernel

/-- The push side's sizes are the guest's. -/
theorem vt_sizes_push {rows : List ℕ} (lm : ℕ) :
    sideSizes [0, lm, 19] (vtPushBlocks rows) = vtSizesP lm (vtHt rows) := by
  simp only [sideSizes, vtPushBlocks, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil]
  rfl

/-- The pull side's sizes are the push side's. -/
theorem vt_sizes_pull {rows : List ℕ} (lm : ℕ) :
    sideSizes [0, lm, 19] (vtPullBlocks rows) = vtSizesP lm (vtHt rows) := by
  simp only [sideSizes, vtPullBlocks, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil]
  rfl

/-- The count side's sizes are the guest's. -/
theorem vt_sizes_count {rows : List ℕ} :
    sideSizes [] (vtCountBlocks rows) = vtSizesC (vtHt rows) := by
  simp only [sideSizes, vtCountBlocks, vt_countColumns, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil, List.nil_append]
  rfl

end
end LeanVM.Guest.B1.Tables
