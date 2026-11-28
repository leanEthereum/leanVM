module

public import NativeVm.Math.Tables.Model

/-!
# The tables' rows as the loop reads them

The rows `tableTerms` folds over, `tablesW.zip (heights.zip (forms.zip weights))`, element by
element (`rows_get`), the tables' data the code holds as literals (`tablesW_opcode`,
`tablesW_width`, `tablesW_nConstraints`), and `tableTerms` as a fold over a list then a `pure`
(`tableTerms_eq`).
-/

@[expose] public section

namespace NativeVm.Math.Tables

open NativeVm.Model LeanVM.Parameters

/-- The tables' widths (`tableWidths`). -/
def widths : List Nat := [13, 13, 7, 14, 14, 92]

theorem tablesW_size : tablesW.size = 6 := by
  rw [← Array.length_toList, tablesW_toList]; rfl

theorem tablesW_get (k : Nat) :
    tablesW.getD k default = (LeanVM.Protocol.Verifier.tables.map TableW.ofTable).getD k default := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, tablesW_toList, List.getD_eq_getElem?_getD]

theorem tablesW_opcode {k : Nat} (hk : k < 6) : (tablesW.getD k default).opcode = k := by
  rw [tablesW_get]
  interval_cases k <;> rfl

theorem tablesW_width {k : Nat} (hk : k < 6) : (tablesW.getD k default).width = widths.getD k 0 := by
  rw [tablesW_get]
  interval_cases k <;> decide

theorem tablesW_nConstraints {k : Nat} (hk : k < 4) : (tablesW.getD k default).nConstraints = 0 := by
  rw [tablesW_get]
  interval_cases k <;> simp [LeanVM.Protocol.Verifier.tables, TableW.ofTable,
    LeanVM.Protocol.Verifier.Table.nConstraints]

theorem getD_eq_getElem' {α : Type} (xs : Array α) (d : α) {i : Nat} (h : i < xs.size) :
    xs.getD i d = xs[i] := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]

/-- The rows' count. -/
theorem rows_length {heights : Array Nat} {forms : Array (Array FormW)} {weights : Array EW}
    (hh : heights.size = 6) (hf : forms.size = 6) (hw : weights.size = 6) :
    (tablesW.zip (heights.zip (forms.zip weights))).toList.length = 6 := by
  simp [tablesW_size, hh, hf, hw]

/-- **Row `k`.** -/
theorem rows_get {heights : Array Nat} {forms : Array (Array FormW)} {weights : Array EW}
    (hh : heights.size = 6) (hf : forms.size = 6) (hw : weights.size = 6) {k : Nat}
    (hk : k < (tablesW.zip (heights.zip (forms.zip weights))).toList.length) :
    (tablesW.zip (heights.zip (forms.zip weights))).toList[k] =
      (tablesW.getD k default, heights.getD k 0, forms.getD k #[], weights.getD k 0) := by
  rw [rows_length hh hf hw] at hk
  rw [Array.getElem_toList, Array.getElem_zip, Array.getElem_zip, Array.getElem_zip,
    getD_eq_getElem' _ _ (by rw [tablesW_size]; exact hk), getD_eq_getElem' _ _ (by omega),
    getD_eq_getElem' _ _ (by omega), getD_eq_getElem' _ _ (by omega)]

/-- `tableTerms` as the fold over the rows' list, then its result. -/
theorem tableTerms_eq (cp fp point : Array EW) (rows : Array (TableW × Nat × Array FormW × EW)) :
    tableTerms cp fp point rows = (rows.toList.foldlM (tableTermsStep cp fp point) (0, 0, #[]) >>=
      fun r ↦ pure (r.2.1, r.2.2)) := by
  unfold tableTerms
  rw [Array.foldlM_toList]

/-- One table of `tableTerms`, its row's parts named. -/
theorem tableTermsStep_eq (cp fp point : Array EW) (cursor : Nat) (final : EW)
    (out : Array (Array EW × Array EW)) (table : TableW) (height : Nat) (forms : Array FormW)
    (weight : EW) :
    tableTermsStep cp fp point (cursor, final, out) (table, height, forms, weight) =
      (readScalars table.width >>= fun evaluations ↦ pure (cursor + table.nConstraints,
        final + weight * (dot (cp.extract cursor (cursor + table.nConstraints))
          (constraintsW table.opcode evaluations) + dot fp (forms.map (·.evaluate evaluations))),
        out.push (point.extract 0 height, evaluations))) := rfl

end NativeVm.Math.Tables
