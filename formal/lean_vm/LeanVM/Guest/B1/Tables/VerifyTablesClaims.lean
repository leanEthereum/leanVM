/-
  LeanVM.Guest.B1.Tables.VerifyTablesClaims

  The table sumcheck's claims over the six tables, as lists: their columns, values and points.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesTerms
public import LeanVM.Guest.B1.Tables.VerifyTablesReads

/-!
# The tables' claims

Over the six tables, with each table's evaluations the guest's (`vtEvalVars`, read through `ρ`),
the claims `ttVal` collects (`ttVal_snd`) are on the tables' columns in order, their values the
evaluations in order, and claim `j`'s point the point's first `h` coordinates of its table
`vtTableOf[j]` (`vt_tc`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The table of each evaluation. -/
def vtTableOf : List ℕ := (List.range 6).flatMap fun t => List.replicate (vtEvalVars.getD t []).length t

theorem vt_widths : ∀ t < 6, (vtEvalVars.getD t []).length = (tables.getD t default).width ∧
    (tables.getD t default).opcode = t := by decide +kernel

theorem vt_evalVars_flatten : vtEvalVars.flatten = evVal := by decide +kernel

theorem vt_evalVars_length : vtEvalVars.length = 6 := rfl

theorem rowClaims_column (pt : List E) (q : (Table × ℕ × List Form × E) × List E) :
    (rowClaims pt q).map (·.column) =
      (List.range q.2.length).map (globalColumnBases.getD q.1.1.opcode 0 + ·) := by
  simp only [rowClaims, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem rowClaims_value (pt : List E) (q : (Table × ℕ × List Form × E) × List E) :
    (rowClaims pt q).map (·.value) = q.2 := by
  simp only [rowClaims, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem rowClaims_point (pt : List E) (q : (Table × ℕ × List Form × E) × List E) :
    (rowClaims pt q).map (·.point) = List.replicate q.2.length (pt.take q.1.2.1) := by
  simp only [rowClaims, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The rows over the six tables, by index. -/
theorem vt_rows_flatMap {β : Type} (X : List (ℕ × List Form × E)) (hX : X.length = 6)
    (evss : List (List E)) (he : evss.length = 6)
    (g : (Table × ℕ × List Form × E) × List E → List β) :
    (List.zip (List.zip tables X) evss).flatMap g = (List.range 6).flatMap fun t =>
      g ((tables.getD t default, X.getD t default), evss.getD t []) := by
  rw [List.flatMap_def, vt_zip_map_range _ _ default [] g (by simp [hX, tables_length']) he,
    List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun t ht => ?_)
  have ht' := List.mem_range.mp ht
  congr 2
  rw [List.getD_eq_getElem _ _ (by simp [hX, tables_length']; omega), List.getElem_zip,
    List.getD_eq_getElem _ _ (by simp [tables_length']; omega),
    List.getD_eq_getElem _ _ (by simp [hX]; omega)]

/-- The tables' claims, at the guest's evaluations. -/
def vtTc (pt : List E) (X : List (ℕ × List Form × E)) (ρ : ℕ → E) : List ColumnClaim :=
  (List.zip (List.zip tables X) (vtEvalVars.map (·.map ρ))).flatMap (rowClaims pt)

/-- **The tables' claims**: their columns, values and points. -/
theorem vt_tc (pt : List E) (X : List (ℕ × List Form × E)) (hX : X.length = 6) (ρ : ℕ → E) :
    (vtTc pt X ρ).map (·.column) =
        tables.flatMap (fun t ↦ (List.range t.width).map (globalColumnBases.getD t.opcode 0 + ·)) ∧
      (vtTc pt X ρ).map (·.value) = evVal.map ρ ∧
      (vtTc pt X ρ).map (·.point) = vtTableOf.map fun t => pt.take (X.getD t default).1 := by
  have hel : (vtEvalVars.map (·.map ρ)).length = 6 := by simp [vt_evalVars_length]
  have hget : ∀ t < 6, (vtEvalVars.map (·.map ρ)).getD t [] = (vtEvalVars.getD t []).map ρ :=
    fun t ht => by
      rw [List.getD_eq_getElem _ _ (by simp [vt_evalVars_length]; omega), List.getElem_map,
        List.getD_eq_getElem _ _ (by simp [vt_evalVars_length]; omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [vtTc, List.map_flatMap, vt_rows_flatMap X hX _ hel, tables_flatMap_fin]
    simp only [rowClaims_column]
    rw [List.flatMap_def, List.flatMap_def, show List.range 6 = (List.finRange 6).map (·.val) by
      decide, List.map_map]
    refine congrArg List.flatten (List.map_congr_left fun t _ => ?_)
    simp only [Function.comp_apply, hget t t.2, List.length_map, (vt_widths t t.2).1]
  · rw [vtTc, List.map_flatMap, vt_rows_flatMap X hX _ hel]
    simp only [rowClaims_value]
    rw [← vt_evalVars_flatten, List.map_flatten, List.flatMap_def]
    refine congrArg List.flatten ?_
    apply List.ext_getElem (by simp [vt_evalVars_length])
    intro t h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range, hget t h1, List.getElem_map,
      List.getD_eq_getElem _ _ (by simp [vt_evalVars_length]; omega)]
  · rw [vtTc, List.map_flatMap, vt_rows_flatMap X hX _ hel]
    simp only [rowClaims_point]
    rw [vtTableOf, List.map_flatMap, List.flatMap_def, List.flatMap_def]
    refine congrArg List.flatten (List.map_congr_left fun t ht => ?_)
    rw [List.map_replicate, hget t (List.mem_range.mp ht), List.length_map]

end
end LeanVM.Guest.B1.VerifySub
