module

public import NativeVm.Equiv.LayoutBuild
public import NativeVm.Equiv.BusPure
public import NativeVm.Model.Tables

/-!
# Phase 4's pure steps: the model's are the statement's

Through `EW.toE`: a table's constraints (`constraintsW_toSpec`: `JUMP`'s are `jumpConstraints`, the
others none, for each of the six tables of `tables`, the columns read by the same
`columnIndexByName` on both sides, nothing evaluated), the constraint count (`nConstraints_eq`), the
tables' weights at the point (`tableWeights_toSpec`) and the column claims of the tables'
evaluations (`tableColumnClaims_toSpec`), a table's point and evaluations read by `convEval`.
-/

@[expose] public section

namespace NativeVm.Model

open NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol

/-- An option read through `EW.toE`, a missing one `0`. -/
theorem toE_optionGetD (o : Option EW) : (o.getD 0).toE = (o.map EW.toE).getD 0 := by
  cases o <;> simp

/-- The constraints of a table of the statement. -/
theorem constraintsW_toSpec {t : Verifier.Table} (ht : t ∈ Verifier.tables) (row : Array EW) :
    (constraintsW t.opcode row).toList.map EW.toE = t.constraints (row.toList.map EW.toE) := by
  simp only [Verifier.tables, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [constraintsW, Verifier.jumpConstraints, toE_optionGetD, Verifier.opXor, Verifier.opMul,
      Verifier.opSet, Verifier.opDeref, Verifier.opJump, Verifier.opKeccak]

/-- The tables' constraint count. -/
theorem nConstraints_eq :
    (tablesW.map (·.nConstraints)).sum = (Verifier.tables.map Verifier.Table.nConstraints).sum := by
  rw [← Array.sum_toList]; simp [tablesW_toList, TableW.ofTable, Function.comp_def]

/-- `tableWeights`. -/
theorem tableWeights_toSpec (heights : Array ℕ) (eq point : Array EW) :
    (tableWeights heights eq point).toList.map EW.toE =
      Verifier.tableWeights heights.toList (eq.toList.map EW.toE) (point.toList.map EW.toE) := by
  unfold tableWeights Verifier.tableWeights
  rw [← Array.foldl_toList, foldl_hom (fun a : Array EW ↦ a.toList.map EW.toE)
    (Prod.map EW.toE id) (g := fun weights (p : E × ℕ) ↦ List.zipWith (fun weight height ↦
      weight * if p.2 < height then 1 + (eq.toList.map EW.toE).getD p.2 0 + p.1 else p.1)
        weights heights.toList)]
  · simp [Array.toList_zipIdx, List.zipIdx_map]
  · intro w p
    simp only [Array.toList_zipWith, List.map_zipWith, List.zipWith_map_left]
    congr 1; funext x y
    by_cases hy : p.2 < y <;> simp [hy, toE_optionGetD]

/-- A table's point and evaluations as the statement's. -/
def convEval (e : Array EW × Array EW) : List E × List E :=
  (e.1.toList.map EW.toE, e.2.toList.map EW.toE)

/-- `tableColumnClaims`. -/
theorem tableColumnClaims_toSpec (evaluations : Array (Array EW × Array EW)) :
    (tableColumnClaims evaluations).toList.map ColumnClaimW.toSpec =
      Verifier.tableColumnClaims (evaluations.toList.map convEval) := by
  simp [tableColumnClaims, Verifier.tableColumnClaims, globalColumnBasesW, ColumnClaimW.toSpec,
    Array.toList_flatMap, List.map_flatMap, List.zip_map_right, List.flatMap_map,
    Array.toList_zipIdx, List.zipIdx_map, Function.comp_def, convEval]

/-- `extract` as `drop` then `take`. -/
theorem toList_extract' {α : Type} (a : Array α) (i j : ℕ) :
    (a.extract i j).toList = (a.toList.drop i).take (j - i) := by
  simp [Array.toList_extract, List.extract_eq_take_drop]

end NativeVm.Model
