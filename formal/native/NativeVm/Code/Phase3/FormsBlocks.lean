module

public import NativeVm.Code.Phase3.FormsModel
public import NativeVm.Code.Phase3.FormsDataPush
public import NativeVm.Code.Phase3.FormsDataPull
public import NativeVm.Code.Phase3.FormsDataCount

/-!
# The bus forms of a side: the data are the layout's blocks

`sideD side` is the side's literal data; a side's table blocks (`sideBlocks`, from `busBlocks`
whatever the heights and rows) have the data's owners and entries (`sideBlocks_ents`), so each
block's form is the data's (`blockForm_eq_buildF`).
-/

@[expose] public section

namespace NativeVm.Code.P3

open NativeVm.Model NativeVm.Equiv LeanVM.Parameters LeanVM.Protocol.Verifier

/-- A side's data. -/
def sideD (side : Nat) : List DBlk := if side = 0 then pushD else if side = 1 then pullD else countD

theorem dprojW_eq (b : DBlk) : dprojW b = (b.1, entsW b.2) := rfl

theorem blockEnts_ofForm (h r o : Nat) (c : List Form) :
    blockEnts ⟨h, r, (c.map FormW.ofForm).toArray, o⟩ = entsS c := by
  simp [blockEnts, entsS, FormW.ofForm, List.zipIdx_map, List.flatMap_map, Function.comp_def]

theorem blockEnts_ofForm1 (h r o : Nat) (f : Form) :
    blockEnts ⟨h, r, #[FormW.ofForm f], o⟩ = entsS [f] := blockEnts_ofForm h r o [f]

theorem tablesW_toList' : tablesW.toList = tables.map TableW.ofTable := by simp [tablesW]

/-- **The blocks of a side are the data's**: owners and entries. -/
theorem sideBlocks_ents {layout : LayoutW} {rows : Array Nat} {side : Nat}
    (h : busBlocks layout.tableLogHeights rows = (layout.push, layout.pull, layout.count))
    (hside : side < 3) :
    (sideBlocks layout side).toList.map (fun b ↦ (b.owner, blockEnts b)) =
      (sideD side).map fun b ↦ (b.1, entsW b.2) := by
  have h1 := congrArg (·.1) h
  have h2 := congrArg (·.2.1) h
  have h3 := congrArg (·.2.2) h
  simp only [Model.busBlocks] at h1 h2 h3
  unfold sideBlocks sideD
  rcases (show side = 0 ∨ side = 1 ∨ side = 2 by omega) with rfl | rfl | rfl
  · simp only [ite_true, ← h1]
    rw [← List.map_congr_left (fun b _ ↦ dprojW_eq b), ← pushD_eq, pushS]
    simp [Array.toList_flatMap, tablesW_toList', TableW.ofTable, List.flatMap_map, List.map_flatMap,
      blockEnts_ofForm, Function.comp_def]
  · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, ← h2]
    rw [← List.map_congr_left (fun b _ ↦ dprojW_eq b), ← pullD_eq, pullS]
    simp [Array.toList_flatMap, tablesW_toList', TableW.ofTable, List.flatMap_map, List.map_flatMap,
      blockEnts_ofForm, Function.comp_def]
  · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false, ← h3]
    rw [← List.map_congr_left (fun b _ ↦ dprojW_eq b), ← countD_eq, countS]
    simp [Array.toList_flatMap, tablesW_toList', TableW.ofTable, List.flatMap_map, List.map_flatMap,
      blockEnts_ofForm1, Function.comp_def]

end NativeVm.Code.P3
