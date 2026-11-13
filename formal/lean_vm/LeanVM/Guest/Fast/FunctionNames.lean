module

public import LeanVM.Guest.NameIndex
import Mathlib.Data.List.GetD

/-!
# The functions the decoder reads frames of, numbered

The decoder reads the witness off the frames of the functions that checked it, through a frame
map keyed by the function's name (`FrameMap`, `B1/Main/Frames.lean`). Its readers, made programs
of the cost machine, key it by a number instead (`NFrames`): **the function's index**, one past
its position in `coreProgram` (`main` is `1`), the index `certOf` and the replayed frame map's
entry table (`Located/ReplayFast.lean`) use, `nameIndex f` for the function named `f` (`nFns` for
no function, `Guest/NameIndex.lean`).

* `decoderFunctionName j`: the name of function `j` (`main`'s off the indices `1 ..< nFns`);
* `nameIndex_decoderFunctionName`: the index of function `j`'s name is `canonIndex j` (`j` on the
  indices, `1` off them), so a frame map keyed by name `V` and one keyed by index agree when the
  latter is `V` re-keyed (`fun j ↦ V (decoderFunctionName j)`) and reads its index through
  `canonIndex`; `decoderFunctionName_nameIndex`: a function's name is that of its index;
* the indices the readers name are generated (`Fast/FunctionIdx.lean`, `scripts/count/gen.py`):
  `idx*` and `name_*` (`main`'s callees whose witness is read, `da_verify`'s callees),
  `openStackedIdx m` (`open_stacked`'s specializations); the `opening_queries` specializations
  and their loop helpers are the table `osCallsTab`'s (`Fast/WhirTablesCheck.lean`).
-/

namespace LeanVM.Guest.Fast

open LeanVM.Parameters LeanVM.Guest.Core

@[expose] public section

/-- A frame map keyed by the functions' indices. -/
abbrev NFrames : Type := ℕ → List E → List E → Val

/-- Whether `j` is a function's index. -/
def isFunctionIndex (j : ℕ) : Bool := 1 ≤ j && j ≤ core_count%

/-- **The name of function `j`** (`main`'s off the indices). -/
noncomputable def decoderFunctionName (j : ℕ) : String :=
  if isFunctionIndex j then (coreProgram.getD (j - 1) default).name else "main"

/-- The index a frame map keyed by index reads for `j`: `j` itself, `main`'s off the indices. -/
def canonIndex (j : ℕ) : ℕ := if isFunctionIndex j then j else 1

theorem nameIndex_main : nameIndex "main" = 1 := by
  unfold nameIndex
  rw [show "main" = (coreProgram[0]'(by rw [coreProgram_length]; omega)).name by decide +kernel,
    findIdx_name_of_nodup coreProgram_names_nodup]

/-- **The index of function `j`'s name.** -/
theorem nameIndex_decoderFunctionName (j : ℕ) :
    nameIndex (decoderFunctionName j) = canonIndex j := by
  unfold decoderFunctionName canonIndex
  split
  · rename_i h
    simp only [isFunctionIndex, Bool.and_eq_true, decide_eq_true_eq] at h
    have hl : j - 1 < coreProgram.length := by rw [coreProgram_length]; omega
    unfold nameIndex
    rw [List.getD_eq_getElem _ _ hl, findIdx_name_of_nodup coreProgram_names_nodup hl]
    omega
  · exact nameIndex_main

/-- **A function's name is that of its index.** -/
theorem decoderFunctionName_nameIndex {f : String} (hf : f ∈ coreProgram.map (·.name)) :
    decoderFunctionName (nameIndex f) = f := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hl := coreProgram_length
  unfold nameIndex decoderFunctionName
  rw [findIdx_name_of_nodup coreProgram_names_nodup hi]
  simp only [isFunctionIndex, show 1 ≤ i + 1 ∧ i + 1 ≤ core_count% by omega, decide_true, Bool.and_self,
    ↓reduceIte, Nat.add_sub_cancel, List.getD_eq_getElem _ _ hi]

end
end LeanVM.Guest.Fast
