/-
  LeanVM.Guest.Memory.GuestWf

  The guest's core IR is well formed (`Program.Wf`): every `callIf` names a loop helper taking
  its arguments, and every `match` and fused dispatch has at most `2^64 - 1` arms; so every
  derivation of its `Program.Rel` is an honest evaluation.
-/

module

public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.CoreData

/-!
# The guest is well formed

`Stmt.wfList` is evaluated by the kernel on the functions of `coreProgram`, a hundred at a time
(`wf_chunk`), and the chunks cover the program (`coreProgram_wf`).
-/

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- The functions of `coreProgram` from `100 * i`, a hundred of them, are well formed. -/
def WfChunk (i : ℕ) : Prop :=
  ((coreProgram.drop (100 * i)).take 100).all (fun fn => Stmt.wfList coreProgram fn.body) = true

set_option maxRecDepth 100000 in
theorem wf_chunk0 : WfChunk 0 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk1 : WfChunk 1 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk2 : WfChunk 2 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk3 : WfChunk 3 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk4 : WfChunk 4 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk5 : WfChunk 5 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk6 : WfChunk 6 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk7 : WfChunk 7 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk8 : WfChunk 8 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk9 : WfChunk 9 := by
  unfold WfChunk; decide +kernel

set_option maxRecDepth 100000 in
theorem wf_chunk10 : WfChunk 10 := by
  unfold WfChunk; decide +kernel

theorem wf_chunk : ∀ i < 11, WfChunk i := by
  intro i hi
  interval_cases i
  exacts [wf_chunk0, wf_chunk1, wf_chunk2, wf_chunk3, wf_chunk4, wf_chunk5, wf_chunk6, wf_chunk7,
    wf_chunk8, wf_chunk9, wf_chunk10]

/-- **The guest's core IR is well formed.** -/
theorem coreProgram_wf : coreProgram.Wf := by
  intro fn hfn
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hfn
  have hk' : k < 1043 := coreProgram_length ▸ hk
  have h := wf_chunk (k / 100) (by omega)
  unfold WfChunk at h
  rw [List.all_eq_true] at h
  refine h _ (List.mem_iff_getElem.mpr ⟨k % 100, ?_, ?_⟩)
  · simp only [List.length_take, List.length_drop]
    omega
  · simp only [List.getElem_take, List.getElem_drop]
    congr 1
    omega

end
end LeanVM.Guest
