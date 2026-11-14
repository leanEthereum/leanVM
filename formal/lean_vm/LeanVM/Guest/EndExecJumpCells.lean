/-
  LeanVM.Guest.EndExecJumpCells

  The jumps' cells on every node's reference run, and the deployed alignment's layout.
-/

module

public import LeanVM.Guest.EndExecChain

/-!
# The jumps' cells on every node's reference run

`jumpCells_at`: from the chained `match`es' arms on every node's reference run (`chainArmAt`), the top frame of every state of the track against a node's run holds what its jumps read (`Bridge.jumpCells_deployed`), what `EndExecX.JumpCellsAt alignA` asks once it reads the frame's pc. `alLayout_alignA`: the deployed alignment's entries are the compiled functions', its code theirs (`AlLayout`).
-/

namespace LeanVM.Guest.EndExec

open LeanVM.Guest LeanVM.Guest.Memory LeanVM.Guest.Bridge

public section

/-- **The jumps' cells on every node's reference run.** -/
theorem jumpCells_at : ∀ r : Ref, r.Ok → ∀ pc fp done e st,
    RefTrack alignA r pc fp (done, e :: st) → JumpCells r.img alignA e pc := fun r hr _ _ _ _ _ h ↦ by
  obtain ⟨rd, hH, hX⟩ := hr.honest
  exact jumpCells_deployed hr.name hH hX.covers (chainArmAt r hr) h

/-- **The deployed alignment's layout**: each function's entry its compiled function's, its code
theirs. -/
theorem alLayout_alignA : AlLayout alignA := fun f _ hf ↦ by
  obtain ⟨j, hj⟩ := B2C.idxOf_of_find hf
  obtain ⟨i, rfl, -, -, -, -, -, -, -, h2⟩ := B2C.fn_of_idx hj
  have hm := End.fnOf_mem h2
  refine ⟨fnOf (i + 1), hm, ?_, B2C.entryOf_of hj, ?_⟩
  · rw [entOf, alignA_of hj]; rfl
  · rw [alignA_of hj]
    exact (CompiledFunction.length_code (CompiledFunction.wellChunked_of_mem hm)).le

end

end LeanVM.Guest.EndExec
