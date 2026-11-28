/-
  LeanVM.Protocol.Relation.Link.GroupLinksNonzero

  A draw where the drawn group's polynomial is nonzero, when the pointers are one-hot and a link
  fails.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupLinksState
public import LeanVM.Protocol.Relation.Link.GroupLinksProgram
public import LeanVM.Protocol.Relation.Link.GroupLinksMemory

/-!
# The nonzero draw

`exists_groupF_ne`: by cases, the state link failing (`lk_state_ne`), else the program lookup
failing (`lkRest_ne_of_program`), else the memory lookup failing (`lkRest_ne_of_memory`). Once the
state link holds, `groupF = −lkRest` (`lk_groupF_split`, `lk_state_zero`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

/-- **A failing link has a draw where the drawn group's polynomial is nonzero.** -/
theorem exists_groupF_ne {bytecode : List K} {layout : Layout} {ρ : ℕ} (hA : Announced bytecode layout ρ)
    {μ : ℕ} (q : Column μ) {chunks : Chunks} (hch : Chunks.new (linkWidth layout) = some chunks)
    (hone : PointersOneHot layout q chunks)
    (hl : ¬ (StateHolds layout q chunks ∧ MemoryHolds layout q chunks ∧ ProgramHolds layout q chunks)) :
    ∃ x0, groupF layout chunks q x0 ≠ 0 := by
  have hch' : Chunks.new chunks.width = some chunks := by rw [Chunks.new_width hch]; exact hch
  have hT : linkCycles layout < 2 ^ chunks.width := linkCycles_lt hch
  have hW : layout.logBytecode ≤ chunks.width := by
    rw [Chunks.new_width hch, linkWidth, pointerWidth]
    exact le_max_of_le_left (le_max_right _ _)
  by_cases hs : StateHolds layout q chunks
  · have hrest : ∀ x : lkp_Vals, lkRest layout chunks q (lkp_set layout chunks x) ≠ 0 →
        groupF layout chunks q (lkp_set layout chunks x) ≠ 0 := by
      intro x hx
      rw [lk_groupF_split hA q hch' hone, lk_state_zero hA q hch' hT hone hs, zero_sub, neg_ne_zero]
      exact hx
    by_cases hp : ProgramHolds layout q chunks
    · have hm : ¬ MemoryHolds layout q chunks := fun hm ↦ hl ⟨hs, hm, hp⟩
      obtain ⟨x, hx⟩ := lkRest_ne_of_memory hA q hch' hone hp hm
      exact ⟨_, hrest x hx⟩
    · obtain ⟨x, hx⟩ := lkRest_ne_of_program hA q hch' hW hone hp
      exact ⟨_, hrest x hx⟩
  · obtain ⟨x, hx⟩ := lk_state_ne hA q hch' hT hone hs
    exact ⟨_, hx⟩

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.exists_groupF_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.exists_groupF_ne
