/-
  LeanVM.Protocol.Relation.Link.Group

  The drawn group's count, `LinkSummandFacts.group`, case by case.
-/

module

public import LeanVM.Protocol.Relation.Link.GroupBase
public import LeanVM.Protocol.Relation.Link.GroupOneHot

/-!
# The drawn group's count

`linkGroup_of_cases`: the relation failing, the draws that escape the group's doom are at most
`linkGroupError·|E|^N`, from the count of each way it fails:

* `¬ KeccakRel`: the Keccak defect dooms every draw (`keccakCarry_of_not_rel`);
* a pointer not one-hot: `hOneHot`, proved by `card_notDoom_of_not_oneHot` (`GroupOneHot.lean`,
  `linkGroup_of_jump_links`);
* a `JUMP` constraint failing: `hJump` (`GroupJump.lean`);
* the pointers one-hot and the constraints holding, the state link or a lookup failing: `hLinks`
  (`GroupLinks.lean`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

open Classical

/-- **The drawn group's count from its cases**, in `LinkSummandFacts.group`'s form. -/
theorem linkGroup_of_cases {layout : Layout} {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks)
    (hOneHot : ¬ PointersOneHot layout q chunks →
      (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks)
    (hJump : ¬ ConstraintsHold layout q →
      (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks)
    (hLinks : PointersOneHot layout q chunks → ConstraintsHold layout q → KeccakRel layout q →
      ¬ (StateHolds layout q chunks ∧ MemoryHolds layout q chunks ∧ ProgramHolds layout q chunks) →
      (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks) :
    (¬ LinkRel layout q ∨ ¬ KeccakRel layout q) →
    (univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
      ¬ RoundDoom True (linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail)
        (IndexCarry layout q chunks (linkB layout chunks q) ((List.ofFn v).headD 0)
          (List.ofFn v).tail)
        (indexClaim layout chunks (List.ofFn v).tail) []).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks := by
  intro hfail
  show (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤ _
  by_cases hk : KeccakRel layout q
  · have hl : ¬ LinkRel layout q := hfail.resolve_right (not_not.mpr hk)
    by_cases ho : PointersOneHot layout q chunks
    · by_cases hc : ConstraintsHold layout q
      · refine hLinks ho hc hk fun ⟨hs, hm, hp⟩ ↦ hl ⟨chunks, hch, ho, hs, hm, hp, hc⟩
      · exact hJump hc
    · exact hOneHot ho
  · have hK := keccakCarry_of_not_rel hk
    rw [filter_false_of_mem fun v _ ↦ not_not.mpr (groupDoom_of_keccak hK v), card_empty]
    exact Nat.zero_le _

/-- **The drawn group's count** at an announced layout, the not-one-hot case proved
(`card_notDoom_of_not_oneHot`): what is left are the `JUMP` constraints' and the links' counts. -/
theorem linkGroup_of_jump_links {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks)
    (hJump : ¬ ConstraintsHold layout q →
      (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks)
    (hLinks : PointersOneHot layout q chunks → ConstraintsHold layout q → KeccakRel layout q →
      ¬ (StateHolds layout q chunks ∧ MemoryHolds layout q chunks ∧ ProgramHolds layout q chunks) →
      (univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
        linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks) :
    (¬ LinkRel layout q ∨ ¬ KeccakRel layout q) →
    (univ.filter fun v : Fin (linkDrawn layout chunks + 1) → E ↦
      ¬ RoundDoom True (linkIdx layout chunks q ((List.ofFn v).headD 0) (List.ofFn v).tail)
        (IndexCarry layout q chunks (linkB layout chunks q) ((List.ofFn v).headD 0)
          (List.ofFn v).tail)
        (indexClaim layout chunks (List.ofFn v).tail) []).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks :=
  linkGroup_of_cases q hch (card_notDoom_of_not_oneHot hA q hch) hJump hLinks

end

end LeanVM.Protocol.Relation
