/-
  LeanVM.Protocol.Relation.Link.GroupLinksEnd

  The failing links' count, and the link's interface for the knowledge-soundness assembly.
-/

module

public import LeanVM.Protocol.Relation.Link
public import LeanVM.Protocol.Relation.Link.GroupLinksNonzero

/-!
# The link's interface

`card_notDoom_of_links`: when the pointers are one-hot and a link fails, at most
`linkGroupError·|E|^N` draws escape the drawn group's doom (`card_notDoom_of_groupF` at the draw
`exists_groupF_ne` gives). It is `linkIfaceOfLinks`' `hLinks`, so `linkIface` is the link's
interface (`Relation/Link.lean`, `Iface.lean`).
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Link

@[expose] public section

open Classical in
/-- **The failing links' count.** -/
theorem card_notDoom_of_links {bytecode : List K} {layout : Layout} {ρ : ℕ}
    (hA : Announced bytecode layout ρ) {μ : ℕ} (q : Column μ) {chunks : Chunks}
    (hch : Chunks.new (linkWidth layout) = some chunks) (hone : PointersOneHot layout q chunks)
    (_hc : ConstraintsHold layout q) (_hk : KeccakRel layout q)
    (hl : ¬ (StateHolds layout q chunks ∧ MemoryHolds layout q chunks ∧ ProgramHolds layout q chunks)) :
    (Finset.univ.filter fun v ↦ ¬ GroupDoomAt layout q chunks v).card ≤
      linkGroupError layout chunks * Fintype.card E ^ linkDrawn layout chunks :=
  card_notDoom_of_groupF hA q hch (exists_groupF_ne hA q hch hone hl).choose_spec

/-- **The link's interface.** -/
noncomputable def linkIface : LinkIface := linkIfaceOfLinks card_notDoom_of_links

end

end LeanVM.Protocol.Relation

/-- info: 'LeanVM.Protocol.Relation.card_notDoom_of_links' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.card_notDoom_of_links

/-- info: 'LeanVM.Protocol.Relation.linkIface' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Protocol.Relation.linkIface
