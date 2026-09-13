import SphincsSecurity.Proof.Ots.ReferenceLayerWitness
import SphincsSecurity.Proof.Ots.OtsTwoEdgeProbability
import SphincsSecurity.Proof.Ots.OtsDistinctContactProbability
import SphincsSecurity.Proof.Ots.OtsMarkerContactPartition
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts canonicalEncodingInputs canonicalGraphInputs instFintypePosition

theorem chainException_contactResult (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (words : OtsReferenceWords)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) (result : ContactResult)
    (hfrontier : ∀ index, result.frontier lay tree leaf index = frontier f parameter words lay tree leaf secret index)
    (hexception : ChainException f parameter words lay tree leaf secret (result.before * result.after)) :
    (∃ index, ForwardChainMatch f (segment parameter words lay tree leaf index) (secret index) (result.before * result.after)) ∨
      result.TwoEdge parameter words ∨ result.TwoContacts parameter words ∨ result.MarkerContact parameter words := by
  have hcontact (index : ChainIndex)
      (h : Seen (segment parameter words lay tree leaf index) (frontier f parameter words lay tree leaf secret index) (result.before * result.after)) :
      (⟨lay, tree, leaf, index⟩ : OtsPrefix.ChainAddress) ∈ contacts parameter words result.frontier (result.before * result.after) := by
    rw [mem_contacts]
    simpa only [hfrontier] using h
  rcases hexception with hf | ⟨index, ht⟩ | ⟨left, right, hne, hl, hr⟩ | ⟨index, hm, hc⟩
  · exact Or.inl hf
  · refine Or.inr (Or.inl ⟨⟨lay, tree, leaf, index⟩, ?_⟩)
    change SeenTwoEdge _ (result.frontier lay tree leaf index) (result.before * result.after)
    rw [hfrontier]
    exact ht
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    apply Finset.one_lt_card.mpr
    refine ⟨⟨lay, tree, leaf, left⟩, hcontact left hl, ⟨lay, tree, leaf, right⟩, hcontact right hr, ?_⟩
    intro he
    exact hne (congrArg (fun address : OtsPrefix.ChainAddress => address.2.2.2) he)
  · exact Or.inr (Or.inr (Or.inr ⟨⟨lay, tree, leaf, index⟩, hm, hcontact index hc⟩))

end SphincsSecurity.Concrete.OtsVerifierWitness
