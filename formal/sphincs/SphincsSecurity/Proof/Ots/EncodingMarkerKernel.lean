import SphincsSecurity.Proof.Ots.EncodingTablePrior
import SphincsSecurity.Proof.Ots.OtsEncodingMarker
namespace SphincsSecurity.Concrete.OtsEncodingMarker

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs

theorem entryMarker_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (cell : canonicalEncodingInputs parameter) :
    Pr[fun output : HashOutput => EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output) |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ 41 / (Fintype.card Digest : ENNReal) := by
  by_cases hp : AtEncodingPosition parameter cell.val ⟨address.1, address.2.1, address.2.2.1⟩
  · refine (_root_.probEvent_mono (mx := (liftM (PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
      (referenceEncodingAllowed_nonempty parameter messages selections cell)) : SPMF HashOutput)) ?_).trans (freshEncodingSupport_neighbor_le
      (referenceFamilyWords selections dummy address.1 address.2.1 address.2.2.1) address.2.2.2 _ _
      (referenceEncodingAllowed_fresh parameter messages selections dummy cell _ hp))
    intro output _ hm
    obtain ⟨_, _, candidate, hd, hn⟩ := hm
    exact TargetSum.mem_decodingDigests.mpr ⟨candidate, TargetSum.mem_unitNeighbors.mpr hn, hd⟩
  · have he : (fun output : HashOutput => EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output)) =
        fun _ => False := by
      funext output
      apply propext
      exact ⟨fun hm => hp hm.1, False.elim⟩
    rw [he]
    simp only [probEvent_eq_tsum_ite, if_false, tsum_zero, zero_le]

theorem encodingInput_position (parameter : PublicParameter) (input : HashInput)
    (hc : input ∈ canonicalEncodingInputs parameter) : ∃ position, AtEncodingPosition parameter input position := by
  rw [canonicalEncodingInputs] at hc
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hc
  obtain ⟨position, pair, hinput⟩ := hc
  exact ⟨position, _, hinput.symm⟩

theorem entryMarker_any_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter) :
    Pr[fun output : HashOutput => ∃ address, EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output) |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ 1722 / (Fintype.card Digest : ENNReal) := by
  obtain ⟨position, hp⟩ := encodingInput_position parameter cell.val cell.property
  refine (_root_.probEvent_mono (mx := (liftM (PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
      (referenceEncodingAllowed_nonempty parameter messages selections cell)) : SPMF HashOutput)) ?_).trans (freshEncodingSupport_all_neighbors_le
    (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx) _ _
    (referenceEncodingAllowed_fresh parameter messages selections dummy cell position hp))
  intro output _ hm
  obtain ⟨⟨lay, tree, leaf, chain⟩, hposition, _, candidate, hd, hn⟩ := hm
  have he := atEncodingPosition_unique hposition hp
  subst position
  exact TargetSum.mem_decodingDigests.mpr ⟨candidate, TargetSum.mem_allUnitNeighbors.mpr ⟨chain, hn⟩, hd⟩

end SphincsSecurity.Concrete.OtsEncodingMarker
