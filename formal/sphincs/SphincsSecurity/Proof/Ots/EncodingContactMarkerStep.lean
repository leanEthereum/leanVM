import SphincsSecurity.Proof.Ots.OtsContactMarkerTrace
namespace SphincsSecurity.Concrete.OtsEncodingMarker

open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs OtsContactTrace.contacts

theorem contactBeforeEntry_query_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed) (input : HashInput) :
    Pr[fun result => ContactBeforeEntry parameter (referenceFamilyWords selections dummy) frontier history (input, result.1) |
      (lazyWorldImpl parameter inputs hencoding outside (.inr input)).run allowed] ≤
      (41 / (Fintype.card Digest : ENNReal)) * (contactMarkerCharge parameter (referenceFamilyWords selections dummy) frontier history (.inr input) : ENNReal) := by
  by_cases hi : input ∈ canonicalEncodingInputs parameter
  · have he : QueryClass.EncodingHash parameter (.inr input) := encodingInput_position parameter input hi
    simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hi, simulateQ_spec_query,
      UniformTableObservation.lazyImpl, StateT.run_mk, probEvent_map, Function.comp_def, contactMarkerCharge, if_pos he, ContactBeforeEntry]
    refine (newMarker_subset_cell_le parameter messages selections dummy history allowed hc
      (OtsContactTrace.contacts parameter (referenceFamilyWords selections dummy) frontier history) ⟨input, hi⟩).trans_eq ?_
    simp only [div_eq_mul_inv]
    ring
  · have hz : Pr[fun result => ContactBeforeEntry parameter (referenceFamilyWords selections dummy) frontier history (input, result.1) |
        (lazyWorldImpl parameter inputs hencoding outside (.inr input)).run allowed] = 0 := by
      apply probEvent_eq_zero
      rintro result _ ⟨address, _, hm⟩
      exact hi hm.1.2.1
    rw [hz]
    exact bot_le

section Potential

attribute [local instance 10000] Classical.propDecidable

theorem contactMarker_query_potential_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (frontier : OtsFrontierValues)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed) (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorldImpl parameter inputs hencoding outside input).run allowed] *
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier (history * hashObservationTrace input result.1) : ENNReal)) ≤
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier history : ENNReal) +
        (41 / (Fintype.card Digest : ENNReal)) * (contactMarkerCharge parameter (referenceFamilyWords selections dummy) frontier history input : ENNReal) := by
  cases input with
  | inl input =>
      simp only [hashObservationTrace, mul_one, contactMarkerCharge, QueryClass.EncodingHash, if_false,
        Nat.cast_zero, mul_zero, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
  | inr input =>
      simp only [hashObservationTrace, contactMarkerCount_step, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
      exact add_le_add (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)
        (contactBeforeEntry_query_le parameter inputs hencoding outside messages selections dummy frontier history allowed hc input)

end Potential

end SphincsSecurity.Concrete.OtsEncodingMarker
