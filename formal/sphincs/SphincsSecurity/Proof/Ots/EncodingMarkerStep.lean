import SphincsSecurity.Proof.Ots.EncodingAdaptiveMarker
namespace SphincsSecurity.Concrete.OtsEncodingMarker

open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs markers

def QueryNewMarker (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : OracleWorld.Domain) (answer : OracleWorld.Range input) : Prop :=
  ∃ address, Seen parameter words address (history * hashObservationTrace input answer) ∧ ¬Seen parameter words address history

theorem queryNewMarker_coin (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : unifSpec.Domain) (answer : unifSpec.Range input) : ¬QueryNewMarker parameter words history (.inl input) answer := by
  simp only [QueryNewMarker, hashObservationTrace, mul_one, and_not_self, exists_false, not_false_eq_true]

theorem queryNewMarker_hash (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : HashInput) (output : HashOutput) :
    QueryNewMarker parameter words history (.inr input) output ↔ ∃ address, NewMarker parameter words history address (input, output) := by
  simp only [QueryNewMarker, hashObservationTrace, seen_mul, seen_of, or_and_right, and_not_self, false_or, NewMarker]

theorem queryNewMarker_any_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history input result.1 |
      (lazyWorldImpl parameter inputs hencoding outside input).run allowed] ≤
      (1722 / (Fintype.card Digest : ENNReal)) * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      have hz : Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history (.inl input) result.1 |
          (lazyWorldImpl parameter inputs hencoding outside (.inl input)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ => queryNewMarker_coin _ _ _ _ result.1
      rw [hz]
      exact bot_le
  | inr input =>
      by_cases hi : input ∈ canonicalEncodingInputs parameter
      · have he : QueryClass.EncodingHash parameter (.inr input) := encodingInput_position parameter input hi
        simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hi, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, probEvent_map, Function.comp_def,
          queryNewMarker_hash, if_pos he, Nat.cast_one, mul_one]
        exact newMarker_any_cell_le parameter messages selections dummy history allowed hc ⟨input, hi⟩
      · have hz : Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history (.inr input) result.1 |
            (lazyWorldImpl parameter inputs hencoding outside (.inr input)).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ hm
          obtain ⟨_, hm⟩ := (queryNewMarker_hash _ _ _ _ _).mp hm
          exact hi hm.1.2.1
        rw [hz]
        exact bot_le

section Potential

attribute [local instance 10000] Classical.propDecidable

theorem markers_query_potential_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorldImpl parameter inputs hencoding outside input).run allowed] *
      ((markers parameter (referenceFamilyWords selections dummy) (history * hashObservationTrace input result.1)).card : ENNReal)) ≤
      ((markers parameter (referenceFamilyWords selections dummy) history).card : ENNReal) +
        (1722 / (Fintype.card Digest : ENNReal)) * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      simp only [hashObservationTrace, mul_one, QueryClass.EncodingHash, if_false, Nat.cast_zero,
        mul_zero, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
  | inr input =>
      simp only [hashObservationTrace, markers_step_card, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
      apply add_le_add (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)
      simpa only [queryNewMarker_hash, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] using
        queryNewMarker_any_le parameter inputs hencoding outside messages selections dummy history allowed hc (.inr input)

end Potential

end SphincsSecurity.Concrete.OtsEncodingMarker
