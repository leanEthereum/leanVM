import SphincsSecurity.Proof.Ots.EncodingMatchAccumulation
import SphincsSecurity.Proof.Ots.ReferenceEncodingContext
import SphincsSecurity.Proof.Ots.EncodingMarkerAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ

theorem referenceEncodingLazyRest_match_le (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => OtsVerifierWitness.EncodingOutputMatch key.parameter (referenceFamilyWords selections dummy)
      (outsideGraphMessage key inputs hencoding outside) selections (result.1.before * result.1.after) |
        referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] *
          (EncodingObservation.encodingCalls key.parameter (result.1.before * result.1.after) : ENNReal) := by
  have h := OtsVerifierWitness.encodingMatch_initial_lazyRun_le key.parameter (referenceFamilyWords selections dummy)
    (outsideGraphMessage key inputs hencoding outside) selections inputs hencoding outside
    (referenceEncodingProgram key inputs hencoding outside selections dummy adversary)
  rw [← referenceEncodingLazyRest_contact_trace key inputs hencoding outside selections dummy adversary,
    probEvent_map, tsum_probOutput_map_mul] at h
  exact h

private theorem weighted_bound {Value : Type} (law : SPMF Value) (left right : Value → ENNReal) (rate : ENNReal)
    (h : ∀ value, left value ≤ rate * right value) :
    (∑' value, Pr[= value | law] * left value) ≤ rate * ∑' value, Pr[= value | law] * right value := by
  calc
    _ ≤ ∑' value, Pr[= value | law] * (rate * right value) :=
      ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (h value)
    _ = _ := by simp only [mul_left_comm _ rate, ENNReal.tsum_mul_left]

theorem referenceEncodingContextGame_match_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => OtsVerifierWitness.EncodingOutputMatch result.1 (referenceFamilyWords result.2.1 dummy)
      result.2.2.1 result.2.1 (result.2.2.2.before * result.2.2.2.after) |
        referenceEncodingContextGame contactObserver inputs hencoding dummy adversary] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | referenceEncodingContextGame contactObserver inputs hencoding dummy adversary] *
          (EncodingObservation.encodingCalls result.1 (result.2.2.2.before * result.2.2.2.after) : ENNReal) := by
  rw [referenceEncodingContextGame_lazy contactObserver inputs hencoding hgraph dummy adversary]
  simp only [probEvent_bind_eq_tsum, probEvent_pure,
    tsum_probOutput_bind_mul, tsum_probOutput_map_mul, tsum_probOutput_pure_mul]
  apply weighted_bound
  intro parameter
  apply weighted_bound
  intro otsSecret
  apply weighted_bound
  intro ftsSecret
  apply weighted_bound
  intro selections
  apply weighted_bound
  intro outside
  simpa only [probEvent_pure, mul_ite, mul_one, mul_zero, probEvent_eq_tsum_ite] using
    referenceEncodingLazyRest_match_le ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) outside selections dummy adversary

theorem referenceEncodingContextGame_expected_encodingCalls (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceEncodingContextGame contactObserver inputs hencoding dummy adversary] *
      (EncodingObservation.encodingCalls result.1 (result.2.2.2.before * result.2.2.2.after) : ENNReal)) =
        ∑' result, Pr[= result | referenceRecordedGame inputs hencoding dummy adversary] * (result.encodingCalls : ENNReal) := by
  have h := congrArg (fun law : SPMF (InstrumentedResult ContactResult) =>
    ∑' result, Pr[= result | law] * (EncodingObservation.encodingCalls result.1 (result.2.2.before * result.2.2.after) : ENNReal))
      (referenceEncodingContextGame_erased contactObserver inputs hencoding dummy adversary)
  rw [tsum_probOutput_map_mul] at h
  exact h.trans (referenceContactGame_expected_encodingCalls inputs hencoding dummy adversary)

theorem referenceEncodingContextGame_match_le_encodingCost (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => OtsVerifierWitness.EncodingOutputMatch result.1 (referenceFamilyWords result.2.1 dummy)
      result.2.2.1 result.2.1 (result.2.2.2.before * result.2.2.2.after) |
        referenceEncodingContextGame contactObserver (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal) := by
  rw [← referenceEncodingContextGame_expected_encodingCalls]
  exact referenceEncodingContextGame_match_le _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary

end SphincsSecurity.Concrete
