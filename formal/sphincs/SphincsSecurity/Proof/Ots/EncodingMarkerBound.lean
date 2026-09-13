import SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation
import SphincsSecurity.Proof.Ots.ReferenceEncodingLazySource
import SphincsSecurity.Proof.Reference.ReferenceContactGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs Finset.univ OtsEncodingMarker.markers

theorem contactObserver_trace (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.output, result.before * result.after)) <$>
      contactObserver parameter words frontier computation = QueryPause.traced hashObservationTrace computation := by
  simpa only [contactObserver, Functor.map_map] using OtsContactTrace.splitRun_trace parameter words frontier computation

theorem referenceEncodingLazyRest_contact_trace (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result => ((result.1.output, result.1.before * result.1.after), result.2)) <$>
      referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary =
        EncodingObservation.lazyRun key.parameter inputs hencoding outside
          (QueryPause.traced hashObservationTrace (referenceEncodingProgram key inputs hencoding outside selections dummy adversary))
          (referenceEncodingAllowed key.parameter (outsideGraphMessage key inputs hencoding outside) selections) := by
  rw [referenceEncodingLazyRest,
    ← EncodingObservation.lazyRun_map (f := fun result : ContactResult => (result.output, result.before * result.after)),
    contactObserver_trace]

theorem referenceEncodingLazyRest_markers_le (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] *
      ((OtsEncodingMarker.markers key.parameter (referenceFamilyWords selections dummy) (result.1.before * result.1.after)).card : ENNReal)) ≤
      (1722 / (Fintype.card Digest : ENNReal)) * ∑' result,
        Pr[= result | referenceEncodingLazyRest contactObserver key inputs hencoding outside selections dummy adversary] *
          (EncodingObservation.encodingCalls key.parameter (result.1.before * result.1.after) : ENNReal) := by
  have h := EncodingObservation.markers_initial_lazyRun_le key.parameter inputs hencoding outside
    (outsideGraphMessage key inputs hencoding outside) selections dummy
    (referenceEncodingProgram key inputs hencoding outside selections dummy adversary)
  rw [← referenceEncodingLazyRest_contact_trace key inputs hencoding outside selections dummy adversary,
    tsum_probOutput_map_mul, tsum_probOutput_map_mul] at h
  exact h

private theorem weighted_bound {Value : Type} (law : SPMF Value) (left right : Value → ENNReal) (rate : ENNReal)
    (h : ∀ value, left value ≤ rate * right value) :
    (∑' value, Pr[= value | law] * left value) ≤ rate * ∑' value, Pr[= value | law] * right value := by
  calc
    _ ≤ ∑' value, Pr[= value | law] * (rate * right value) :=
      ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (h value)
    _ = _ := by simp only [mul_left_comm _ rate, ENNReal.tsum_mul_left]

theorem referenceContactGame_markers_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
      ((OtsEncodingMarker.markers result.1 (referenceFamilyWords result.2.1 dummy)
        (result.2.2.before * result.2.2.after)).card : ENNReal)) ≤
      (1722 / (Fintype.card Digest : ENNReal)) * ∑' result,
        Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
          (EncodingObservation.encodingCalls result.1 (result.2.2.before * result.2.2.after) : ENNReal) := by
  rw [referenceContactGame, ← referenceEncodingLazyGame_original contactObserver inputs hencoding hgraph dummy adversary]
  simp only [referenceEncodingLazyGame, tsum_probOutput_bind_mul, tsum_probOutput_map_mul, tsum_probOutput_pure_mul]
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
  exact referenceEncodingLazyRest_markers_le ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter)
    outside selections dummy adversary

end SphincsSecurity.Concrete
