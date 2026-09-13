import SphincsSecurity.Proof.Ots.EncodingMarkerBound
import SphincsSecurity.Proof.Reference.ReferenceQueryAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs Finset.univ

theorem contactObserver_encodingCalls (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.output, EncodingObservation.encodingCalls parameter (result.before * result.after))) <$>
      contactObserver parameter words frontier computation = QueryCap.counted (QueryClass.EncodingHash parameter) computation := by
  have h := congrArg (Functor.map (fun result => (result.1, EncodingObservation.encodingCalls parameter result.2)))
    (contactObserver_trace parameter words frontier computation)
  rw [Functor.map_map] at h
  exact h.trans (QueryPause.traced_counted hashObservationTrace (QueryClass.EncodingHash parameter)
    (EncodingObservation.encodingCalls parameter) (EncodingObservation.encodingCalls_one parameter)
    (EncodingObservation.encodingCalls_step parameter) computation)

theorem referenceContactRest_encodingCalls (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (labels : CanonicalGraphLabels) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : ContactResult => (result.output, EncodingObservation.encodingCalls key.parameter (result.before * result.after))) <$>
      referenceInstrumentedRest contactObserver key oracle labels selections dummy adversary =
        (fun result => (result.1, QueryCap.calls (QueryClass.EncodingHash key.parameter) result.2)) <$>
          referenceRecordedRest key oracle labels selections dummy adversary := by
  rw [referenceInstrumentedRest, referenceRecordedRest, ← simulateQ_map, ← simulateQ_map,
    contactObserver_encodingCalls, QueryCap.recorded_counted]

theorem referenceContactGame_encodingCalls (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : InstrumentedResult ContactResult =>
      (result.1, result.2.1, result.2.2.output, EncodingObservation.encodingCalls result.1 (result.2.2.before * result.2.2.after))) <$>
        referenceContactGame inputs hencoding dummy adversary =
      (fun result : ReferenceRecordedResult => (result.1, result.2.1, result.2.2.1, result.encodingCalls)) <$>
        referenceRecordedGame inputs hencoding dummy adversary := by
  unfold referenceContactGame referenceInstrumentedGame referenceRecordedGame
  simp only [map_bind, map_pure, ReferenceRecordedResult.encodingCalls]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  have h := congrArg (fun law => (fun result => (parameter, reference.1, result.1, result.2)) <$> 𝒟[law])
    (referenceContactRest_encodingCalls ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
      (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary)
  simpa only [← bind_pure_comp, evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

theorem referenceContactGame_expected_encodingCalls (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceContactGame inputs hencoding dummy adversary] *
      (EncodingObservation.encodingCalls result.1 (result.2.2.before * result.2.2.after) : ENNReal)) =
        ∑' result, Pr[= result | referenceRecordedGame inputs hencoding dummy adversary] * (result.encodingCalls : ENNReal) := by
  have h := congrArg (fun law : SPMF (PublicParameter × ReferenceFamily × (Bool × SigningBoundaryTrace) × Nat) =>
    ∑' result, Pr[= result | law] * (result.2.2.2 : ENNReal)) (referenceContactGame_encodingCalls inputs hencoding dummy adversary)
  simpa only [tsum_probOutput_map_mul] using h

theorem referenceContactGame_markers_le_encodingCost (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
      ((OtsEncodingMarker.markers result.1 (referenceFamilyWords result.2.1 dummy)
        (result.2.2.before * result.2.2.after)).card : ENNReal)) ≤
      (1722 / (Fintype.card Digest : ENNReal)) * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal) := by
  rw [← referenceContactGame_expected_encodingCalls]
  exact referenceContactGame_markers_le _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary

end SphincsSecurity.Concrete
