import SphincsSecurity.Proof.Hypertree.StructuralMatchAccumulation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs structuralInputs Finset.univ

theorem structuralLazy_contact_match_le (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (outside : NonstructuralRows key.parameter inputs)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    Pr[fun result => ReferenceStructuralMatch.Seen key labels words (result.1.before * result.1.after) |
      StructuralObservation.lazyRun key inputs labels outside (contactObserver key.parameter words frontier computation) (fun _ => Finset.univ)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | StructuralObservation.lazyRun key inputs labels outside
          (contactObserver key.parameter words frontier computation) (fun _ => Finset.univ)] *
            (StructuralObservation.otherCalls key.parameter words (result.1.before * result.1.after) : ENNReal) := by
  have h := StructuralObservation.match_initial_lazyRun_le key inputs labels hgraph outside words computation
  have htrace : (fun result => ((result.1.output, result.1.before * result.1.after), result.2)) <$>
      StructuralObservation.lazyRun key inputs labels outside (contactObserver key.parameter words frontier computation) (fun _ => Finset.univ) =
        StructuralObservation.lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) (fun _ => Finset.univ) := by
    rw [← StructuralObservation.lazyRun_map (f := fun result : ContactResult => (result.output, result.before * result.after)), contactObserver_trace]
  rw [← htrace, probEvent_map, tsum_probOutput_map_mul] at h
  exact h

private theorem weighted_bound {Value : Type} (law : SPMF Value) (left right : Value → ENNReal) (rate : ENNReal)
    (h : ∀ value, left value ≤ rate * right value) :
    (∑' value, Pr[= value | law] * left value) ≤ rate * ∑' value, Pr[= value | law] * right value := by
  calc
    _ ≤ ∑' value, Pr[= value | law] * (rate * right value) := ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (h value)
    _ = _ := by simp only [mul_left_comm _ rate, ENNReal.tsum_mul_left]

theorem referenceGraphContextRest_match_le (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => ReferenceStructuralMatch.Seen key result.1 (referenceFamilyWords result.2.1 dummy)
      (result.2.2.before * result.2.2.after) | referenceGraphContextRest contactObserver key inputs hencoding dummy adversary] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | referenceGraphContextRest contactObserver key inputs hencoding dummy adversary] *
          (StructuralObservation.otherCalls key.parameter (referenceFamilyWords result.2.1 dummy) (result.2.2.before * result.2.2.after) : ENNReal) := by
  rw [StructuralObservation.referenceGraphContextRest_lazy contactObserver key inputs hencoding hgraph dummy adversary]
  simp only [probEvent_bind_eq_tsum, probEvent_pure, tsum_probOutput_bind_mul, tsum_probOutput_map_mul, tsum_probOutput_pure_mul]
  apply weighted_bound
  intro labels
  apply weighted_bound
  intro outside
  simpa only [probEvent_pure, mul_ite, mul_one, mul_zero, probEvent_eq_tsum_ite] using
    structuralLazy_contact_match_le key inputs labels hgraph outside
      (referenceFamilyWords (referenceTableSelection key (structuralAnswer key inputs labels outside (fun _ => 0))) dummy) _
      (structuralProgram key inputs labels outside _ adversary)

theorem referenceGraphContextGame_match_le (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => ReferenceStructuralMatch.Seen result.1 result.2.1 (referenceFamilyWords result.2.2.1 dummy)
      (result.2.2.2.before * result.2.2.2.after) | referenceGraphContextGame contactObserver inputs hencoding dummy adversary] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | referenceGraphContextGame contactObserver inputs hencoding dummy adversary] *
          (StructuralObservation.otherCalls result.1.parameter (referenceFamilyWords result.2.2.1 dummy)
            (result.2.2.2.before * result.2.2.2.after) : ENNReal) := by
  simp only [referenceGraphContextGame, probEvent_bind_eq_tsum, probEvent_pure, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul]
  apply weighted_bound
  intro parameter
  apply weighted_bound
  intro otsSecret
  apply weighted_bound
  intro ftsSecret
  simpa only [probEvent_pure, mul_ite, mul_one, mul_zero, probEvent_eq_tsum_ite] using
    referenceGraphContextRest_match_le ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter) (hgraph parameter) dummy adversary

theorem contactObserver_otherCalls (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld (Bool × SigningBoundaryTrace)) :
    (fun result : ContactResult => (result.output, StructuralObservation.otherCalls parameter words (result.before * result.after))) <$>
      contactObserver parameter words frontier computation = QueryCap.counted (QueryClass.OtherHash parameter words) computation := by
  have h := congrArg (Functor.map (fun result => (result.1, StructuralObservation.otherCalls parameter words result.2)))
    (contactObserver_trace parameter words frontier computation)
  rw [Functor.map_map] at h
  exact h.trans (QueryPause.traced_counted hashObservationTrace (QueryClass.OtherHash parameter words)
    (StructuralObservation.otherCalls parameter words) (StructuralObservation.otherCalls_one parameter words)
    (StructuralObservation.otherCalls_step parameter words) computation)

theorem referenceContactRest_otherCalls (key : SecretKey) (oracle : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : ContactResult => (result.output,
      StructuralObservation.otherCalls key.parameter (referenceFamilyWords selections dummy) (result.before * result.after))) <$>
        referenceInstrumentedRest contactObserver key oracle labels selections dummy adversary =
      (fun result => (result.1, QueryCap.calls (QueryClass.OtherHash key.parameter (referenceFamilyWords selections dummy)) result.2)) <$>
        referenceRecordedRest key oracle labels selections dummy adversary := by
  rw [referenceInstrumentedRest, referenceRecordedRest, ← simulateQ_map, ← simulateQ_map,
    contactObserver_otherCalls, QueryCap.recorded_counted]

theorem referenceContactGame_otherCalls (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : InstrumentedResult ContactResult => (result.1, result.2.1, result.2.2.output,
      StructuralObservation.otherCalls result.1 (referenceFamilyWords result.2.1 dummy) (result.2.2.before * result.2.2.after))) <$>
        referenceContactGame inputs hencoding dummy adversary =
      (fun result : ReferenceRecordedResult => (result.1, result.2.1, result.2.2.1, result.otherCalls dummy)) <$>
        referenceRecordedGame inputs hencoding dummy adversary := by
  unfold referenceContactGame referenceInstrumentedGame referenceRecordedGame
  simp only [map_bind, map_pure, ReferenceRecordedResult.otherCalls]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  apply congrArg (𝒟[referenceFamilyOracleSample _ inputs (hencoding parameter)] >>= ·)
  funext reference
  have h := congrArg (fun law => (fun result => (parameter, reference.1, result.1, result.2)) <$> 𝒟[law])
    (referenceContactRest_otherCalls ⟨parameter, 0, otsSecret, ftsSecret⟩ (finiteHashAnswer ∅ inputs reference.2)
      (canonicalGraphLabels parameter otsSecret ftsSecret (finiteHashAnswer ∅ inputs reference.2)) reference.1 dummy adversary)
  simpa only [← bind_pure_comp, evalDist_bind, evalDist_pure, bind_assoc, pure_bind] using h

theorem referenceGraphContextGame_expected_otherCalls (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (∑' result, Pr[= result | referenceGraphContextGame contactObserver inputs hencoding dummy adversary] *
      (StructuralObservation.otherCalls result.1.parameter (referenceFamilyWords result.2.2.1 dummy)
        (result.2.2.2.before * result.2.2.2.after) : ENNReal)) =
      ∑' result, Pr[= result | referenceRecordedGame inputs hencoding dummy adversary] * (result.otherCalls dummy : ENNReal) := by
  have he := congrArg (fun law : SPMF (InstrumentedResult ContactResult) => ∑' result, Pr[= result | law] *
    (StructuralObservation.otherCalls result.1 (referenceFamilyWords result.2.1 dummy) (result.2.2.before * result.2.2.after) : ENNReal))
      (referenceGraphContextGame_erased contactObserver inputs hencoding dummy adversary)
  rw [tsum_probOutput_map_mul] at he
  have hc := congrArg (fun law : SPMF (PublicParameter × ReferenceFamily × (Bool × SigningBoundaryTrace) × Nat) =>
    ∑' result, Pr[= result | law] * (result.2.2.2 : ENNReal)) (referenceContactGame_otherCalls inputs hencoding dummy adversary)
  simp only [tsum_probOutput_map_mul] at hc
  exact he.trans hc

theorem referenceGraphContextGame_match_le_otherCost (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => ReferenceStructuralMatch.Seen result.1 result.2.1 (referenceFamilyWords result.2.2.1 dummy)
      (result.2.2.2.before * result.2.2.2.after) |
        referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.otherCalls dummy : ENNReal) := by
  rw [← referenceGraphContextGame_expected_otherCalls]
  exact referenceGraphContextGame_match_le _ _ (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary

end SphincsSecurity.Concrete
