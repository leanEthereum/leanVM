import SphincsSecurity.Proof.Ots.EncodingContactMarkerStep
import SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation
namespace SphincsSecurity.Concrete.EncodingObservation

open _root_.OracleComp OracleSpec OtsEncodingMarker
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Finset.univ canonicalEncodingInputs OtsContactTrace.contacts

theorem contactMarker_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier (history * result.1.2) : ENNReal)) ≤
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier history : ENNReal) +
        (41 / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (contactMarkerCost parameter (referenceFamilyWords selections dummy) frontier history result.1.2 : ENNReal) := by
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_history_potential_le hashObservationTrace (lazyWorldImpl parameter inputs hencoding outside)
    (fun history allowed => TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed ∧
      ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier history)
    _ (contactMarkerCost parameter (referenceFamilyWords selections dummy) frontier) _
    (contactMarkerCost_one parameter (referenceFamilyWords selections dummy) frontier)
    (contactMarkerCost_step parameter (referenceFamilyWords selections dummy) frontier) _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent parameter inputs hencoding outside _ allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary parameter inputs hencoding outside) (translate parameter input)
        allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail parameter inputs hencoding outside _ allowed hi.2)
  · intro history allowed hi input
    exact contactMarker_query_potential_le parameter inputs hencoding outside messages selections dummy frontier history allowed hi.1 input

theorem contactMarker_initial_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp OracleWorld Result) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
      (referenceEncodingAllowed parameter messages selections)] *
      (contactMarkerCount parameter (referenceFamilyWords selections dummy) frontier result.1.2 : ENNReal)) ≤
        (41 / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
            (referenceEncodingAllowed parameter messages selections)] *
              (contactMarkerCost parameter (referenceFamilyWords selections dummy) frontier 1 result.1.2 : ENNReal) := by
  simpa only [one_mul, contactMarkerCount_one, Nat.cast_zero, zero_add] using
    contactMarker_lazyRun_le parameter inputs hencoding outside messages selections dummy frontier computation 1 _
      (traceConsistent_one parameter _) (referenceEncodingAllowed_nonempty parameter messages selections)

end SphincsSecurity.Concrete.EncodingObservation
