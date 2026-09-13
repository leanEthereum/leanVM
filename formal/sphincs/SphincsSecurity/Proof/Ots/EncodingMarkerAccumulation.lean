import SphincsSecurity.Proof.Ots.EncodingMarkerStep
import SphincsSecurity.Proof.Base.QueryTracePotential

/-! ## UniformTableObservationMass -/

namespace SphincsSecurity.Concrete.UniformTableObservation

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false

theorem lazyRun_neverFail {Coordinate Value AuxIndex Result : Type} [DecidableEq Coordinate]
    {auxSpec : OracleSpec AuxIndex} (auxiliary : QueryImpl auxSpec SPMF)
    (haux : ∀ input, NeverFail (auxiliary input))
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    NeverFail (lazyRun auxiliary computation allowed) := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure value => rw [lazyRun_pure]; infer_instance
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          exact ⟨haux input, fun answer _ => ih answer allowed ha⟩
      | inr coordinate =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          constructor
          · rw [cell, dif_pos (ha coordinate)]
            exact ⟨probFailure_of_liftM_PMF _⟩
          · intro answer _
            exact ih answer _ (discloseTableValue_nonempty allowed ha coordinate answer)

end SphincsSecurity.Concrete.UniformTableObservation

namespace SphincsSecurity.Concrete.EncodingObservation

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs OtsEncodingMarker.markers

theorem lazyRun_neverFail {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (ha : ∀ row, (allowed row).Nonempty) : NeverFail (lazyRun parameter inputs hencoding outside computation allowed) := by
  apply UniformTableObservation.lazyRun_neverFail _ _ _ _ ha
  intro input
  exact ⟨probFailure_eq_zero (mx := fixedHashWorld (nonencodingAnswer parameter inputs hencoding outside) input)⟩

noncomputable def encodingCalls (parameter : PublicParameter) (trace : OtsContactTrace.Trace) : Nat :=
  QueryCap.calls (QueryClass.EncodingHash parameter) (trace.toList.map fun entry => .inr entry.1)

theorem encodingCalls_one (parameter : PublicParameter) : encodingCalls parameter 1 = 0 := rfl

theorem encodingCalls_step (parameter : PublicParameter) (input : OracleWorld.Domain) (answer : OracleWorld.Range input)
    (tail : OtsContactTrace.Trace) :
    encodingCalls parameter (hashObservationTrace input answer * tail) =
      (if QueryClass.EncodingHash parameter input then 1 else 0) + encodingCalls parameter tail := by
  cases input with
  | inl input => simp only [hashObservationTrace, one_mul, QueryClass.EncodingHash, if_false, Nat.zero_add]
  | inr input =>
      simp only [encodingCalls, hashObservationTrace, FreeMonoid.toList_mul, FreeMonoid.toList_of,
        List.singleton_append, List.map_cons, QueryCap.calls_cons]

theorem markers_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) (history * result.1.2)).card : ENNReal)) ≤
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) history).card : ENNReal) +
        (1722 / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (encodingCalls parameter result.1.2 : ENNReal) := by
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_potential_le hashObservationTrace (lazyWorldImpl parameter inputs hencoding outside)
    (fun history allowed => TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed ∧
      ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => (OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) history).card)
    _ (encodingCalls parameter) _ (encodingCalls_one parameter) (encodingCalls_step parameter) _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent parameter inputs hencoding outside _ allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary parameter inputs hencoding outside) (translate parameter input)
        allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail parameter inputs hencoding outside _ allowed hi.2)
  · intro history allowed hi input
    exact OtsEncodingMarker.markers_query_potential_le parameter inputs hencoding outside messages selections dummy history allowed hi.1 input

theorem markers_initial_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
      (referenceEncodingAllowed parameter messages selections)] *
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) result.1.2).card : ENNReal)) ≤
        (1722 / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
            (referenceEncodingAllowed parameter messages selections)] * (encodingCalls parameter result.1.2 : ENNReal) := by
  simpa only [one_mul, OtsEncodingMarker.markers_one, Finset.card_empty, Nat.cast_zero, zero_add] using
    markers_lazyRun_le parameter inputs hencoding outside messages selections dummy computation 1 _
      (traceConsistent_one parameter _) (referenceEncodingAllowed_nonempty parameter messages selections)

end SphincsSecurity.Concrete.EncodingObservation
