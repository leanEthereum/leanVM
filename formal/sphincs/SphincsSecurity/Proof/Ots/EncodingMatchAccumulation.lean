import SphincsSecurity.Proof.Ots.EncodingMatchKernel
import SphincsSecurity.Proof.Ots.EncodingMarkerAccumulation
import SphincsSecurity.Proof.Ots.ReferenceLayerWitness
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs

variable (parameter : PublicParameter) (words : OtsReferenceWords)
  (messages : EncodingPosition → Digest) (selections : ReferenceFamily)

theorem encodingOutputMatch_one : ¬EncodingOutputMatch parameter words messages selections 1 := by
  simp [EncodingOutputMatch]

theorem encodingOutputMatch_of (entry : HashInput × HashOutput) :
    EncodingOutputMatch parameter words messages selections (FreeMonoid.of entry) ↔
      entry.1 ∈ canonicalEncodingInputs parameter ∧ PublicEncodingMatch.Match parameter messages words selections entry.1 entry.2 := by
  simp [EncodingOutputMatch]

theorem encodingOutputMatch_mul (before after : OtsContactTrace.Trace) :
    EncodingOutputMatch parameter words messages selections (before * after) ↔
      EncodingOutputMatch parameter words messages selections before ∨ EncodingOutputMatch parameter words messages selections after := by
  simp only [EncodingOutputMatch, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]

theorem newEncodingMatch_cell_le (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (row : canonicalEncodingInputs parameter) :
    Pr[fun output => PublicEncodingMatch.Match parameter messages words selections row.val output ∧
      ¬EncodingOutputMatch parameter words messages selections history | cell (allowed row)] ≤ (Fintype.card Digest : ENNReal)⁻¹ := by
  refine (_root_.probEvent_mono (fun _ _ h => ⟨h.1, fun hin => h.2 ⟨_, hin, row.property, h.1⟩⟩)).trans
    ((hc.new_reply_probability_le row (PublicEncodingMatch.Match parameter messages words selections row.val)).trans ?_)
  simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
    PublicEncodingMatch.match_allowed_le parameter messages words selections row

def QueryNewEncodingMatch (history : OtsContactTrace.Trace) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) : Prop :=
  EncodingOutputMatch parameter words messages selections (history * hashObservationTrace input answer) ∧
    ¬EncodingOutputMatch parameter words messages selections history

theorem queryNewEncodingMatch_coin (history : OtsContactTrace.Trace) (input : unifSpec.Domain) (answer : unifSpec.Range input) :
    ¬QueryNewEncodingMatch parameter words messages selections history (.inl input) answer := by
  simp only [QueryNewEncodingMatch, hashObservationTrace, mul_one, and_not_self, not_false_eq_true]

theorem queryNewEncodingMatch_hash (history : OtsContactTrace.Trace) (input : HashInput) (output : HashOutput) :
    QueryNewEncodingMatch parameter words messages selections history (.inr input) output ↔
      (input ∈ canonicalEncodingInputs parameter ∧ PublicEncodingMatch.Match parameter messages words selections input output) ∧
        ¬EncodingOutputMatch parameter words messages selections history := by
  simp only [QueryNewEncodingMatch, hashObservationTrace, encodingOutputMatch_mul, encodingOutputMatch_of,
    or_and_right, and_not_self, false_or]

theorem queryNewEncodingMatch_le (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    Pr[fun result => QueryNewEncodingMatch parameter words messages selections history input result.1 |
      (lazyWorldImpl parameter inputs hencoding outside input).run allowed] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      have hz : Pr[fun result => QueryNewEncodingMatch parameter words messages selections history (.inl input) result.1 |
          (lazyWorldImpl parameter inputs hencoding outside (.inl input)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ => queryNewEncodingMatch_coin _ _ _ _ _ _ result.1
      rw [hz]
      exact bot_le
  | inr input =>
      by_cases hi : input ∈ canonicalEncodingInputs parameter
      · have he : QueryClass.EncodingHash parameter (.inr input) := OtsEncodingMarker.encodingInput_position parameter input hi
        simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hi, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, probEvent_map, Function.comp_def,
          queryNewEncodingMatch_hash, if_pos he, Nat.cast_one, mul_one]
        simp only [hi, true_and]
        exact newEncodingMatch_cell_le parameter words messages selections history allowed hc ⟨input, hi⟩
      · have hz : Pr[fun result => QueryNewEncodingMatch parameter words messages selections history (.inr input) result.1 |
            (lazyWorldImpl parameter inputs hencoding outside (.inr input)).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ hm
          exact hi ((queryNewEncodingMatch_hash _ _ _ _ _ _ _).mp hm).1.1
        rw [hz]
        exact bot_le

theorem encodingMatch_query_potential_le (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorldImpl parameter inputs hencoding outside input).run allowed] *
      (if EncodingOutputMatch parameter words messages selections (history * hashObservationTrace input result.1) then 1 else 0 : ENNReal)) ≤
      (if EncodingOutputMatch parameter words messages selections history then 1 else 0 : ENNReal) +
        (Fintype.card Digest : ENNReal)⁻¹ * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  by_cases hs : EncodingOutputMatch parameter words messages selections history
  · have hnext : ∀ answer, EncodingOutputMatch parameter words messages selections (history * hashObservationTrace input answer) :=
      fun _ => (encodingOutputMatch_mul _ _ _ _ _ _).mpr (Or.inl hs)
    simp only [if_pos hs, if_pos (hnext _), mul_one]
    exact le_add_of_le_left tsum_probOutput_le_one
  · simpa only [QueryNewEncodingMatch, hs, not_false_eq_true, and_true, if_false, zero_add,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero] using
      queryNewEncodingMatch_le parameter words messages selections inputs hencoding outside history allowed hc input

theorem encodingMatch_lazyRun_le {Result : Type} (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    Pr[fun result => EncodingOutputMatch parameter words messages selections (history * result.1.2) |
      lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] ≤
      (if EncodingOutputMatch parameter words messages selections history then 1 else 0 : ENNReal) +
        (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (encodingCalls parameter result.1.2 : ENNReal) := by
  suffices h : (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside
      (QueryPause.traced hashObservationTrace computation) allowed] *
      (if EncodingOutputMatch parameter words messages selections (history * result.1.2) then 1 else 0 : ENNReal)) ≤
      (if EncodingOutputMatch parameter words messages selections history then 1 else 0 : ENNReal) +
        (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (encodingCalls parameter result.1.2 : ENNReal) by
    simpa only [mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite] using h
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_potential_le hashObservationTrace (lazyWorldImpl parameter inputs hencoding outside)
    (fun history allowed => TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed ∧
      ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => if EncodingOutputMatch parameter words messages selections history then 1 else 0)
    _ (encodingCalls parameter) _ (encodingCalls_one parameter) (encodingCalls_step parameter) _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent parameter inputs hencoding outside _ allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary parameter inputs hencoding outside) (translate parameter input)
        allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail parameter inputs hencoding outside _ allowed hi.2)
  · intro history allowed hi input
    exact encodingMatch_query_potential_le parameter words messages selections inputs hencoding outside history allowed hi.1 input

theorem encodingMatch_initial_lazyRun_le {Result : Type} (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) :
    Pr[fun result => EncodingOutputMatch parameter words messages selections result.1.2 |
      lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
        (referenceEncodingAllowed parameter messages selections)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
          (referenceEncodingAllowed parameter messages selections)] * (encodingCalls parameter result.1.2 : ENNReal) := by
  simpa only [one_mul, if_neg (encodingOutputMatch_one parameter words messages selections), zero_add] using
    encodingMatch_lazyRun_le parameter words messages selections inputs hencoding outside computation 1 _
      (traceConsistent_one parameter _) (referenceEncodingAllowed_nonempty parameter messages selections)

end SphincsSecurity.Concrete.OtsVerifierWitness
