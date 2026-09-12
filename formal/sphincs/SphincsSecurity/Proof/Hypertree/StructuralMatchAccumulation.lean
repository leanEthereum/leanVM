import SphincsSecurity.Proof.Hypertree.StructuralTraceCache
namespace SphincsSecurity.Concrete.StructuralObservation

open _root_.OracleComp OracleSpec UniformTableCompletion ReferenceStructuralMatch
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] structuralInputs canonicalGraphInputs Finset.univ

theorem entry_active (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (input : HashInput) (answer : HashOutput)
    (h : Entry key labels words input answer) : Active key inputs labels input := by
  refine ⟨(mem_structuralInputs key.parameter inputs input).mpr ⟨hgraph h.1, ?_⟩, h.noncanonical⟩
  obtain ⟨position, _, _, hp, _⟩ := h.2
  exact ⟨position, hp⟩

theorem newMatch_cell_le (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : structuralInputs key.parameter inputs → Finset HashOutput)
    (hc : TraceConsistent key inputs labels history allowed) (row : structuralInputs key.parameter inputs)
    (ha : Active key inputs labels row.val) :
    Pr[fun output => Entry key labels words row.val output ∧ ¬Seen key labels words history | cell (allowed row)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ((if QueryClass.OtherHash key.parameter words (.inr row.val) then 1 else 0 : Nat) : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ⟨h.1, fun hin => h.2 ⟨_, hin, h.1⟩⟩)).trans
    ((hc.new_reply_probability_le row ha (Entry key labels words row.val)).trans ?_)
  simpa only [cell, dif_pos Finset.univ_nonempty, PMF.uniformOfFintype] using entry_uniform_other_le key labels words row.val

def QueryNewMatch (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : OracleWorld.Domain) (answer : OracleWorld.Range input) : Prop :=
  Seen key labels words (history * hashObservationTrace input answer) ∧ ¬Seen key labels words history

theorem queryNewMatch_coin (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : unifSpec.Domain) (answer : unifSpec.Range input) : ¬QueryNewMatch key labels words history (.inl input) answer := by
  simp only [QueryNewMatch, hashObservationTrace, mul_one, and_not_self, not_false_eq_true]

theorem queryNewMatch_hash (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : HashInput) (answer : HashOutput) :
    QueryNewMatch key labels words history (.inr input) answer ↔ Entry key labels words input answer ∧ ¬Seen key labels words history := by
  simp only [QueryNewMatch, hashObservationTrace, seen_mul, seen_of, or_and_right, and_not_self, false_or]

theorem queryNewMatch_le (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (outside : NonstructuralRows key.parameter inputs) (words : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : structuralInputs key.parameter inputs → Finset HashOutput)
    (hc : TraceConsistent key inputs labels history allowed) (input : OracleWorld.Domain) :
    Pr[fun result => QueryNewMatch key labels words history input result.1 | (lazyWorldImpl key inputs labels outside input).run allowed] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ((if QueryClass.OtherHash key.parameter words input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      have hz : Pr[fun result => QueryNewMatch key labels words history (.inl input) result.1 |
          (lazyWorldImpl key inputs labels outside (.inl input)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ => queryNewMatch_coin _ _ _ _ _ result.1
      rw [hz]
      exact bot_le
  | inr input =>
      by_cases ha : Active key inputs labels input
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos ha, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, probEvent_map, Function.comp_def, queryNewMatch_hash]
        exact newMatch_cell_le key inputs labels words history allowed hc ⟨input, ha.1⟩ ha
      · have hz : Pr[fun result => QueryNewMatch key labels words history (.inr input) result.1 |
            (lazyWorldImpl key inputs labels outside (.inr input)).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ hm
          exact ha (entry_active key inputs labels words hgraph input result.1 ((queryNewMatch_hash _ _ _ _ _ _).mp hm).1)
        rw [hz]
        exact bot_le

noncomputable def otherCalls (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) : Nat :=
  QueryCap.calls (QueryClass.OtherHash parameter words) (trace.toList.map fun entry => .inr entry.1)

theorem otherCalls_one (parameter : PublicParameter) (words : OtsReferenceWords) : otherCalls parameter words 1 = 0 := rfl

theorem otherCalls_step (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain)
    (answer : OracleWorld.Range input) (tail : OtsContactTrace.Trace) :
    otherCalls parameter words (hashObservationTrace input answer * tail) =
      (if QueryClass.OtherHash parameter words input then 1 else 0) + otherCalls parameter words tail := by
  cases input with
  | inl input =>
      simp only [hashObservationTrace, one_mul, QueryClass.OtherHash, CausalFrontierProgram.NonmessageHash, false_and, if_false, Nat.zero_add]
  | inr input =>
      simp only [otherCalls, hashObservationTrace, FreeMonoid.toList_mul, FreeMonoid.toList_of,
        List.singleton_append, List.map_cons, QueryCap.calls_cons]

theorem match_query_potential_le (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (outside : NonstructuralRows key.parameter inputs) (words : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : structuralInputs key.parameter inputs → Finset HashOutput)
    (hc : TraceConsistent key inputs labels history allowed) (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorldImpl key inputs labels outside input).run allowed] *
      (if Seen key labels words (history * hashObservationTrace input result.1) then 1 else 0 : ENNReal)) ≤
      (if Seen key labels words history then 1 else 0 : ENNReal) +
        (Fintype.card Digest : ENNReal)⁻¹ * ((if QueryClass.OtherHash key.parameter words input then 1 else 0 : Nat) : ENNReal) := by
  by_cases hs : Seen key labels words history
  · have hnext : ∀ answer, Seen key labels words (history * hashObservationTrace input answer) :=
      fun _ => (seen_mul _ _ _ _ _).mpr (Or.inl hs)
    simp only [if_pos hs, if_pos (hnext _), mul_one]
    exact le_add_of_le_left tsum_probOutput_le_one
  · simpa only [QueryNewMatch, hs, not_false_eq_true, and_true, if_false, zero_add,
      probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero] using queryNewMatch_le key inputs labels hgraph outside words history allowed hc input

theorem match_lazyRun_le {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (outside : NonstructuralRows key.parameter inputs) (words : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : structuralInputs key.parameter inputs → Finset HashOutput) (hc : TraceConsistent key inputs labels history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    Pr[fun result => Seen key labels words (history * result.1.2) |
      lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) allowed] ≤
      (if Seen key labels words history then 1 else 0 : ENNReal) + (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) allowed] *
          (otherCalls key.parameter words result.1.2 : ENNReal) := by
  suffices h : (∑' result, Pr[= result | lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) allowed] *
      (if Seen key labels words (history * result.1.2) then 1 else 0 : ENNReal)) ≤
      (if Seen key labels words history then 1 else 0 : ENNReal) + (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) allowed] *
          (otherCalls key.parameter words result.1.2 : ENNReal) by
    simpa only [mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite] using h
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_potential_le hashObservationTrace (lazyWorldImpl key inputs labels outside)
    (fun history allowed => TraceConsistent key inputs labels history allowed ∧ ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => if Seen key labels words history then 1 else 0)
    _ (otherCalls key.parameter words) _ (otherCalls_one key.parameter words) (otherCalls_step key.parameter words)
    _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent key inputs labels outside allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary key inputs labels outside) (translate key inputs labels input) allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail key inputs labels outside _ allowed hi.2)
  · intro history allowed hi input
    exact match_query_potential_le key inputs labels hgraph outside words history allowed hi.1 input

theorem match_initial_lazyRun_le {Result : Type} (key : SecretKey) (inputs : Finset HashInput) (labels : CanonicalGraphLabels)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (outside : NonstructuralRows key.parameter inputs) (words : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) :
    Pr[fun result => Seen key labels words result.1.2 |
      lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) (fun _ => Finset.univ)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ∑' result,
        Pr[= result | lazyRun key inputs labels outside (QueryPause.traced hashObservationTrace computation) (fun _ => Finset.univ)] *
          (otherCalls key.parameter words result.1.2 : ENNReal) := by
  simpa only [one_mul, if_neg (seen_one key labels words), zero_add] using
    match_lazyRun_le key inputs labels hgraph outside words computation 1 _ (traceConsistent_one key inputs labels) (fun _ => Finset.univ_nonempty)

end SphincsSecurity.Concrete.StructuralObservation
