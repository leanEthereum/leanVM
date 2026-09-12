import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualComposition
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

theorem fixedBoundaryRun_bind_query_bound {A B : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld A) (next : A → OracleComp OracleWorld B) (q : Nat)
    (hbound : (computation >>= next).IsQueryBoundP (· matches .inr _) q)
    (result : A × SigningBoundaryTrace) (hresult : 𝒟[fixedBoundaryRun parameter oracle computation] result ≠ 0) :
    result.2.hashCalls ≤ q ∧ (next result.1).IsQueryBoundP (· matches .inr _) (q - result.2.hashCalls) := by
  induction computation using OracleComp.inductionOn generalizing q result with
  | pure value =>
      simp only [fixedBoundaryRun_pure, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      simpa only [SigningBoundaryTrace.hashCalls, FreeMonoid.toList_one, List.length_nil, Nat.sub_zero, pure_bind] using
        And.intro (Nat.zero_le q) hbound
  | query_bind input continuation ih =>
      rw [bind_assoc, isQueryBoundP_query_bind_iff] at hbound
      rw [ResidualByteFrontend.fixedBoundaryRun_query_bind, evalDist_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [evalDist_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨tail, htail, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have h := ih answer _ (hbound.2 answer) tail htail
      rw [SigningBoundaryTrace.hashCalls_mul, signingBoundaryTrace_hashCalls_eq]
      cases input with
      | inl input => simpa only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.zero_add] using h
      | inr input =>
          have hpositive : 0 < q := hbound.1.resolve_left (by simp)
          simp only [↓reduceIte] at h ⊢
          exact ⟨by omega, by simpa only [Nat.sub_sub] using h.2⟩

theorem fixedHashStep_hashCalls (parameter : PublicParameter) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (routing : InterleavedResidual.Routing) (actual : Labels) (oracle : QueryImpl HashSpec Id) (input : HashInput) (memory : Memory) :
    (fixedHashStep parameter words selections routing actual oracle input memory).2.external.hashCalls = memory.external.hashCalls + 1 := by
  rw [fixedHashStep_external]
  exact ResidualByteFrontend.fixedStep_hashCalls parameter words routing.disclosed routing.known actual oracle input memory.external

theorem applyBoundary_recordSigning_hashCalls (memory : Memory) (message : Message) (record : InterleavedResidual.SigningRecord) :
    ((memory.applyBoundary record.2).recordSigning message record).external.hashCalls = memory.external.hashCalls + record.2.hashCalls := rfl

theorem fixedSourceImpl_query_bound {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (q : Nat) (hbound : (simulateQ (expandedAdversaryImpl context.key)
      (liftM ((OracleWorld + SigningSpec).query input) >>= next)).IsQueryBoundP (· matches .inr _) q)
    (memory : Memory) (result : Option ((OracleWorld + SigningSpec).Range input) × Memory)
    (hresult : (fixedSourceImpl context input).run.run memory result ≠ 0) :
    ∃ cost ≤ q, result.2.external.hashCalls = memory.external.hashCalls + cost ∧
      ∀ answer, result.1 = some answer →
        (simulateQ (expandedAdversaryImpl context.key) (next answer)).IsQueryBoundP (· matches .inr _) (q - cost) := by
  cases input with
  | inl input =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inl, isQueryBoundP_query_bind_iff] at hbound
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query] at hresult
      cases input with
      | inl input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨value, _, hresult⟩ := hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          refine ⟨0, Nat.zero_le _, (Nat.add_zero _).symm, ?_⟩
          intro answer heq
          cases Option.some.inj heq
          exact hbound.2 value
      | inr input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          have hpositive : 0 < q := hbound.1.resolve_left (by simp)
          refine ⟨1, hpositive, fixedHashStep_hashCalls _ _ _ _ _ _ _ _, ?_⟩
          intro answer _
          exact hbound.2 answer
  | inr message =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
      change (sign context.key message >>= _).IsQueryBoundP (· matches .inr _) q at hbound
      rw [← signWithView_fst context.key message, bind_map_left] at hbound
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨record, hrecord, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have h := fixedBoundaryRun_bind_query_bound context.key.parameter context.oracle (signWithView context.key message)
        (fun reply => simulateQ (expandedAdversaryImpl context.key) (next reply.1)) q hbound record hrecord
      refine ⟨record.2.hashCalls, h.1, applyBoundary_recordSigning_hashCalls memory message record, ?_⟩
      intro answer heq
      cases Option.some.inj heq
      exact h.2

theorem fixedSourceRun_hashCalls_le {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (q : Nat)
    (hbound : (simulateQ (expandedAdversaryImpl context.key) computation).IsQueryBoundP (· matches .inr _) q)
    (memory : Memory) (result : Option Result × Memory) (hresult : fixedSourceRun context computation memory result ≠ 0) :
    result.2.external.hashCalls ≤ memory.external.hashCalls + q := by
  induction computation using OracleComp.inductionOn generalizing q memory result with
  | pure value =>
      simp only [fixedSourceRun_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [fixedSourceRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, middle⟩, hmiddle, hresult⟩ := hresult
      obtain ⟨cost, hcost, hpaid, hnext⟩ := fixedSourceImpl_query_bound context input next q hbound memory (answer, middle) hmiddle
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hpaid.trans_le (Nat.add_le_add_left hcost _)
      | some answer =>
          have h := ih answer (q - cost) (hnext answer rfl) middle result hresult
          rw [hpaid] at h
          omega

theorem observedRun_source_hashCalls_le {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (hinputs : sourceInputs context.key computation ⊆ inputs)
    (q : Nat) (hbound : (simulateQ (expandedAdversaryImpl context.key) computation).IsQueryBoundP (· matches .inr _) q)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (result : Option Result × State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections) computation) state result ≠ 0) :
    result.2.memory.external.hashCalls ≤ state.memory.external.hashCalls + q := by
  have h := map_nonzero _ forgetState result hresult
  rw [observedRun_source_memory context computation hinputs state hcovered hcompatible] at h
  exact fixedSourceRun_hashCalls_le context computation q hbound state.memory (forgetState result) h

end SphincsSecurity.Concrete.RetainedResidual
