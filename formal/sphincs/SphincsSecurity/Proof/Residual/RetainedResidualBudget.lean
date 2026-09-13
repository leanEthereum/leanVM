import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualSuccessTransfer
import SphincsSecurity.Proof.Reference.FixedQueryBound
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

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
    (q : Nat) (hbound : FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key)
      (liftM ((OracleWorld + SigningSpec).query input) >>= next)) q)
    (memory : Memory) (result : Option ((OracleWorld + SigningSpec).Range input) × Memory)
    (hresult : (fixedSourceImpl context input).run.run memory result ≠ 0) :
    ∃ cost ≤ q, result.2.external.hashCalls = memory.external.hashCalls + cost ∧
      ∀ answer, result.1 = some answer →
        FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key) (next answer)) (q - cost) := by
  cases input with
  | inl input =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inl] at hbound
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
          exact (fixedHashQueryBound_query_bind context.oracle (.inl input) _ q hbound value
            (by simp [fixedHashWorld])).2
      | inr input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          have hquery := fixedHashQueryBound_query_bind context.oracle (.inr input) _ q hbound
            (context.oracle input) (by simp [fixedHashWorld])
          refine ⟨1, hquery.1, fixedHashStep_hashCalls _ _ _ _ _ _ _ _, ?_⟩
          intro answer heq
          rcases fixedHashStep_answer context input memory with hstop | hlive
          · rw [hstop] at heq; contradiction
          · rw [hlive] at heq
            cases Option.some.inj heq
            exact hquery.2
  | inr message =>
      rw [simulateQ_expandedAdversaryImpl_query_bind_inr] at hbound
      change FixedHashQueryBound context.oracle (sign context.key message >>= _) q at hbound
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
    (hbound : FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key) computation) q)
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
    (q : Nat) (hbound : FixedHashQueryBound context.oracle (simulateQ (expandedAdversaryImpl context.key) computation) q)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (result : Option Result × State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections) computation) state result ≠ 0) :
    result.2.memory.external.hashCalls ≤ state.memory.external.hashCalls + q := by
  have h := map_nonzero _ forgetState result hresult
  rw [observedRun_source_memory context computation hinputs state hcovered hcompatible] at h
  exact fixedSourceRun_hashCalls_le context computation q hbound state.memory (forgetState result) h

end SphincsSecurity.Concrete.RetainedResidual
