import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.RetainedResidualContext
import SphincsSecurity.Proof.Residual.RetainedResidualRows
import SphincsSecurity.Proof.Residual.RetainedResidualSigningTrace
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable instance signatureFintype : Fintype Signature := by
  classical
  exact Fintype.ofEquiv
    (Randomness × (FtsTree → Digest) × (FtsTree → Fin ftsTreeHeight → Digest) ×
      (Layer → Counter) × (Layer → ChainIndex → Digest) × (PathIndex → Digest))
    { toFun := fun s => ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩
      invFun := fun s => (s.randomness, s.ftsSecret, s.ftsPath, s.counter, s.chainValue, s.authPath)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

noncomputable local instance instFintypeRangeOracleWorldSigningSpec (input : (OracleWorld + SigningSpec).Domain) :
    Fintype ((OracleWorld + SigningSpec).Range input) := by
  cases input <;> infer_instance

noncomputable def requestInputs (key : SecretKey) : (OracleWorld + SigningSpec).Domain → Finset HashInput
  | .inl input => hashInputs (liftM (OracleWorld.query input))
  | .inr message => hashInputs (signWithView key message)

noncomputable def sourceInputs {Result : Type} (key : SecretKey)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) : Finset HashInput :=
  OracleComp.construct (fun _ => ∅)
    (fun input _ tail => requestInputs key input ∪ Finset.univ.biUnion tail) computation

theorem sourceInputs_pure {Result : Type} (key : SecretKey) (value : Result) :
    sourceInputs key (pure value) = ∅ := rfl

theorem sourceInputs_query_bind {Result : Type} (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    sourceInputs key (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      requestInputs key input ∪ Finset.univ.biUnion (fun answer => sourceInputs key (next answer)) := by
  simp only [sourceInputs, OracleComp.construct_query_bind]

theorem requestInputs_subset {Result : Type} (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    requestInputs key input ⊆ sourceInputs key (liftM ((OracleWorld + SigningSpec).query input) >>= next) := by
  rw [sourceInputs_query_bind]
  exact Finset.subset_union_left

theorem sourceInputs_next_subset {Result : Type} (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result)
    (answer : (OracleWorld + SigningSpec).Range input) :
    sourceInputs key (next answer) ⊆ sourceInputs key (liftM ((OracleWorld + SigningSpec).query input) >>= next) := by
  intro row hrow
  rw [sourceInputs_query_bind, Finset.mem_union]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨answer, Finset.mem_univ _, hrow⟩)

noncomputable def fixedSourceImpl {inputs : Finset HashInput} (context : Context inputs) :
    QueryImpl (OracleWorld + SigningSpec) (OptionT (StateT Memory SPMF))
  | .inl input => OptionT.mk <| StateT.mk fun memory =>
      fixedByteRun context.key.parameter context.words context.auxiliary.selections memory.routing
        context.actual context.oracle (liftM (OracleWorld.query input)) memory
  | .inr message => OptionT.mk <| StateT.mk fun memory =>
      (fun record : SigningRecord => (some record.1.1, (memory.applyBoundary record.2).recordSigning message record)) <$>
        𝒟[fixedBoundaryRun context.key.parameter context.oracle (signWithView context.key message)]

noncomputable def fixedSourceRun {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (memory : Memory) : SPMF (Option Result × Memory) :=
  (OptionT.run (simulateQ (fixedSourceImpl context) computation)).run memory

theorem fixedSourceRun_pure {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (value : Result) (memory : Memory) : fixedSourceRun context (pure value) memory = pure (some value, memory) := by
  simp only [fixedSourceRun, simulateQ_pure, OptionT.run_pure, StateT.run_pure]

theorem fixedSourceRun_query_bind {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) (memory : Memory) :
    fixedSourceRun context (liftM ((OracleWorld + SigningSpec).query input) >>= next) memory =
      ((fixedSourceImpl context input).run.run memory >>= fun result =>
        result.1.elim (pure (none, result.2)) (fun answer => fixedSourceRun context (next answer) result.2)) := by
  simp only [fixedSourceRun, simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind]
  apply congrArg (_ >>= ·)
  funext result
  rcases result with ⟨answer, after⟩
  cases answer <;> rfl

theorem Context.external_memory {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) :
    forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
      (externalProgram inputs context.key.parameter context.words context.auxiliary.selections computation) state =
      fixedByteRun context.key.parameter context.words context.auxiliary.selections state.memory.routing
        context.actual context.oracle computation state.memory :=
  observedRun_externalProgram_original_memory context.key.parameter inputs context.encoding context.words
    context.publicReplies context.auxiliary.selections context.auxiliary.rows context.key.otsSecret context.key.ftsSecret
    context.graph context.auxiliary.seed computation hinputs state hcompatible.agrees hcompatible.replies hcovered
    hcompatible.cached hcompatible.structural

theorem Context.signing_memory {inputs : Finset HashInput} (context : Context inputs) (message : Message)
    (hinputs : hashInputs (signWithView context.key message) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) :
    forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
      (signingProgram inputs context.key.parameter context.key.root context.words context.auxiliary.selections message) state =
      (fun record : SigningRecord => (some record.1.1, (state.memory.applyBoundary record.2).recordSigning message record)) <$>
        𝒟[fixedBoundaryRun context.key.parameter context.oracle (signWithView context.key message)] :=
  observedRun_signingProgram_original_memory context.key inputs context.encoding context.graph context.auxiliary
    context.auxiliary_valid context.dummy context.publicReplies message hinputs state hcompatible.agrees hcompatible.replies
    hcovered hcompatible.cached hcompatible.structural

theorem observedRun_request_memory {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain) (hinputs : requestInputs context.key input ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) :
    forgetState <$> observedRun context.environment context.actual context.auxiliary.seed
      (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections input) state =
      (fixedSourceImpl context input).run.run state.memory := by
  cases input with
  | inl input =>
      rw [adversaryImpl, fixedSourceImpl, OptionT.run_mk, StateT.run_mk]
      exact context.external_memory _ hinputs state hcovered hcompatible
  | inr message =>
      rw [adversaryImpl, fixedSourceImpl, OptionT.run_mk, StateT.run_mk]
      exact context.signing_memory message hinputs state hcovered hcompatible

theorem fixedSourceImpl_compatible {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain) (memory : Memory) (hcompatible : Compatible context memory)
    (answer : (OracleWorld + SigningSpec).Range input) (after : Memory)
    (hresult : (fixedSourceImpl context input).run.run memory (some answer, after) ≠ 0) : Compatible context after := by
  cases input with
  | inl input =>
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query] at hresult
      cases input with
      | inl input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨value, _, hresult⟩ := hresult
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq] at hresult
          exact hresult.2 ▸ hcompatible
      | inr input =>
          simp only [fixedByteImpl, OptionT.run_mk, StateT.run_mk, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          have h := fixedHashStep_compatible context input memory hcompatible answer (congrArg Prod.fst hresult).symm
          simpa only [← hresult] using h
  | inr message =>
      simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨record, hrecord, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not, Prod.mk.injEq] at hresult
      exact hresult.2 ▸ originalSigning_compatible context memory hcompatible message record hrecord

theorem observedRun_request_compatible {inputs : Finset HashInput} (context : Context inputs)
    (input : (OracleWorld + SigningSpec).Domain) (hinputs : requestInputs context.key input ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (answer : (OracleWorld + SigningSpec).Range input) (after : State inputs)
    (hresult : observedRun context.environment context.actual context.auxiliary.seed
      (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections input) state (some answer, after) ≠ 0) :
    Compatible context after.memory := by
  have h := map_nonzero _ forgetState (some answer, after) hresult
  rw [observedRun_request_memory context input hinputs state hcovered hcompatible] at h
  exact fixedSourceImpl_compatible context input state.memory hcompatible answer after.memory h

end SphincsSecurity.Concrete.RetainedResidual
