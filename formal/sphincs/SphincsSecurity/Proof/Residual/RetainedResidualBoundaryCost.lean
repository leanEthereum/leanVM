import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.ResidualSigningProgram
import SphincsSecurity.Proof.Residual.RetainedResidualSigningKernel
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs
set_option backward.isDefEq.respectTransparency false

theorem messageState_memory (parameter : PublicParameter) {inputs : Finset HashInput} (state : State inputs)
    (input : inputs) (answer : HashOutput) (hm : FtsProbeSimulation.MessageHashInput parameter input.val) :
    (messageState parameter state input answer).memory =
      state.memory.applyBoundary (signingBoundaryTrace parameter (.inr input.val) answer) := by
  simp only [messageState, Memory.applyBoundary, Memory.observeMessage, signingBoundaryTrace, if_pos hm]
  rfl

variable (parameter : PublicParameter) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
  (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem lazyByteRun_map {A B : Type} (routing : Routing) (f : A → B)
    (computation : OracleComp OracleWorld A) (state : State inputs) :
    lazyByteRun parameter inputs hencoding words publicReplies selections rows routing (f <$> computation) state =
      Prod.map (Option.map f) id <$> lazyByteRun parameter inputs hencoding words publicReplies selections rows routing computation state := by
  simp only [lazyByteRun, simulateQ_map, lazyRun, runWith, OptionT.run_map, StateT.run_map]
  rfl

attribute [local irreducible] lazyRun environment lazyByteRun

theorem lazyByteRun_boundary_memory {Result : Type} (routing : Routing)
    (computation : OracleComp OracleWorld Result) (hinputs : hashInputs computation ⊆ inputs)
    (hmessage : ResidualByteFrontend.MessageOnly parameter computation) (state : State inputs)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option (Result × SigningBoundaryTrace) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (boundaryComputation parameter computation) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ result.2.memory = state.memory.applyBoundary record.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      have hp : boundaryComputation parameter (pure value) = pure (value, 1) := by
        simp only [boundaryComputation, simulateQ_pure, WriterT.run_pure]
      rw [hp, lazyByteRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact ⟨(value, 1), rfl, (applyBoundary_one state.memory).symm⟩
  | query_bind input next ih =>
      have hnext : ∀ answer, hashInputs (next answer) ⊆ inputs :=
        fun answer => (hashInputs_next_subset input next answer).trans hinputs
      have hmnext : ∀ answer, ResidualByteFrontend.MessageOnly parameter (next answer) :=
        fun answer row hrow => hmessage row ((hashInputs_next_subset input next answer) hrow)
      rw [ResidualByteFrontend.boundaryComputation_query_bind] at hresult
      cases input with
      | inl input =>
          rw [lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨answer, _, hresult⟩ := hresult
          rw [lazyByteRun_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨raw, hraw, hresult⟩ := hresult
          obtain ⟨record, hr, hmemory⟩ := ih answer (hnext answer) (hmnext answer) state hcovered raw hraw
          simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          have heq : raw = (some record, raw.2) := Prod.ext hr rfl
          rw [heq]
          exact ⟨record, rfl, hmemory⟩
      | inr input =>
          change HashOutput → OracleComp OracleWorld Result at next
          have hin := hinputs (mem_hashInputs_hash_bind input next)
          have hm := hmessage input (mem_hashInputs_hash_bind input next)
          rw [lazyByteRun_message_bind parameter inputs hencoding words publicReplies selections rows routing input hin hm _ state hcovered,
            RetainedObservation.bind_nonzero] at hresult
          obtain ⟨reply, hreply, hresult⟩ := hresult
          obtain ⟨_, hrows⟩ := randomOracle_messageState parameter inputs state hcovered ⟨input, hin⟩ reply
            ((mem_support_iff _ _).mpr hreply)
          rw [lazyByteRun_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
          obtain ⟨raw, hraw, hresult⟩ := hresult
          obtain ⟨record, hr, hmemory⟩ := ih reply.1 (hnext reply.1) (hmnext reply.1) _ hrows raw hraw
          simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          have heq : raw = (some record, raw.2) := Prod.ext hr rfl
          rw [heq]
          refine ⟨(record.1, signingBoundaryTrace parameter (.inr input) reply.1 * record.2), rfl, ?_⟩
          change raw.2.memory = state.memory.applyBoundary (signingBoundaryTrace parameter (.inr input) reply.1 * record.2)
          rw [hmemory, messageState_memory parameter state ⟨input, hin⟩ reply.1 hm, ← applyBoundary_mul]

theorem digestWork_memory (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (selected : Option (Randomness × Index × (IndexGroup → FtsLeaf)) × SigningBoundaryTrace) (memory : Memory) :
    (memory.applyBoundary selected.2).accountWork (digestWork known words selections selected).2 =
      memory.applyBoundary (digestWork known words selections selected).1.2 := by
  rcases selected with ⟨selected, trace⟩
  cases selected with
  | none =>
      simp only [digestWork, Memory.accountWork, ResidualByteFrontend.accountWork, Nat.add_zero]
  | some selected =>
      simp only [digestWork, applyBoundary_mul, applyBoundary_pow_none]

theorem lazyByteRun_publicSigningWork_memory (routing : Routing) (root : Digest) (message : Message)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option (PublicSigningRecord × Nat) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message) state result ≠ 0) :
    ∃ work, result.1 = some work ∧ result.2.memory.accountWork work.2 = state.memory.applyBoundary work.1.2 := by
  rw [publicSigningWork_eq_digestWork, lazyByteRun_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨raw, hraw, hresult⟩ := hresult
  obtain ⟨record, hr, hmemory⟩ := lazyByteRun_boundary_memory parameter inputs hencoding words publicReplies selections rows routing
    (publicDigestLoop parameter root message digestAttemptLimit) hinputs
    (ResidualByteFrontend.messageOnly_publicDigestLoop parameter root message digestAttemptLimit) state hcovered raw hraw
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  have heq : raw = (some record, raw.2) := Prod.ext hr rfl
  rw [heq]
  refine ⟨digestWork routing.known words selections record, rfl, ?_⟩
  change raw.2.memory.accountWork _ = _
  rw [hmemory, digestWork_memory]

theorem lazyRun_jointSigningProgram_memory_trace (routing : Routing) (root : Digest) (message : Message)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (result : Option SigningRecord × State inputs)
    (hresult : lazyRun (environment parameter inputs hencoding words publicReplies selections rows)
      (simulateQ (embed inputs routing)
        (ResidualByteFrontend.jointSigningProgram inputs parameter root routing.known words selections message)) state result ≠ 0) :
    ∃ record, result.1 = some record ∧ result.2.memory = state.memory.applyBoundary record.2 := by
  rw [ResidualByteFrontend.jointSigningProgram, simulateQ_bind, lazyRun_bind, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨middle, hmiddle, hresult⟩ := hresult
  rw [← lazyByteRun] at hmiddle
  obtain ⟨work, hw, hpaid⟩ := lazyByteRun_publicSigningWork_memory parameter inputs hencoding words publicReplies selections rows
    routing root message hinputs state hcovered middle hmiddle
  have hcandidates := (lazyByteRun_message_support parameter inputs hencoding words publicReplies selections rows routing
    (ResidualByteFrontend.publicSigningWork parameter root routing.known words selections message)
    (by simpa only [ResidualByteFrontend.hashInputs_publicSigningWork] using hinputs)
    (ResidualByteFrontend.publicSigningWork_messageOnly parameter root routing.known words selections message)
    state hcovered middle hmiddle).2
  have ha' : ∀ coordinate, (middle.2.candidates coordinate).Nonempty := by rw [hcandidates]; exact ha
  rw [hw, Option.elim_some] at hresult
  obtain ⟨actual, hr, hmemory⟩ := lazyRun_completeWork_support parameter inputs hencoding words publicReplies selections rows
    routing work middle.2 ha' result hresult
  exact ⟨_, hr, by rw [hmemory, completePublicSigningRecord_trace]; exact hpaid⟩

theorem checkedHashResult_hashCalls (routing : Routing) (actual : Labels) (seed : inputs → HashOutput)
    (input : inputs) (state : State inputs) :
    (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.hashCalls =
      state.memory.external.hashCalls + 1 := by
  have hp := congrArg (fun result : Option HashOutput × ResidualByteFrontend.State inputs => result.2.memory.hashCalls)
    (hashResult_project parameter inputs hencoding words publicReplies selections rows routing actual seed input state)
  change (hashResult parameter inputs hencoding words publicReplies selections rows routing actual seed input state).2.memory.external.hashCalls = _
  exact hp.trans (ResidualByteFrontend.hashQueryResult_hashCalls parameter inputs words routing.disclosed routing.known
    (ResidualByteAction.freshPrefix parameter inputs hencoding words routing.disclosed routing.known publicReplies selections rows)
    actual seed input (project state))

theorem lazyByteRun_hash_result (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (result : Option HashOutput × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query (.inr input))) state result ≠ 0) :
    ∃ actual seed, result = checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state := by
  unfold lazyByteRun at hresult
  rw [← run_erasure _ _ state ha, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨actual, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨seed, _, hresult⟩ := hresult
  simp only [simulateQ_spec_query, ResidualByteFrontend.checkedTranslate, dif_pos hin] at hresult
  rw [observedRun_checkedHashQuery parameter inputs hencoding words publicReplies selections rows routing actual seed
    ⟨input, hin⟩ state] at hresult
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
  subst result
  exact ⟨actual, seed, rfl⟩

theorem lazyByteRun_hash_hashCalls (routing : Routing) (input : HashInput) (hin : input ∈ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (result : Option HashOutput × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query (.inr input))) state result ≠ 0) :
    result.2.memory.external.hashCalls = state.memory.external.hashCalls + 1 := by
  obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows routing input hin state ha result hresult
  exact checkedHashResult_hashCalls parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state

theorem lazyByteRun_world_hashCalls (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state result ≠ 0) :
    result.2.memory.external.hashCalls = state.memory.external.hashCalls + if input matches .inr _ then 1 else 0 := by
  cases input with
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [lazyByteRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact (Nat.add_zero _).symm
  | inr input =>
      apply lazyByteRun_hash_hashCalls parameter inputs hencoding words publicReplies selections rows routing input _ state ha result hresult
      apply hinputs
      rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
      exact mem_hashInputs_hash_bind input pure

theorem lazyByteRun_world_messageTrace (routing : Routing) (input : OracleWorld.Domain)
    (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (state : State inputs) (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (result : Option (OracleWorld.Range input) × State inputs)
    (hresult : lazyByteRun parameter inputs hencoding words publicReplies selections rows routing
      (liftM (OracleWorld.query input)) state result ≠ 0) :
    result.2.memory.messageCalls = state.memory.messageCalls ++
      result.1.elim [] (fun answer => (signingBoundaryTrace parameter input answer).messageCalls) := by
  cases input with
  | inl input =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl input))), lazyByteRun_random_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [lazyByteRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact (List.append_nil _).symm
  | inr input =>
      have hin : input ∈ inputs := by
        apply hinputs
        rw [← bind_pure (liftM (OracleWorld.query (.inr input)))]
        exact mem_hashInputs_hash_bind input pure
      obtain ⟨actual, seed, rfl⟩ := lazyByteRun_hash_result parameter inputs hencoding words publicReplies selections rows routing input hin state ha result hresult
      have h := checkedHashResult_memory parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state
      dsimp only at h
      have hmessages := congrArg Memory.messageCalls h
      apply hmessages.trans
      generalize (checkedHashResult parameter inputs hencoding words publicReplies selections rows routing actual seed ⟨input, hin⟩ state).1 = answer
      cases answer with
      | none => simp only [Memory.afterReply, Option.elim_none, List.append_nil]
      | some answer =>
          by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
          · simp only [Memory.afterReply, Option.elim_some, Memory.observeMessage, signingBoundaryTrace, if_pos hm]
            rfl
          · simp only [Memory.afterReply, Option.elim_some, Memory.observeMessage, signingBoundaryTrace, if_neg hm]
            exact (List.append_nil _).symm

end SphincsSecurity.Concrete.RetainedResidual
