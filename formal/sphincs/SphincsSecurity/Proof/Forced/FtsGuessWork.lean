import SphincsSecurity.Proof.Forced.FtsGuessReference
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun fixedImpl runWith)
set_option backward.isDefEq.respectTransparency false

variable {Memory : Type}

theorem runWith_bind {First Result : Type}
    (implementation : QueryImpl World (StateT (State Coordinate Digest Memory) SPMF))
    (first : OracleComp World First) (next : First → OracleComp World Result) (state : State Coordinate Digest Memory) :
    runWith implementation (first >>= next) state =
      runWith implementation first state >>= fun middle => runWith implementation (next middle.1) middle.2 := by
  simp only [runWith, simulateQ_bind, StateT.run_bind]

theorem runWith_map {First Result : Type}
    (implementation : QueryImpl World (StateT (State Coordinate Digest Memory) SPMF))
    (function : First → Result) (computation : OracleComp World First) (state : State Coordinate Digest Memory) :
    runWith implementation (function <$> computation) state =
      (fun result => (function result.1, result.2)) <$> runWith implementation computation state := by
  simp only [runWith, simulateQ_map, StateT.run_map]

private theorem map_nonzero {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

theorem fixed_auxiliary_probes (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (input : Auxiliary.Domain) (state : State Coordinate Digest Memory) (result : Auxiliary.Range input × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (liftM (World.query (.inl input))) state result ≠ 0) :
    result.2.probes = state.probes := by
  simp only [fixedRun, runWith, simulateQ_spec_query, fixedImpl, StateT.run_mk, map_nonzero] at hr
  obtain ⟨answer, _, rfl⟩ := hr
  rfl

theorem fixed_hashProgram_probes (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (parameter : PublicParameter) (labels : CanonicalGraphLabels) (input : HashInput)
    (state : State Coordinate Digest Memory) (result : HashOutput × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (hashProgram parameter labels input) state result ≠ 0) :
    result.2.probes ≤ state.probes + 1 := by
  cases hd : FtsProbeSimulation.decodeProbe? parameter input with
  | none =>
      rw [hashProgram, hd] at hr
      rw [fixed_auxiliary_probes environment secrets (.inl (.inr input)) state result hr]
      omega
  | some probe =>
      rw [hashProgram, hd, fixedRun, SecretGuessObservation.runWith_query_bind] at hr
      simp only [fixedImpl, StateT.run_mk, pure_bind] at hr
      split at hr
      · simp only [SecretGuessObservation.runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        subst result
        exact le_rfl
      · have heq := fixed_auxiliary_probes environment secrets (.inl (.inr input)) _ result hr
        simpa only [SecretGuessObservation.afterTrial] using heq.le

theorem fixed_worldProgram_probes (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (parameter : PublicParameter) (labels : CanonicalGraphLabels) (input : OracleWorld.Domain)
    (state : State Coordinate Digest Memory) (result : OracleWorld.Range input × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (worldProgram parameter labels input) state result ≠ 0) :
    result.2.probes ≤ state.probes + (signingBoundaryTrace parameter input result.1).hashCalls := by
  rw [signingBoundaryTrace_hashCalls_eq]
  cases input with
  | inl input =>
      rw [fixed_auxiliary_probes environment secrets (.inl (.inl input)) state result hr]
      exact le_rfl
  | inr input => exact fixed_hashProgram_probes environment secrets parameter labels input state result hr

theorem fixed_signingProgram_probes (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (message : Message) (state : State Coordinate Digest Memory)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (signingProgram message) state result ≠ 0) :
    result.2.probes = state.probes := by
  rw [signingProgram, fixedRun, runWith_bind, RetainedObservation.bind_nonzero] at hr
  obtain ⟨middle, hm, hr⟩ := hr
  have hp := fixed_auxiliary_probes environment secrets (.inr message) state middle hm
  change fixedRun environment secrets (FtsGuessSigning.completeRecord middle.1) middle.2 result ≠ 0 at hr
  rw [FtsGuessSigning.fixedRun_completeRecord] at hr
  simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  subst result
  exact (congrArg Prod.snd (FtsGuessSigning.completedState_counts environment secrets middle.1 middle.2)).trans hp

private theorem two_writers_probes {Source Result ω₁ ω₂ : Type} {spec : OracleSpec Source} [Monoid ω₁] [Monoid ω₂]
    (environment : Environment Auxiliary Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (implementation : QueryImpl spec (WriterT ω₁ (WriterT ω₂ (OracleComp World))))
    (cost : ω₁ → Nat) (hzero : cost 1 = 0) (hmul : ∀ first second, cost (first * second) = cost first + cost second)
    (hquery : ∀ input state result, fixedRun environment secrets ((implementation input).run).run state result ≠ 0 →
      result.2.probes ≤ state.probes + cost result.1.1.2)
    (computation : OracleComp spec Result) (state : State Coordinate Digest Memory)
    (result : ((Result × ω₁) × ω₂) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets ((simulateQ implementation computation).run).run state result ≠ 0) :
    result.2.probes ≤ state.probes + cost result.1.1.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, fixedRun, SecretGuessObservation.runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      simp only [hzero, Nat.add_zero, le_refl]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map,
        fixedRun, runWith_bind, runWith_map, RetainedObservation.bind_nonzero, map_nonzero] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      have hhead := hquery input state middle hm
      have htail := ih middle.1.1.1 middle.2 tail ht
      simp only [hmul]
      omega

theorem fixed_adversaryRun_probes {Result : Type} (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (state : State Coordinate Digest Memory)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (adversaryRun parameter labels computation) state result ≠ 0) :
    result.2.probes ≤ state.probes + result.1.1.2.hashCalls := by
  apply two_writers_probes environment secrets (adversaryImpl parameter labels) SigningBoundaryTrace.hashCalls rfl
    SigningBoundaryTrace.hashCalls_mul _ (OtsPrefix.logged computation) state result hr
  intro input state result hr
  cases input with
  | inl input =>
      simp only [adversaryImpl, WriterT.run_mk, fixedRun, runWith_map, map_nonzero] at hr
      obtain ⟨answer, ha, rfl⟩ := hr
      exact fixed_worldProgram_probes environment secrets parameter labels input state answer ha
  | inr message =>
      simp only [adversaryImpl, WriterT.run_mk, fixedRun, runWith_map, map_nonzero] at hr
      obtain ⟨record, hr, rfl⟩ := hr
      rw [fixed_signingProgram_probes environment secrets message state record hr]
      exact Nat.le_add_right _ _

private theorem traced_map {First Result : Type} (function : First → Result) (computation : OracleComp OracleWorld First) :
    QueryPause.traced hashObservationTrace (function <$> computation) =
      (fun result => (function result.1, result.2)) <$> QueryPause.traced hashObservationTrace computation := by
  simp only [QueryPause.traced, simulateQ_map, WriterT.run_map]

theorem fixed_tracedBoundary_probes {Result : Type} (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels)
    (computation : OracleComp OracleWorld Result) (state : State Coordinate Digest Memory)
    (result : ((Result × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (simulateQ (worldProgram parameter labels)
      (QueryPause.traced hashObservationTrace (boundaryComputation parameter computation))) state result ≠ 0) :
    result.2.probes ≤ state.probes + result.1.1.2.hashCalls := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      simp only [boundaryComputation, simulateQ_pure, WriterT.run_pure, QueryPause.traced_pure,
        fixedRun, SecretGuessObservation.runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact le_rfl
  | query_bind input next ih =>
      simp only [ResidualByteFrontend.boundaryComputation_query_bind, QueryPause.traced_query_bind, traced_map,
        simulateQ_bind, simulateQ_spec_query, simulateQ_map, fixedRun, runWith_bind, runWith_map,
        RetainedObservation.bind_nonzero, map_nonzero] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      have hhead := fixed_worldProgram_probes environment secrets parameter labels input state middle hm
      have htail := ih middle.1 middle.2 tail ht
      simp only [SigningBoundaryTrace.hashCalls_mul]
      omega

theorem fixed_verifyProgram_probes (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (forgery : Forgery) (state : State Coordinate Digest Memory)
    (result : ((Bool × SigningBoundaryTrace) × Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (verifyProgram parameter root labels forgery) state result ≠ 0) :
    result.2.probes ≤ state.probes + result.1.1.2.hashCalls :=
  fixed_tracedBoundary_probes environment secrets parameter labels _ state result hr

abbrev Completed := AdversaryTrace × (Bool × SigningBoundaryTrace) × Trace

def completedWork (result : Completed) : Nat :=
  result.1.1.2.hashCalls + result.2.1.2.hashCalls

theorem fixed_completedRun_probes (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (adversary : Adversary) (state : State Coordinate Digest Memory) (result : Completed × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (completedRun parameter root labels adversary) state result ≠ 0) :
    result.2.probes ≤ state.probes + completedWork result.1 := by
  simp only [completedRun, fixedRun, runWith_bind, SecretGuessObservation.runWith_pure,
    RetainedObservation.bind_nonzero, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨before, hb, checked, hc, rfl⟩ := hr
  have hbefore := fixed_adversaryRun_probes environment secrets parameter labels _ state before hb
  have hchecked := fixed_verifyProgram_probes environment secrets parameter root labels _ before.2 checked hc
  simp only [completedWork]
  omega

end SphincsSecurity.Concrete.FtsGuessHash
