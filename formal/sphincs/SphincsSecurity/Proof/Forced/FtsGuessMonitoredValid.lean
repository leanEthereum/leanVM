import SphincsSecurity.Proof.Forced.FtsGuessMonitoredStep
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State forcedTrial environment)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput hashInputs UniformTableCompletion.complete

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)

/-! ### The cached forced run is a probability law -/

theorem evalDist_probComp_lift {Result : Type} (computation : ProbComp Result) :
    𝒟[computation] = (liftM (liftM computation : PMF Result) : SPMF Result) := by
  apply SPMF.ext
  intro result
  rw [SPMF.liftM_apply, ← PMF.probOutput_eq_apply]
  rfl

theorem probComp_bind_const {Result Other : Type} (computation : ProbComp Result) (after : SPMF Other) :
    (𝒟[computation] >>= fun _ => after) = after := by
  rw [evalDist_probComp_lift]
  exact RetainedObservation.lift_bind_const _ _

theorem cachedSeedRun_seedLift_query_bind_const {Other : Type} (input : (SeedSpec inputs).Domain)
    (cache : QueryCache HashSpec) (after : SPMF Other) :
    (cachedSeedRun inputs (seedLift inputs input) cache >>= fun _ => after) = after := by
  cases input with
  | inl input =>
      simp only [cachedSeedRun, seedLift, simulateQ_spec_query, cachedSeedImpl, StateT.run_mk, forcedSeedAuxiliary,
        bind_map_left]
      exact probComp_bind_const _ after
  | inr input =>
      simp only [cachedSeedRun, seedLift, simulateQ_spec_query, cachedSeedImpl, StateT.run_mk]
      exact probComp_bind_const _ after

theorem cachedSeedRun_seedLift_bind_const {Result Other : Type} (computation : OracleComp (SeedSpec inputs) Result)
    (cache : QueryCache HashSpec) (after : SPMF Other) :
    (cachedSeedRun inputs (simulateQ (seedLift inputs) computation) cache >>= fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing cache with
  | pure value => rw [simulateQ_pure, cachedSeedRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, cachedSeedRun_bind, bind_assoc]
      simp only [ih]
      exact cachedSeedRun_seedLift_query_bind_const inputs input cache after

theorem cachedAuxiliary_bind_const {Other : Type} (input : Auxiliary.Domain) (cache : QueryCache HashSpec)
    (after : SPMF Other) :
    (cachedAuxiliary parameter root otsSecret labels inputs hencoding selections rows dummy input cache >>= fun _ => after) =
      after :=
  cachedSeedRun_seedLift_bind_const inputs _ cache after

theorem forcedTrial_bind_const {Other : Type} (state : State Coordinate Digest PUnit)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (coordinate : Coordinate) (candidate : Digest)
    (after : SPMF Other) :
    (forcedTrial slot state coordinate candidate >>= fun _ => after) = after := by
  by_cases he : SecretGuessObservation.EligibleAt slot state coordinate candidate
  · rw [forcedTrial, if_pos he, pure_bind]
  · rw [forcedTrial, if_neg he, SecretGuessObservation.trial, bind_assoc]
    simp only [pure_bind]
    rw [complete_of_nonempty _ ha]
    exact RetainedObservation.lift_bind_const _ _

theorem cell_bind_const {Other : Type} (allowed : Finset Digest) (ha : allowed.Nonempty) (after : SPMF Other) :
    (cell allowed >>= fun _ => after) = after := by
  rw [cell, dif_pos ha]
  exact RetainedObservation.lift_bind_const _ _

theorem cachedForcedImpl_bind_const {Other : Type} (input : World.Domain) (state : CachedState)
    (ha : ∀ coordinate, (state.2.allowed coordinate).Nonempty) (after : SPMF Other) :
    ((cachedForcedImpl parameter root otsSecret labels inputs hencoding selections rows dummy slot input).run state >>=
      fun _ => after) = after := by
  cases input with
  | inl input =>
      simp only [cachedForcedImpl, StateT.run_mk, bind_map_left]
      exact cachedAuxiliary_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy input state.1 after
  | inr input =>
      cases input with
      | inl probe =>
          rcases probe with ⟨coordinate, candidate⟩
          simp only [cachedForcedImpl, StateT.run_mk, bind_map_left]
          exact forcedTrial_bind_const slot state.2 ha coordinate candidate after
      | inr coordinate =>
          simp only [cachedForcedImpl, StateT.run_mk, bind_map_left]
          exact cell_bind_const _ (ha coordinate) after

theorem cachedForcedImpl_nonempty (input : World.Domain) (state : CachedState)
    (ha : ∀ coordinate, (state.2.allowed coordinate).Nonempty) (result : World.Range input × CachedState)
    (hr : (cachedForcedImpl parameter root otsSecret labels inputs hencoding selections rows dummy slot input).run state result ≠ 0) :
    ∀ coordinate, (result.2.2.allowed coordinate).Nonempty := by
  rw [← cachedForcedRun_query] at hr
  exact cachedForcedRun_nonempty parameter root otsSecret labels inputs hencoding selections rows dummy slot
    (liftM (World.query input)) state.1 state.2 ha result hr

theorem cachedForcedRun_bind_const {Result Other : Type} (computation : OracleComp World Result) (state : CachedState)
    (ha : ∀ coordinate, (state.2.allowed coordinate).Nonempty) (after : SPMF Other) :
    (cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot computation state >>=
      fun _ => after) = after := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => rw [cachedForcedRun_pure, pure_bind]
  | query_bind input next ih =>
      rw [cachedForcedRun_query_bind, bind_assoc]
      rw [RetainedObservation.bind_congr _ _ (fun _ => after) (fun result hr =>
        ih result.1 result.2 (cachedForcedImpl_nonempty parameter root otsSecret labels inputs hencoding selections rows dummy slot
          input state ha result hr))]
      exact cachedForcedImpl_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot input state ha after

theorem tsum_cachedForcedRun_eq_one {Result : Type} (computation : OracleComp World Result) (state : CachedState)
    (ha : ∀ coordinate, (state.2.allowed coordinate).Nonempty) :
    (∑' result, Pr[= result | cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      computation state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (cachedForcedRun_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot computation state ha (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

/-! ### Cached-state forms of the forced-run lemmas -/

theorem cachedSigning_mem_support_sign' (message : Message) (state : CachedState)
    (ha : ∀ coordinate, (state.2.allowed coordinate).Nonempty)
    (hauxiliary : ∀ seed : inputs → HashOutput,
      (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) state result ≠ 0)
    (secrets : Coordinate → Digest) (hsecrets : complete result.2.2.allowed secrets ≠ 0) :
    result.1.1.1 ∈ support (sign ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ message) := by
  rcases state with ⟨cache, guess⟩
  exact cachedSigning_mem_support_sign parameter root otsSecret labels inputs hencoding selections rows dummy slot message cache guess ha
    hauxiliary result hr secrets hsecrets

theorem cachedForcedRun_signingProgram' (message : Message) (state : CachedState)
    (ha : ∀ coordinate, (state.2.allowed coordinate).Nonempty)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (auxiliary : QueryImpl Auxiliary ProbComp) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) state =
      (complete state.2.allowed >>= fun secrets =>
        (fun result => (completePublicSigningRecord (fun index tree leaf => secrets (index, tree, leaf)) result.1,
          (result.2, FtsGuessSigning.completedState (environment auxiliary) secrets result.1 state.2))) <$>
          𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root (known otsSecret labels)
            (referenceFamilyWords selections dummy) selections message)).run state.1]) := by
  rcases state with ⟨cache, guess⟩
  exact cachedForcedRun_signingProgram parameter root otsSecret labels inputs hencoding selections rows dummy slot message cache guess ha
    hinputs auxiliary

theorem cachedForcedRun_world_unif' (sample : unifSpec.Domain) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels (.inl sample)) state =
      (fun answer => (answer, state)) <$> 𝒟[(liftM (unifSpec.query sample) : ProbComp _)] := by
  rcases state with ⟨cache, guess⟩
  exact cachedForcedRun_world_unif parameter root otsSecret labels inputs hencoding selections rows dummy slot sample cache guess

theorem cachedForcedRun_world_message' (input : HashInput) (hin : input ∈ inputs)
    (hmessage : FtsProbeSimulation.MessageHashInput parameter input) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels (.inr input)) state =
      (fun result => (result.1, (result.2, state.2))) <$> 𝒟[(romImpl (.inr input)).run state.1] := by
  rcases state with ⟨cache, guess⟩
  exact cachedForcedRun_world_message parameter root otsSecret labels inputs hencoding selections rows dummy slot input hin hmessage
    cache guess

theorem cachedForcedRun_world_hash_support' (input : HashInput) (state : CachedState) (result : HashOutput × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels (.inr input)) state result ≠ 0) :
    (∀ other, other ≠ input → result.2.1 other = state.1 other) ∧ state.1 ≤ result.2.1 ∧
      QueryCache.enncard result.2.1 ≤ QueryCache.enncard state.1 + 1 := by
  rcases state with ⟨cache, guess⟩
  exact cachedForcedRun_world_hash_support parameter root otsSecret labels inputs hencoding selections rows dummy slot input cache guess
    result hr

/-! ### Valid monitored states -/

def Valid (state : MonitoredState) : Prop := ∀ coordinate, (state.1.2.allowed coordinate).Nonempty

variable (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

theorem monitoredStep_forced (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    forcedAdversaryStep parameter root otsSecret labels inputs hencoding selections rows dummy slot input state.1
      (result.1, result.2.1) ≠ 0 := by
  have h := map_nonzero_of _ (fun result => (result.1, result.2.1)) result hresult
  rwa [monitoredStep_erasure] at h

theorem monitoredStep_valid (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) : Valid result.2 := by
  have h := monitoredStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    input state result hresult
  rw [forcedAdversaryStep] at h
  exact cachedForcedRun_nonempty parameter root otsSecret labels inputs hencoding selections rows dummy slot _ state.1.1 state.1.2 hvalid
    _ h

theorem monitoredStep_allowed_subset (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState)
    (result : AdversaryStep input × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state result ≠ 0) :
    ∀ coordinate, result.2.1.2.allowed coordinate ⊆ state.1.2.allowed coordinate := by
  have h := monitoredStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    input state result hresult
  rw [forcedAdversaryStep] at h
  exact cachedForcedRun_allowed_subset parameter root otsSecret labels inputs hencoding selections rows dummy slot _ state.1.1 state.1.2
    _ h

theorem monitoredStep_bind_const {Other : Type} (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState)
    (hvalid : Valid state) (after : SPMF Other) :
    (monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>=
      fun _ => after) = after := by
  have h := cachedForcedRun_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot
    ((adversaryImpl parameter labels input).run.run) state.1 hvalid after
  rw [← forcedAdversaryStep, ← monitoredStep_erasure, bind_map_left] at h
  exact h

theorem tsum_monitoredStep_eq_one (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState) (hvalid : Valid state) :
    (∑' result, Pr[= result | monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
      stopAfter input state]) = 1 := by
  have h := congrArg (fun law : SPMF Unit => Pr[= () | law])
    (monitoredStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state hvalid (pure ()))
  simpa only [probOutput_bind_eq_tsum, probOutput_pure_self, mul_one] using h

theorem monitoredWorldStep_bind_const {Other : Type} (input : OracleWorld.Domain) (state : MonitoredState)
    (hvalid : Valid state) (after : SPMF Other) :
    (monitoredWorldStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter input state >>=
      fun _ => after) = after :=
  monitoredStep_bind_const parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (.inl input) state hvalid after

/-! ### Input coverage along the run -/

def CoveredRun (computation : OracleComp (OracleWorld + SigningSpec) Forgery) (state : MonitoredState) : Prop :=
  ∀ secrets : Coordinate → Digest, complete state.1.2.allowed secrets ≠ 0 →
    coveredInputs ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ computation ⊆ inputs

theorem exists_complete_ne_zero (allowed : Coordinate → Finset Digest) (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    ∃ secrets, complete allowed secrets ≠ 0 :=
  ⟨fun coordinate => (ha coordinate).choose, complete_ne_zero_of_mem allowed _ (fun coordinate => (ha coordinate).choose_spec)⟩

theorem complete_ne_zero_of_subset (before after : Coordinate → Finset Digest) (hsubset : ∀ coordinate, after coordinate ⊆ before coordinate)
    (secrets : Coordinate → Digest) (hsecrets : complete after secrets ≠ 0) : complete before secrets ≠ 0 :=
  complete_ne_zero_of_mem before secrets (fun coordinate => hsubset coordinate (mem_of_complete_ne_zero after secrets hsecrets coordinate))

theorem covered_world_mem (input : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query (.inl (.inr input))) >>= next) state) :
    input ∈ inputs := by
  obtain ⟨secrets, hsecrets⟩ := exists_complete_ne_zero state.1.2.allowed hvalid
  exact hcovered secrets hsecrets (coveredInputs_world _ input next)

set_option linter.constructorNameAsVariable false in
theorem covered_world_inputs (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query (.inl input)) >>= next) state) :
    hashInputs (liftM (OracleWorld.query input)) ⊆ inputs := by
  cases input with
  | inl sample =>
      rw [← bind_pure (liftM (OracleWorld.query (.inl sample))), hashInputs_query_bind]
      intro row hrow
      rw [Finset.mem_union, Finset.mem_biUnion] at hrow
      rcases hrow with hrow | ⟨_, _, hrow⟩ <;> simp only [hashInputs_pure, Finset.notMem_empty] at hrow
  | inr hash =>
      rw [← bind_pure (liftM (OracleWorld.query (.inr hash))), hashInputs_query_bind]
      intro row hrow
      rw [Finset.mem_union, Finset.mem_biUnion] at hrow
      rcases hrow with hrow | ⟨_, _, hrow⟩
      · rw [Finset.mem_singleton] at hrow
        subst row
        exact covered_world_mem parameter root otsSecret inputs hash next state hvalid hcovered
      · simp only [hashInputs_pure, Finset.notMem_empty] at hrow

theorem covered_sign_digest (message : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) state) :
    hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs := by
  obtain ⟨secrets, hsecrets⟩ := exists_complete_ne_zero state.1.2.allowed hvalid
  let key : SecretKey := ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
  have h := (coveredInputs_sign key message next).trans (hcovered secrets hsecrets)
  rw [← publicDigestLoop_eq key message digestAttemptLimit] at h
  exact h

theorem covered_world_next (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query (.inl input)) >>= next) state)
    (result : AdversaryStep (.inl input) × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (.inl input) state result ≠ 0) :
    CoveredRun parameter root otsSecret inputs (next result.1.1.1) result.2 := by
  intro secrets hsecrets
  have hbefore := complete_ne_zero_of_subset _ _
    (monitoredStep_allowed_subset parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (.inl input) state result hresult) secrets hsecrets
  exact (coveredInputs_world_next _ input next result.1.1.1).trans (hcovered secrets hbefore)

theorem covered_sign_next (message : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (state : MonitoredState) (hvalid : Valid state)
    (hauxiliary : ∀ seed : inputs → HashOutput,
      (⟨selections, rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support)
    (hcovered : CoveredRun parameter root otsSecret inputs (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) state)
    (result : AdversaryStep (.inr message) × MonitoredState)
    (hresult : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (.inr message) state result ≠ 0) :
    CoveredRun parameter root otsSecret inputs (next result.1.1.1) result.2 := by
  intro secrets hsecrets
  have hbefore := complete_ne_zero_of_subset _ _
    (monitoredStep_allowed_subset parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (.inr message) state result hresult) secrets hsecrets
  have hforced := monitoredStep_forced parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    (.inr message) state result hresult
  rw [forcedAdversaryStep_sign] at hforced
  obtain ⟨raw, hraw, heq⟩ := map_nonzero_source' _ _ _ hforced
  have hstate : result.2.1 = raw.2 := congrArg Prod.snd heq
  have hsignature : result.1.1.1 = raw.1.1.1 := congrArg (fun r => r.1.1.1) heq
  rw [hstate] at hsecrets
  have hsupport := cachedSigning_mem_support_sign' parameter root otsSecret labels inputs hencoding selections rows dummy slot message
    state.1 hvalid hauxiliary raw hraw secrets hsecrets
  rw [hsignature]
  exact (coveredInputs_sign_next _ message next raw.1.1.1 hsupport).trans (hcovered secrets hbefore)

theorem covered_pure (forgery : Forgery) (state : MonitoredState) (hvalid : Valid state)
    (hcovered : CoveredRun parameter root otsSecret inputs (pure forgery) state) :
    hashInputs (liftM (verify ⟨root, parameter⟩ forgery.message forgery.signature : OracleComp HashSpec Bool) :
      OracleComp OracleWorld Bool) ⊆ inputs := by
  obtain ⟨secrets, hsecrets⟩ := exists_complete_ne_zero state.1.2.allowed hvalid
  have h := hcovered secrets hsecrets
  rwa [coveredInputs_pure] at h

theorem hashInputs_world_next {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) (answer : OracleWorld.Range input) :
    hashInputs (next answer) ⊆ hashInputs (liftM (OracleWorld.query input) >>= next) := by
  rw [hashInputs_query_bind]
  intro row hrow
  rw [Finset.mem_union, Finset.mem_biUnion]
  exact Or.inr ⟨answer, Finset.mem_univ _, hrow⟩

theorem hashInputs_world_query {Result : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld Result) :
    hashInputs (liftM (OracleWorld.query input)) ⊆ hashInputs (liftM (OracleWorld.query input) >>= next) := by
  intro row hrow
  rw [hashInputs_query_bind, Finset.mem_union]
  left
  cases input with
  | inl sample =>
      exfalso
      rw [← bind_pure (liftM (OracleWorld.query (.inl sample))), hashInputs_query_bind, Finset.mem_union, Finset.mem_biUnion] at hrow
      rcases hrow with hrow | ⟨_, _, hrow⟩ <;> simp only [hashInputs_pure, Finset.notMem_empty] at hrow
  | inr hash =>
      rw [← bind_pure (liftM (OracleWorld.query (.inr hash))), hashInputs_query_bind, Finset.mem_union, Finset.mem_biUnion] at hrow
      rcases hrow with hrow | ⟨_, _, hrow⟩
      · exact hrow
      · simp only [hashInputs_pure, Finset.notMem_empty] at hrow

end SphincsSecurity.Concrete.FtsGuessHash
