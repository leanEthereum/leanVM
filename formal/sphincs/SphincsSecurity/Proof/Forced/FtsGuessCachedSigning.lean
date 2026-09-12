import SphincsSecurity.Proof.Forced.FtsGuessCachedForced
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion CanonicalProbeRouting
open FtsGuessSigning (Coordinate)
open FtsProbeSimulation (MessageHashInput messageAnswers)
open SecretGuessObservation (State forcedRun lazyRun fixedRun disclosure environment plainAfterDisclosure)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput

theorem map_nonzero_of {A B : Type} (law : SPMF A) (f : A → B) (value : A) (hvalue : law value ≠ 0) :
    (f <$> law) (f value) ≠ 0 := by
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
  exact ⟨value, hvalue, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩

theorem map_nonzero_source' {A B : Type} (law : SPMF A) (f : A → B) (result : B)
    (hresult : (f <$> law) result ≠ 0) : ∃ source, law source ≠ 0 ∧ result = f source := by
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨source, hsource, hresult⟩ := hresult
  exact ⟨source, hsource, by simpa only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using hresult⟩

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)

theorem cachedForcedRun_query (input : World.Domain) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (liftM (World.query input)) state =
      (cachedForcedImpl parameter root otsSecret labels inputs hencoding selections rows dummy slot input).run state := by
  rw [← bind_pure (liftM (World.query input)), cachedForcedRun_query_bind]
  simp only [cachedForcedRun_pure, Prod.mk.eta, bind_pure]

/-! ### Fixed-seed support -/

theorem seedAllowed_nonempty (cache : QueryCache HashSpec) (input : inputs) : (seedAllowed inputs cache input).Nonempty := by
  unfold seedAllowed
  cases cache input.val <;> simp

theorem seedProgram_forced_fixed {Result : Type} (seed : inputs → HashOutput) (computation : OracleComp World Result)
    (state : State Coordinate Digest PUnit) :
    simulateQ (UniformTableObservation.fixedImpl forcedSeedAuxiliary seed)
      (SecretGuessObservation.forcedProgram (seedProgram parameter root otsSecret labels inputs hencoding selections rows dummy)
        (sampleForcedBool inputs) (sampleForcedDigest inputs) slot computation state) =
      forcedRun (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy)) slot
        computation state := by
  apply SecretGuessObservation.simulateQ_forcedProgram
  · intro input
    rw [seedProgram, seedLift_fixed, referenceProgram_fixed]
  · intro law
    simp only [sampleForcedBool, simulateQ_spec_query, UniformTableObservation.fixedImpl, forcedSeedAuxiliary]
  · intro law
    simp only [sampleForcedDigest, simulateQ_spec_query, UniformTableObservation.fixedImpl, forcedSeedAuxiliary]

/-- A supported cached run is a supported fixed-seed forced run for some seed agreeing with the initial cache. -/
theorem cachedForcedRun_fixed_seed {Result : Type} (computation : OracleComp World Result)
    (cache : QueryCache HashSpec) (state : State Coordinate Digest PUnit) (result : Result × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot computation (cache, state) result ≠ 0) :
    ∃ seed : inputs → HashOutput, (∀ (input : inputs) (output : HashOutput), cache input.val = some output → seed input = output) ∧
      forcedRun (environment (referenceAnswers parameter root otsSecret labels inputs hencoding ⟨selections, rows, seed⟩ dummy)) slot
        computation state (result.1, result.2.2) ≠ 0 := by
  rw [cachedForcedRun_seed] at hr
  obtain ⟨raw, hraw, heq⟩ := map_nonzero_source' _ _ _ hr
  have hproj := map_nonzero_of _ (Prod.map id (seedAllowed inputs)) raw hraw
  rw [cachedSeedRun_project, ← UniformTableObservation.run_erasure _ _ _ (seedAllowed_nonempty inputs cache),
    RetainedObservation.bind_nonzero] at hproj
  obtain ⟨seed, hseed, hobserved⟩ := hproj
  refine ⟨seed, ?_, ?_⟩
  · intro input output houtput
    rw [complete_apply] at hseed
    split_ifs at hseed with hmem
    · have h := hmem input
      simpa only [seedAllowed, houtput, Option.elim_some, Finset.mem_singleton] using h
    · exact absurd rfl hseed
  · have h := map_nonzero_of _ Prod.fst _ hobserved
    rw [UniformTableObservation.observedRun_forget, seedProgram_forced_fixed] at h
    simpa only [heq, Prod.map_fst, id_eq] using h

theorem cachedForcedRun_nonempty {Result : Type} (computation : OracleComp World Result)
    (cache : QueryCache HashSpec) (state : State Coordinate Digest PUnit)
    (ha : ∀ coordinate, (state.allowed coordinate).Nonempty) (result : Result × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot computation (cache, state) result ≠ 0) :
    ∀ coordinate, (result.2.2.allowed coordinate).Nonempty := by
  obtain ⟨seed, _, hforced⟩ := cachedForcedRun_fixed_seed parameter root otsSecret labels inputs hencoding selections rows dummy slot
    computation cache state result hr
  exact SecretGuessObservation.forcedRun_nonempty _ slot computation state ha _ hforced

/-! ### Auxiliary hash queries -/

theorem cachedAuxiliary_unif (sample : unifSpec.Domain) (cache : QueryCache HashSpec) :
    cachedAuxiliary parameter root otsSecret labels inputs hencoding selections rows dummy (.inl (.inl sample)) cache =
      (fun answer => (answer, cache)) <$> 𝒟[(liftM (unifSpec.query sample) : ProbComp _)] := by
  rw [cachedAuxiliary, seedProgram]
  change cachedSeedRun inputs (simulateQ (seedLift inputs) (liftM ((SeedSpec inputs).query (.inl sample)))) cache = _
  rw [simulateQ_spec_query, seedLift, cachedSeedRun, simulateQ_spec_query]
  rfl

theorem cachedAuxiliary_message (input : inputs) (hmessage : MessageHashInput parameter input.val) (cache : QueryCache HashSpec) :
    cachedAuxiliary parameter root otsSecret labels inputs hencoding selections rows dummy (.inl (.inr input.val)) cache =
      𝒟[(romImpl (.inr input.val)).run cache] := by
  rw [cachedAuxiliary, seedProgram,
    referenceProgram_message parameter root otsSecret labels inputs hencoding selections rows dummy input hmessage,
    simulateQ_spec_query, seedLift, cachedSeedRun, simulateQ_spec_query]
  rfl

/-- One seed-table hash cell at `input` moves the cache at most at `input`, never removes rows, and adds at most one. -/
theorem cachedSeedRun_residualProgram_support {Row : Type} (embed : Row → inputs) (table : Row → HashOutput)
    (input : HashInput) (cache : QueryCache HashSpec) (result : HashOutput × QueryCache HashSpec)
    (hr : cachedSeedRun inputs (simulateQ (seedLift inputs) (residualProgram inputs embed table input)) cache result ≠ 0) :
    (∀ other, other ≠ input → result.2 other = cache other) ∧ cache ≤ result.2 ∧
      QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
  by_cases hi : input ∈ inputs
  · rw [residualProgram, dif_pos hi] at hr
    by_cases hrange : (⟨input, hi⟩ : inputs) ∈ Set.range embed
    · rw [dif_pos hrange, simulateQ_pure, cachedSeedRun_pure] at hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact ⟨fun _ _ => rfl, le_rfl, le_self_add⟩
    · rw [dif_neg hrange, simulateQ_spec_query, seedLift, cachedSeedRun, simulateQ_spec_query] at hr
      change 𝒟[(randomOracle (spec := HashSpec) input).run cache] result ≠ 0 at hr
      have hmem : result ∈ support ((randomOracle (spec := HashSpec) input).run cache) :=
        (mem_support_iff_evalDist_apply_ne_zero _ _).mpr hr
      cases hc : cache input with
      | some output =>
          rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hmem
          subst result
          exact ⟨fun _ _ => rfl, le_rfl, le_self_add⟩
      | none =>
          rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hmem
          obtain ⟨output, _, rfl⟩ := hmem
          refine ⟨fun other hne => QueryCache.cacheQuery_of_ne cache output hne, QueryCache.le_cacheQuery cache hc, ?_⟩
          exact (enncard_cacheQuery_of_fresh cache input output hc).le
  · rw [residualProgram, dif_neg hi, simulateQ_pure, cachedSeedRun_pure] at hr
    simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
    subst result
    exact ⟨fun _ _ => rfl, le_rfl, le_self_add⟩

theorem cachedAuxiliary_hash_support (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec)
    (hr : cachedAuxiliary parameter root otsSecret labels inputs hencoding selections rows dummy (.inl (.inr input)) cache result ≠ 0) :
    (∀ other, other ≠ input → result.2 other = cache other) ∧ cache ≤ result.2 ∧
      QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
  rw [cachedAuxiliary, seedProgram] at hr
  change cachedSeedRun inputs (simulateQ (seedLift inputs) (auxiliaryHashProgram parameter otsSecret labels inputs hencoding rows input)) cache
    result ≠ 0 at hr
  have hpure (value : HashOutput) (hp : cachedSeedRun inputs (simulateQ (seedLift inputs) (pure value)) cache result ≠ 0) :
      (∀ other, other ≠ input → result.2 other = cache other) ∧ cache ≤ result.2 ∧
        QueryCache.enncard result.2 ≤ QueryCache.enncard cache + 1 := by
    rw [simulateQ_pure, cachedSeedRun_pure] at hp
    simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hp
    subst result
    exact ⟨fun _ _ => rfl, le_rfl, le_self_add⟩
  unfold auxiliaryHashProgram at hr
  cases hp : FtsProbeSimulation.decodeProbe? parameter input with
  | some probe =>
      rw [hp] at hr
      exact cachedSeedRun_residualProgram_support inputs _ rows input cache result hr
  | none =>
      rw [hp] at hr
      cases hd : decodePosition parameter input with
      | none =>
          rw [hd] at hr
          exact cachedSeedRun_residualProgram_support inputs _ rows input cache result hr
      | some position =>
          rw [hd] at hr
          dsimp only at hr
          split_ifs at hr with hcanonical
          · exact hpure _ hr
          · exact cachedSeedRun_residualProgram_support inputs _ rows input cache result hr

/-! ### World queries -/

theorem cachedForcedRun_world_unif (sample : unifSpec.Domain) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels (.inl sample)) (cache, state) =
      (fun answer => (answer, (cache, state))) <$> 𝒟[(liftM (unifSpec.query sample) : ProbComp _)] := by
  rw [worldProgram, cachedForcedRun_query]
  simp only [cachedForcedImpl, StateT.run_mk, cachedAuxiliary_unif, Functor.map_map]

theorem cachedForcedRun_world_message (input : HashInput) (hin : input ∈ inputs) (hmessage : MessageHashInput parameter input)
    (cache : QueryCache HashSpec) (state : State Coordinate Digest PUnit) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels (.inr input)) (cache, state) =
      (fun result => (result.1, (result.2, state))) <$> 𝒟[(romImpl (.inr input)).run cache] := by
  rw [worldProgram, hashProgram, message_not_probe parameter input hmessage]
  rw [cachedForcedRun_query]
  simp only [cachedForcedImpl, StateT.run_mk]
  rw [cachedAuxiliary_message parameter root otsSecret labels inputs hencoding selections rows dummy ⟨input, hin⟩ hmessage cache]
  rfl

theorem cachedForcedRun_world_hash_support (input : HashInput) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) (result : HashOutput × CachedState)
    (hr : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (worldProgram parameter labels (.inr input)) (cache, state) result ≠ 0) :
    (∀ other, other ≠ input → result.2.1 other = cache other) ∧ cache ≤ result.2.1 ∧
      QueryCache.enncard result.2.1 ≤ QueryCache.enncard cache + 1 := by
  have haux (current : State Coordinate Digest PUnit)
      (h : cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (liftM (World.query (.inl (.inl (.inr input))))) (cache, current) result ≠ 0) :
      (∀ other, other ≠ input → result.2.1 other = cache other) ∧ cache ≤ result.2.1 ∧
        QueryCache.enncard result.2.1 ≤ QueryCache.enncard cache + 1 := by
    rw [cachedForcedRun_query] at h
    simp only [cachedForcedImpl, StateT.run_mk] at h
    obtain ⟨raw, hraw, heq⟩ := map_nonzero_source' _ _ _ h
    subst result
    exact cachedAuxiliary_hash_support parameter root otsSecret labels inputs hencoding selections rows dummy input cache raw hraw
  rw [worldProgram, hashProgram] at hr
  cases hp : FtsProbeSimulation.decodeProbe? parameter input with
  | none =>
      rw [hp] at hr
      exact haux state hr
  | some probe =>
      rw [hp, cachedForcedRun_query_bind] at hr
      simp only [cachedForcedImpl, StateT.run_mk] at hr
      rw [RetainedObservation.bind_nonzero] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      obtain ⟨hit, _, rfl⟩ := map_nonzero_source' _ _ _ hmiddle
      dsimp only at hr
      split_ifs at hr with hhit
      · rw [cachedForcedRun_pure] at hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
        subst result
        exact ⟨fun _ _ => rfl, le_rfl, le_self_add⟩
      · exact haux _ hr

theorem messageAnswers_eq_of_cache_of_ne (cache after : QueryCache HashSpec) (input : HashInput)
    (hmessage : ¬MessageHashInput parameter input) (hother : ∀ other, other ≠ input → after other = cache other) :
    messageAnswers parameter after = messageAnswers parameter cache := by
  funext payload
  apply hother
  intro heq
  exact hmessage ⟨payload, heq⟩

/-! ### Signing -/

theorem lazyRun_bind {First Result : Type} (auxiliary : QueryImpl Auxiliary ProbComp) (first : OracleComp World First)
    (next : First → OracleComp World Result) (state : State Coordinate Digest PUnit) :
    lazyRun (environment auxiliary) (first >>= next) state =
      (lazyRun (environment auxiliary) first state >>= fun middle => lazyRun (environment auxiliary) (next middle.1) middle.2) :=
  runWith_bind _ first next state

theorem lazyRun_pure {Result : Type} (auxiliary : QueryImpl Auxiliary ProbComp) (value : Result)
    (state : State Coordinate Digest PUnit) :
    lazyRun (environment auxiliary) (pure value) state = pure (value, state) :=
  SecretGuessObservation.runWith_pure _ value state

theorem lazyRun_disclosure_bind {Result : Type} (auxiliary : QueryImpl Auxiliary ProbComp) (coordinate : Coordinate)
    (next : Digest → OracleComp World Result) (state : State Coordinate Digest PUnit) :
    lazyRun (environment auxiliary) (disclosure coordinate >>= next) state =
      (cell (state.allowed coordinate) >>= fun value =>
        lazyRun (environment auxiliary) (next value) (plainAfterDisclosure state coordinate value)) := by
  rw [disclosure, lazyRun, SecretGuessObservation.runWith_query_bind]
  simp only [SecretGuessObservation.lazyImpl, StateT.run_mk, bind_map_left]
  rfl

theorem cachedForcedRun_disclosure_bind {Result : Type} (coordinate : Coordinate)
    (next : Digest → OracleComp World Result) (cache : QueryCache HashSpec) (state : State Coordinate Digest PUnit) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (disclosure coordinate >>= next) (cache, state) =
      (cell (state.allowed coordinate) >>= fun value =>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (next value)
          (cache, plainAfterDisclosure state coordinate value)) := by
  rw [disclosure, cachedForcedRun_query_bind]
  simp only [cachedForcedImpl, StateT.run_mk, bind_map_left]
  rfl

theorem cachedForcedRun_disclosureSequence {Result : Type} {n : Nat} (coordinates : Fin n → Coordinate)
    (next : (Fin n → Digest) → OracleComp World Result) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) (auxiliary : QueryImpl Auxiliary ProbComp) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      ((sequenceFin fun index => disclosure (coordinates index)) >>= next) (cache, state) =
      (lazyRun (environment auxiliary) (sequenceFin fun index => disclosure (coordinates index)) state >>= fun middle =>
        cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (next middle.1) (cache, middle.2)) := by
  induction n generalizing state with
  | zero =>
      simp only [sequenceFin, pure_bind, lazyRun_pure]
  | succ n ih =>
      rw [sequenceFin]
      simp only [bind_assoc, pure_bind]
      rw [cachedForcedRun_disclosure_bind, lazyRun_disclosure_bind, bind_assoc]
      apply congrArg (cell (state.allowed (coordinates 0)) >>= ·)
      funext value
      rw [ih, lazyRun_bind, bind_assoc]
      apply congrArg (_ >>= ·)
      funext middle
      rw [lazyRun_pure, pure_bind]

theorem cachedForcedRun_completeRecord (record : PublicSigningRecord) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) (auxiliary : QueryImpl Auxiliary ProbComp) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (FtsGuessSigning.completeRecord record) (cache, state) =
      (fun result => (result.1, (cache, result.2))) <$> lazyRun (environment auxiliary) (FtsGuessSigning.completeRecord record) state := by
  obtain ⟨⟨plan, view⟩, trace⟩ := record
  cases plan with
  | none =>
      simp only [FtsGuessSigning.completeRecord, cachedForcedRun_pure, lazyRun, SecretGuessObservation.runWith_pure, map_pure]
  | some plan =>
      cases view with
      | none =>
          simp only [FtsGuessSigning.completeRecord, cachedForcedRun_pure, lazyRun, SecretGuessObservation.runWith_pure, map_pure]
      | some view =>
          simp only [FtsGuessSigning.completeRecord]
          rw [cachedForcedRun_disclosureSequence parameter root otsSecret labels inputs hencoding selections rows dummy slot _ _ cache state
            auxiliary, lazyRun_bind, map_bind]
          apply congrArg (_ >>= ·)
          funext middle
          rw [cachedForcedRun_pure, lazyRun_pure, map_pure]

theorem cachedForcedRun_auxiliary_query (input : Auxiliary.Domain) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (liftM (World.query (.inl input))) (cache, state) =
      (fun result => (result.1, (result.2, state))) <$>
        cachedAuxiliary parameter root otsSecret labels inputs hencoding selections rows dummy input cache := by
  rw [cachedForcedRun_query]
  rfl

theorem cachedForcedRun_completeRecord_mixture (record : PublicSigningRecord) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (auxiliary : QueryImpl Auxiliary ProbComp) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (FtsGuessSigning.completeRecord record) (cache, state) =
      (complete state.allowed >>= fun secrets =>
        pure (completePublicSigningRecord (fun index tree leaf => secrets (index, tree, leaf)) record,
          (cache, FtsGuessSigning.completedState (environment auxiliary) secrets record state))) := by
  rw [cachedForcedRun_completeRecord parameter root otsSecret labels inputs hencoding selections rows dummy slot record cache state
    auxiliary, ← SecretGuessObservation.run_erasure (environment auxiliary) _ state ha, map_bind]
  apply congrArg (complete state.allowed >>= ·)
  funext secrets
  rw [FtsGuessSigning.fixedRun_completeRecord, map_pure]

/-- The cached signing law is the actual random-oracle digest loop from the current cache, completed with a secret table drawn from the current candidates, whose selected coordinates are then disclosed. -/
theorem cachedForcedRun_signingProgram (message : Message) (cache : QueryCache HashSpec)
    (state : State Coordinate Digest PUnit) (ha : ∀ coordinate, (state.allowed coordinate).Nonempty)
    (hinputs : hashInputs (publicDigestLoop parameter root message digestAttemptLimit) ⊆ inputs)
    (auxiliary : QueryImpl Auxiliary ProbComp) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (signingProgram message) (cache, state) =
      (complete state.allowed >>= fun secrets =>
        (fun result => (completePublicSigningRecord (fun index tree leaf => secrets (index, tree, leaf)) result.1,
          (result.2, FtsGuessSigning.completedState (environment auxiliary) secrets result.1 state))) <$>
          𝒟[(simulateQ romImpl (Prod.fst <$> ResidualByteFrontend.publicSigningWork parameter root (known otsSecret labels)
            (referenceFamilyWords selections dummy) selections message)).run cache]) := by
  rw [signingProgram, cachedForcedRun_bind, cachedForcedRun_auxiliary_query, bind_map_left, cachedAuxiliary, seedProgram,
    cached_reference_signing_record parameter root otsSecret labels inputs hencoding selections rows dummy message cache hinputs]
  simp only [cachedForcedRun_completeRecord_mixture parameter root otsSecret labels inputs hencoding selections rows dummy slot _ _ state ha
    auxiliary]
  rw [RetainedObservation.bind_comm]
  apply congrArg (complete state.allowed >>= ·)
  funext secrets
  rw [map_eq_bind_pure_comp]
  exact congrArg (_ >>= ·) (funext fun _ => rfl)

end SphincsSecurity.Concrete.FtsGuessHash
