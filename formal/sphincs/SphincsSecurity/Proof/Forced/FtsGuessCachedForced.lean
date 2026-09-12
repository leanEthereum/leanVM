import SphincsSecurity.Proof.Forced.FtsGuessCachedMessage
import SphincsSecurity.Proof.Residual.RetainedResidualCoverageStep

/-! ## FtsGuessSigningDigest -/

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec CanonicalProbeRouting ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs publicDigestLoop signDigestLoop

theorem publicSigningWork_complete_digest (key : SecretKey) (known : Labels) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (actual : Labels) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) result.1.1).1, result.2)) <$>
      𝒟[(simulateQ romImpl (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache] =
        RetainedResidual.digestCompletionValue known words selections actual <$>
          𝒟[(simulateQ romImpl (signDigestLoop digestAttemptLimit key message)).run cache] := by
  rw [RetainedResidual.publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, evalDist_map,
    Functor.map_map, publicDigestLoop_eq, simulateQ_boundaryComputation]
  rw [← boundaryRun_forget key.parameter (signDigestLoop digestAttemptLimit key message) cache,
    evalDist_map, Functor.map_map]
  change (fun result => ((completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf))
    (RetainedResidual.digestWork known words selections result.1).1).1, result.2)) <$>
      𝒟[boundaryRun key.parameter (signDigestLoop digestAttemptLimit key message) cache] = _
  congr 1
  funext result
  rcases result with ⟨⟨selected, trace⟩, after⟩
  cases selected <;> rfl

end SphincsSecurity.Concrete.FtsGuessHash

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State initialState forcedRun forcedProgram forcedTrial plainAfterTrial plainAfterDisclosure)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput

abbrev CachedState := QueryCache HashSpec × State Coordinate Digest PUnit

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)

noncomputable def seedProgram (input : Auxiliary.Domain) : OracleComp (ForcedSeedSpec inputs) (Auxiliary.Range input) :=
  simulateQ (seedLift inputs) (referenceProgram parameter root otsSecret labels inputs hencoding selections rows dummy input)

noncomputable def cachedAuxiliary (input : Auxiliary.Domain) (cache : QueryCache HashSpec) :
    SPMF (Auxiliary.Range input × QueryCache HashSpec) :=
  cachedSeedRun inputs (seedProgram parameter root otsSecret labels inputs hencoding selections rows dummy input) cache

noncomputable def cachedForcedImpl : QueryImpl World (StateT CachedState SPMF)
  | .inl input => StateT.mk fun state => (fun result => (result.1, (result.2, state.2))) <$>
      cachedAuxiliary parameter root otsSecret labels inputs hencoding selections rows dummy input state.1
  | .inr (.inl (coordinate, candidate)) => StateT.mk fun state =>
      (fun hit => (hit, (state.1, plainAfterTrial state.2 coordinate candidate hit))) <$>
        forcedTrial slot state.2 coordinate candidate
  | .inr (.inr coordinate) => StateT.mk fun state =>
      (fun value => (value, (state.1, plainAfterDisclosure state.2 coordinate value))) <$> cell (state.2.allowed coordinate)

noncomputable def cachedForcedRun {Result : Type} (computation : OracleComp World Result) (state : CachedState) :
    SPMF (Result × CachedState) :=
  (simulateQ (cachedForcedImpl parameter root otsSecret labels inputs hencoding selections rows dummy slot) computation).run state

theorem cachedForcedRun_pure {Result : Type} (value : Result) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (pure value) state =
      pure (value, state) := by
  simp only [cachedForcedRun, simulateQ_pure, StateT.run_pure]

theorem cachedForcedRun_query_bind {Result : Type} (input : World.Domain)
    (next : World.Range input → OracleComp World Result) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
      (liftM (World.query input) >>= next) state =
      ((cachedForcedImpl parameter root otsSecret labels inputs hencoding selections rows dummy slot input).run state >>=
        fun result => cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
          (next result.1) result.2) := by
  simp only [cachedForcedRun, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem cachedForcedRun_bind {First Result : Type} (first : OracleComp World First)
    (next : First → OracleComp World Result) (state : CachedState) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot (first >>= next) state =
      (cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot first state >>=
        fun middle => cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
          (next middle.1) middle.2) := by
  simp only [cachedForcedRun, simulateQ_bind, StateT.run_bind]

theorem cachedSeedRun_pure {Result : Type} (value : Result) (cache : QueryCache HashSpec) :
    cachedSeedRun inputs (pure value : OracleComp (ForcedSeedSpec inputs) Result) cache = pure (value, cache) := by
  simp only [cachedSeedRun, simulateQ_pure, StateT.run_pure]

theorem cachedSeedRun_bind {First Result : Type} (first : OracleComp (ForcedSeedSpec inputs) First)
    (next : First → OracleComp (ForcedSeedSpec inputs) Result) (cache : QueryCache HashSpec) :
    cachedSeedRun inputs (first >>= next) cache =
      (cachedSeedRun inputs first cache >>= fun middle => cachedSeedRun inputs (next middle.1) middle.2) := by
  simp only [cachedSeedRun, simulateQ_bind, StateT.run_bind]

theorem cachedSeedRun_sampleForcedBool (law : SPMF Bool) (cache : QueryCache HashSpec) :
    cachedSeedRun inputs (sampleForcedBool inputs law) cache = (fun hit => (hit, cache)) <$> law := by
  rw [cachedSeedRun, sampleForcedBool, simulateQ_spec_query]
  rfl

theorem cachedSeedRun_sampleForcedDigest (law : SPMF Digest) (cache : QueryCache HashSpec) :
    cachedSeedRun inputs (sampleForcedDigest inputs law) cache = (fun value => (value, cache)) <$> law := by
  rw [cachedSeedRun, sampleForcedDigest, simulateQ_spec_query]
  rfl

/-- Running the forced interpreter against the actual cached seed table is the seed-program run in `cachedSeedRun`, with the secret-guess state carried alongside the cache. -/
theorem cachedForcedRun_seed {Result : Type} (computation : OracleComp World Result)
    (cache : QueryCache HashSpec) (state : State Coordinate Digest PUnit) :
    cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot computation (cache, state) =
      (fun result => (result.1.1, (result.2, result.1.2))) <$>
        cachedSeedRun inputs (forcedProgram (seedProgram parameter root otsSecret labels inputs hencoding selections rows dummy)
          (sampleForcedBool inputs) (sampleForcedDigest inputs) slot computation state) cache := by
  induction computation using OracleComp.inductionOn generalizing cache state with
  | pure value =>
      rw [cachedForcedRun_pure, SecretGuessObservation.forcedProgram_pure, cachedSeedRun_pure, map_pure]
  | query_bind input next ih =>
      rw [cachedForcedRun_query_bind, SecretGuessObservation.forcedProgram_query_bind]
      cases input with
      | inl input =>
          rw [cachedSeedRun_bind, map_bind]
          simp only [cachedForcedImpl, StateT.run_mk, bind_map_left, cachedAuxiliary]
          apply congrArg (cachedSeedRun inputs (seedProgram parameter root otsSecret labels inputs hencoding selections rows dummy input) cache >>= ·)
          funext answer
          exact ih answer.1 answer.2 state
      | inr input =>
          cases input with
          | inl probe =>
              rcases probe with ⟨coordinate, candidate⟩
              rw [cachedSeedRun_bind, cachedSeedRun_sampleForcedBool, map_bind]
              simp only [cachedForcedImpl, StateT.run_mk, bind_map_left]
              apply congrArg (forcedTrial slot state coordinate candidate >>= ·)
              funext hit
              exact ih hit cache (plainAfterTrial state coordinate candidate hit)
          | inr coordinate =>
              rw [cachedSeedRun_bind, cachedSeedRun_sampleForcedDigest, map_bind]
              simp only [cachedForcedImpl, StateT.run_mk, bind_map_left]
              apply congrArg (cell (state.allowed coordinate) >>= ·)
              funext value
              exact ih value cache (plainAfterDisclosure state coordinate value)

theorem seedAllowed_empty : seedAllowed inputs ∅ = fun _ => Finset.univ := by
  funext input
  simp only [seedAllowed, QueryCache.empty_apply, Option.elim_none]

/-- Starting from the empty cache, forgetting the cache recovers the deferred forced run. -/
theorem cachedForcedRun_deferred (adversary : Adversary) :
    (fun result => (result.1, result.2.2)) <$>
      cachedForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot
        (completedRun parameter root labels adversary) (∅, initialState PUnit.unit) =
      Prod.fst <$> deferredForcedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot adversary := by
  rw [cachedForcedRun_seed, Functor.map_map, deferredForcedRun, ← seedAllowed_empty inputs, ← cachedSeedRun_project,
    Functor.map_map]
  rfl

theorem cachedForcedRun_original_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q slot : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : Completed × CachedState)
    (hr : cachedForcedRun parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) auxiliary.selections auxiliary.rows dummy slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (∅, initialState PUnit.unit) result ≠ 0) :
    1212415 + completedWork result.1 ≤ q ∧ result.2.2.probes ≤ completedWork result.1 := by
  have hp : (Prod.fst <$> deferredForcedRun parameter (canonicalGraphRoot labels) otsSecret labels
      (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary parameter)
      auxiliary.selections auxiliary.rows dummy slot adversary) (result.1, result.2.2) ≠ 0 := by
    rw [← cachedForcedRun_deferred, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hp
  obtain ⟨deferred, hdeferred, heq⟩ := hp
  simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
  have h := deferredForcedRun_original_budget dummy adversary q slot hbound parameter otsSecret labels auxiliary hauxiliary
    deferred hdeferred
  rw [← heq] at h
  exact h

theorem referenceAuxiliary_mem_support (inputs : Finset HashInput) (selections : ReferenceFamily)
    (hselections : selections ∈ (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).support)
    (rows : EncodingPosition → Fin encodingAttemptLimit → HashOutput)
    (hrows : rows ∈ (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit
      decodeEncodingOutput_invalid_nonempty selections).support) (seed : inputs → HashOutput) :
    (⟨selections, Function.uncurry rows, seed⟩ : ReferenceAuxiliary inputs) ∈ (referenceAuxiliarySample inputs).support := by
  rw [referenceAuxiliarySample, PMF.mem_support_bind_iff]
  refine ⟨selections, hselections, ?_⟩
  rw [PMF.mem_support_bind_iff]
  refine ⟨rows, hrows, ?_⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨seed, PMF.mem_support_uniformOfFintype seed, rfl⟩

noncomputable def cachedNearGame (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) : SPMF Bool := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let rows ← 𝒟[FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections]
  let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
  (fun result => decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1)) <$>
    cachedForcedRun parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (∅, initialState PUnit.unit)

theorem forcedNearGame_cached (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) :
    forcedNearGame dummy adversary slot = cachedNearGame dummy adversary slot := by
  rw [forcedNearGame_deferred]
  simp only [forcedNearDeferredGame, cachedNearGame]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  apply congrArg (𝒟[FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit
    decodeEncodingOutput_invalid_nonempty selections] >>= ·)
  funext rows
  apply congrArg (𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= ·)
  funext labels
  have h := congrArg (Functor.map (fun result : Completed × State Coordinate Digest PUnit =>
    decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1)))
    (cachedForcedRun_deferred parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot adversary)
  simp only [Functor.map_map] at h
  exact h.symm

end SphincsSecurity.Concrete.FtsGuessHash
