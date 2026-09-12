import SphincsSecurity.Proof.Forced.FtsGuessDeferredSeed
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  publicDigestLoop canonicalGraphRoot canonicalGraphInput

noncomputable def forcedNearDeferredGame (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) : SPMF Bool := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let selections ← 𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let rows ← 𝒟[FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections]
  let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
  (fun result => decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1.1)) <$>
    deferredForcedRun parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot adversary

theorem forcedNearGame_deferred (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) :
    forcedNearGame dummy adversary slot = forcedNearDeferredGame dummy adversary slot := by
  simp only [forcedNearGame, forcedNearDeferredGame, referenceAuxiliarySample, ← PMF.monad_bind_eq_bind,
    ← PMF.monad_map_eq_map, evalDist_bind, evalDist_map, bind_assoc, bind_map_left]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit] >>= ·)
  funext selections
  apply congrArg (𝒟[FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit
    decodeEncodingOutput_invalid_nonempty selections] >>= ·)
  funext rows
  rw [RetainedObservation.bind_comm]
  apply congrArg (𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= ·)
  funext labels
  have h := congrArg (Functor.map (fun result => decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1)))
    (forcedRun_seed_marginal parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) selections (Function.uncurry rows) dummy slot adversary)
  simpa only [map_bind, Functor.map_map, originalAnswers] using h

theorem referenceAuxiliary_seed_support (inputs : Finset HashInput) (auxiliary : ReferenceAuxiliary inputs)
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) (seed : inputs → HashOutput) :
    { auxiliary with seed := seed } ∈ (referenceAuxiliarySample inputs).support := by
  rw [referenceAuxiliarySample, PMF.mem_support_bind_iff] at hauxiliary ⊢
  obtain ⟨selections, hselections, hauxiliary⟩ := hauxiliary
  rw [PMF.mem_support_bind_iff] at hauxiliary
  obtain ⟨rows, hrows, hauxiliary⟩ := hauxiliary
  rw [PMF.mem_support_map_iff] at hauxiliary
  obtain ⟨oldSeed, _, rfl⟩ := hauxiliary
  refine ⟨selections, hselections, ?_⟩
  rw [PMF.mem_support_bind_iff]
  refine ⟨rows, hrows, ?_⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨seed, PMF.mem_support_uniformOfFintype seed, rfl⟩

theorem deferredForcedRun_original_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q slot : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : (Completed × SecretGuessObservation.State FtsGuessSigning.Coordinate Digest PUnit) ×
      (canonicalGraphGameInputs adversary → Finset HashOutput))
    (hr : deferredForcedRun parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) auxiliary.selections auxiliary.rows dummy slot adversary result ≠ 0) :
    1212415 + completedWork result.1.1 ≤ q ∧ result.1.2.probes ≤ completedWork result.1.1 := by
  have hp : (Prod.fst <$> deferredForcedRun parameter (canonicalGraphRoot labels) otsSecret labels
      (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary parameter)
      auxiliary.selections auxiliary.rows dummy slot adversary) result.1 ≠ 0 := by
    rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  rw [← forcedRun_seed_marginal, RetainedObservation.bind_nonzero] at hp
  obtain ⟨seed, _, hs⟩ := hp
  exact forced_original_completedRun_budget dummy adversary q slot hbound parameter otsSecret labels
    { auxiliary with seed := seed } (referenceAuxiliary_seed_support _ auxiliary hauxiliary seed) result.1 hs

end SphincsSecurity.Concrete.FtsGuessHash
