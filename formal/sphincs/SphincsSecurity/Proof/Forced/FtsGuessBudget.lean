import SphincsSecurity.Proof.Forced.FtsGuessWork
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] instSampleableTypePublicParameter canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval
set_option backward.isDefEq.respectTransparency false

noncomputable def verdict (result : Completed) : Bool × SigningBoundaryTrace :=
  (decide (SigningTranscript.Valid result.1.1.1.2 ∧ ¬SigningTranscript.Contains result.1.1.1.2 result.1.1.1.1) && result.2.1.1,
    (FreeMonoid.of none) ^ 1212415 * (result.1.1.2 * result.2.1.2))

theorem verdict_work (result : Completed) : (verdict result).2.hashCalls = 1212415 + completedWork result := by
  simp only [verdict, SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none, completedWork]

theorem referenceForgeryRest_verdict (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun before => (completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
      (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) before).output) <$>
      referenceForgeryRest key f labels selections dummy adversary =
      referenceFamilyFrontierRest key f labels selections dummy adversary := by
  have h := congrArg (Functor.map Prod.fst) (referenceForgeryRest_trace key f labels selections dummy adversary)
  rw [Functor.map_map, fixedTrace_forget, CausalFrontierProgram.fixed_game,
    ← causalFrontierGame_eq] at h
  exact h

theorem reference_completed_verdict (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    verdict <$> simulateQ
      (fixedAnswers (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy)
        (FtsGuessSigning.secretTable key.ftsSecret))
      (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) =
      referenceFamilyFrontierRest key
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
        labels auxiliary.selections dummy adversary := by
  rw [fixed_reference_completedForgeryRest key inputs hencoding labels auxiliary hauxiliary dummy adversary, Functor.map_map,
    ← referenceForgeryRest_verdict]
  congr 1
  funext before
  simp only [verdict, completedAtRoot, completedReferenceContact, reference_root]

private theorem probComp_nonzero {Result : Type} (computation : ProbComp Result) (result : Result)
    (hr : result ∈ support computation) : 𝒟[computation] result ≠ 0 := by
  simpa only [mem_support_iff, probOutput_def] using hr

theorem referenceResidualGame_auxiliary_support (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (parameter : PublicParameter) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (auxiliary : ReferenceAuxiliary inputs)
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) (labels : CanonicalGraphLabels)
    (result : Bool × SigningBoundaryTrace)
    (hr : 𝒟[referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret⟩
      (programmedHash parameter otsSecret ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs (hencoding parameter) labels auxiliary.rows auxiliary.seed)))
      labels auxiliary.selections dummy adversary] result ≠ 0) :
    (auxiliary.selections, result) ∈ support (referenceResidualGame inputs hencoding dummy adversary) := by
  rw [mem_support_iff]
  change referenceResidualGame inputs hencoding dummy adversary (auxiliary.selections, result) ≠ 0
  rw [referenceResidualGame_eq_auxiliary]
  simp only [RetainedObservation.bind_nonzero]
  refine ⟨parameter, probComp_nonzero sampleParameter parameter ?_, otsSecret, probComp_nonzero sampleOtsSecrets otsSecret ?_,
    ftsSecret, probComp_nonzero sampleFtsSecrets ftsSecret ?_, auxiliary, ?_, labels, ?_, result, hr, ?_⟩
  · unfold sampleParameter
    exact @mem_support_uniformSample PublicParameter instSampleableTypePublicParameter parameter
  · simp only [sampleOtsSecrets, support_uniformSample, Set.mem_univ]
  · simp only [sampleFtsSecrets, support_uniformSample, Set.mem_univ]
  · simpa only [SPMF.liftM_apply] using (PMF.mem_support_iff _ _).mp hauxiliary
  · simpa only [SPMF.liftM_apply] using (PMF.mem_support_iff _ _).mp (PMF.mem_support_uniformOfFintype labels)
  · simp

noncomputable def originalAnswers (dummy : OtsReferenceWords) (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary)) : QueryImpl Auxiliary ProbComp :=
  referenceAnswers parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) auxiliary dummy

theorem original_completedWork_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : Completed)
    (hr : 𝒟[simulateQ (fixedAnswers (originalAnswers dummy adversary parameter otsSecret labels auxiliary)
      (FtsGuessSigning.secretTable ftsSecret)) (completedRun parameter (canonicalGraphRoot labels) labels adversary)] result ≠ 0) :
    1212415 + completedWork result ≤ q := by
  have hv : 𝒟[referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret⟩
      (programmedHash parameter otsSecret ftsSecret labels
        (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
          (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
            (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary.rows auxiliary.seed)))
      labels auxiliary.selections dummy adversary] (verdict result) ≠ 0 := by
    rw [← reference_completed_verdict ⟨parameter, 0, otsSecret, ftsSecret⟩ (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary hauxiliary dummy adversary, evalDist_map]
    rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  have hs := referenceResidualGame_auxiliary_support (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary parameter otsSecret ftsSecret auxiliary hauxiliary labels _ hv
  simpa only [verdict_work] using referenceResidualGame_hashCalls_le dummy adversary q hbound (auxiliary.selections, verdict result) hs

theorem fixed_original_completedRun_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (secrets : Coordinate → Digest)
    (labels : CanonicalGraphLabels) (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (state : State Coordinate Digest PUnit) (result : Completed × State Coordinate Digest PUnit)
    (hr : fixedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) secrets
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) state result ≠ 0) :
    1212415 + completedWork result.1 ≤ q ∧ result.2.probes ≤ state.probes + completedWork result.1 := by
  classical
  have hp : 𝒟[simulateQ (fixedAnswers (originalAnswers dummy adversary parameter otsSecret labels auxiliary) secrets)
      (completedRun parameter (canonicalGraphRoot labels) labels adversary)] result.1 ≠ 0 := by
    rw [← SecretGuessObservation.fixedRun_projection _ secrets _ state,
      map_eq_bind_pure_comp, RetainedObservation.bind_nonzero]
    exact ⟨result, hr, by simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]⟩
  have hw := original_completedWork_le dummy adversary q hbound parameter otsSecret (FtsGuessSigning.secretTable.symm secrets)
    labels auxiliary hauxiliary result.1 hp
  have hc := fixed_completedRun_probes
    (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) secrets
    parameter (canonicalGraphRoot labels) labels adversary state result hr
  exact ⟨hw, hc⟩

theorem lazy_original_completedRun_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : SecretGuessObservation.lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (SecretGuessObservation.initialState PUnit.unit) result ≠ 0) :
    1212415 + completedWork result.1 ≤ q ∧ result.2.probes ≤ completedWork result.1 := by
  rw [← SecretGuessObservation.run_erasure _ _ _ (fun _ => Finset.univ_nonempty), RetainedObservation.bind_nonzero] at hr
  obtain ⟨secrets, _, hr⟩ := hr
  have h := fixed_original_completedRun_budget dummy adversary q hbound parameter otsSecret secrets labels auxiliary hauxiliary
    (SecretGuessObservation.initialState PUnit.unit) result hr
  simpa only [SecretGuessObservation.initialState, Nat.zero_add] using h

theorem lazy_original_completedRun_probes (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : SecretGuessObservation.lazyRun
      (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary))
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (SecretGuessObservation.initialState PUnit.unit) result ≠ 0) :
    1212415 + result.2.probes ≤ q := by
  obtain ⟨hw, hp⟩ := lazy_original_completedRun_budget dummy adversary q hbound parameter otsSecret labels auxiliary hauxiliary result hr
  omega

end SphincsSecurity.Concrete.FtsGuessHash
