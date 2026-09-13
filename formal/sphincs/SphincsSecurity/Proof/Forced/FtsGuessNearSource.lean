import SphincsSecurity.Proof.Forced.FtsGuessNearEvent
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (forcedRun initialState)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

noncomputable def sourceNearWitness (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (before : AdversaryTrace) : Prop :=
  let result := completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
    (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) before
  SigningTranscript.Valid before.1.1.2 ∧ ReferenceFtsCoverage.NearGuess (ReferenceVerifierWitness.rootedKey key f) f
    before.1.1.2 before.1.2 (result.before * result.after) before.1.1.1

noncomputable def referenceNearWitnessRest (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Bool :=
  (fun before => decide (sourceNearWitness key f labels selections dummy before)) <$>
    referenceForgeryRest key f labels selections dummy adversary

theorem referenceNearWitnessRest_program (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))
    referenceNearWitnessRest key f labels auxiliary.selections dummy adversary =
      (fun result => decide (completedNearGuess { key with root := canonicalGraphRoot labels } f result)) <$>
        simulateQ (fixedAnswers (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy)
          (FtsGuessSigning.secretTable key.ftsSecret)) (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) := by
  dsimp only
  rw [fixed_reference_completedForgeryRest key inputs hencoding labels auxiliary hauxiliary dummy adversary,
    referenceNearWitnessRest, Functor.map_map]
  congr 1
  funext before
  rw [sourceNearWitness, rootedKey_programmedHash key labels _ dummy]
  simp only [completedReferenceContact, reference_root, completedNearGuess, completedAtRoot]
  exact decide_eq_decide.mpr Iff.rfl

theorem referenceNearWitnessRest_initial_bound (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun hit => hit = true | 𝒟[sampleFtsSecrets] >>= fun ftsSecret =>
      𝒟[referenceNearWitnessRest ⟨parameter, 0, otsSecret, ftsSecret⟩
        (programmedHash parameter otsSecret ftsSecret labels
          (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
            (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
              (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary.rows auxiliary.seed)))
        labels auxiliary.selections dummy adversary]] ≤
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  have h := (initial_reference_near_witnesses parameter otsSecret (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary hauxiliary dummy adversary).trans
    (lazy_original_near_event_le dummy adversary budget hbudget parameter otsSecret labels auxiliary hauxiliary)
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) => law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒟[simulateQ
        (fixedAnswers (originalAnswers dummy adversary parameter otsSecret labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels adversary)]) FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  simp only [originalAnswers] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) := referenceNearWitnessRest_program
    ⟨parameter, 0, otsSecret, ftsSecret⟩ (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary hauxiliary dummy adversary
  simp only [hprogram, evalDist_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

noncomputable def forcedNearGame (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) : SPMF Bool := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let auxiliary ← 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]
  let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
  (fun result => decide (completedNearCertificate parameter (canonicalGraphRoot labels) result.1)) <$>
    forcedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)

theorem forcedNearGame_probability (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat) :
    Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] =
      ∑' parameter, Pr[= parameter | 𝒟[sampleParameter]] *
        ∑' otsSecret, Pr[= otsSecret | 𝒟[sampleOtsSecrets]] *
          ∑' auxiliary, Pr[= auxiliary | 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]] *
            ∑' labels, Pr[= labels | 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]] *
              forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  simp only [forcedNearGame, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def, decide_eq_true_eq, forcedNearProbability]

private theorem weighted_sum {Index First : Type} (indices : Finset Index) (law : SPMF First)
    (value : Index → First → ENNReal) (rate : ENNReal) :
    rate * (∑ index ∈ indices, ∑' first, Pr[= first | law] * value index first) =
      ∑' first, Pr[= first | law] * (rate * ∑ index ∈ indices, value index first) := by
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro first
  rw [← Finset.mul_sum]
  ring

private theorem pmf_support_nonzero {Result : Type} (law : PMF Result) (result : Result) (hr : 𝒟[law] result ≠ 0) :
    result ∈ law.support := by
  simpa only [PMF.mem_support_iff, SPMF.liftM_apply] using hr

theorem referenceForgeryGame_near_guess_le_forced (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) :
    Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, Pr[fun hit => hit = true | forcedNearGame dummy adversary slot] := by
  have hsource := referenceForgeryGame_bind_auxiliary (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
    (fun key f labels selections before => pure (decide (sourceNearWitness key f labels selections dummy before)))
  simp only [evalDist_pure, bind_pure_comp] at hsource
  have hprojected := congrArg (fun law : SPMF Bool => Pr[fun hit => hit = true | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[ReferenceForgerySample.nearGuess dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _ at hprojected
  rw [hprojected]
  simp_rw [forcedNearGame_probability, weighted_sum]
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro parameter
  apply mul_le_mul' le_rfl
  rw [probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro otsSecret
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs adversary)],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro auxiliary
  by_cases hz : 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs adversary)] auxiliary = 0
  · simp only [SPMF.probOutput_eq_apply, hz, zero_mul, le_refl]
  apply mul_le_mul' le_rfl
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[PMF.uniformOfFintype CanonicalGraphLabels],
    probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro labels
  apply mul_le_mul' le_rfl
  have h := referenceNearWitnessRest_initial_bound dummy adversary budget hbudget parameter otsSecret labels auxiliary
    (pmf_support_nonzero _ auxiliary hz)
  simpa only [referenceNearWitnessRest, evalDist_map] using h

end SphincsSecurity.Concrete.FtsGuessHash

namespace SphincsSecurity.Concrete

open _root_.OracleComp ENNReal

theorem forgeAdvantage_le_forcedNear_small_budget (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, TargetSum.Valid (dummy lay tree leaf))
    (adversary : Adversary) (q : Nat) (hbound : HasHashQueryBound scheme adversary q)
    (hsmall : q ≤ 3 * 2 ^ 114) :
    forgeAdvantage scheme adversary ≤
      (7 / 4 : ENNReal) * ((q : ENNReal) / 2 ^ 128) + (q : ENNReal) * (11 / 2 ^ 144 : ENNReal) +
      (2 ^ 700 : ENNReal)⁻¹ + ((q : ENNReal) / 2 ^ 128) ^ 2 / (2 * (1 - (q : ENNReal) / 2 ^ 128) ^ 2) +
      ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range q, Pr[fun hit => hit = true | FtsGuessHash.forcedNearGame dummy adversary slot] :=
  (forgeAdvantage_le_nearGuess_normalized_small_budget dummy hdummy adversary q hbound hsmall).trans
    (add_le_add le_rfl (FtsGuessHash.referenceForgeryGame_near_guess_le_forced dummy adversary q hbound))

end SphincsSecurity.Concrete
