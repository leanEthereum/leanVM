import SphincsSecurity.Proof.Forced.FtsGuessEventTransfer
import SphincsSecurity.Proof.Reference.ReferenceForgeryAuxiliary
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace UniformTableCompletion
open FtsGuessSigning (Coordinate)
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

noncomputable def sourceTwoWitnesses (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (before : AdversaryTrace) : Prop :=
  let result := completedReferenceContact key.parameter f (referenceFamilyWords selections dummy)
    (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords selections dummy)) before
  ReferenceFtsCoverage.TwoGuesses (ReferenceVerifierWitness.rootedKey key f) f before.1.1.2
    (result.before * result.after) before.1.1.1

noncomputable def referenceTwoGuesses {inputs : Finset HashInput} (dummy : OtsReferenceWords)
    (sample : ReferenceForgerySample inputs) : Prop :=
  let f := finiteHashAnswer ∅ inputs sample.2.1.2
  sourceTwoWitnesses sample.1 f (canonicalGraphLabels sample.1.parameter sample.1.otsSecret sample.1.ftsSecret f)
    sample.2.1.1 dummy sample.2.2

noncomputable def referenceTwoWitnessRest (key : SecretKey) (f : QueryImpl HashSpec Id) (labels : CanonicalGraphLabels)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) : ProbComp Bool :=
  (fun before => decide (sourceTwoWitnesses key f labels selections dummy before)) <$>
    referenceForgeryRest key f labels selections dummy adversary

theorem rootedKey_programmedHash (key : SecretKey) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) :
    ReferenceVerifierWitness.rootedKey key (programmedHash key.parameter key.otsSecret key.ftsSecret labels residual) =
      { key with root := canonicalGraphRoot labels } := by
  have hroot := ReferenceVerifierWitness.source_root key
    (programmedHash key.parameter key.otsSecret key.ftsSecret labels residual) words
  rw [canonicalGraphLabels_programmedHash, reference_root] at hroot
  change { key with root := (ReferenceVerifierWitness.rootedKey key
    (programmedHash key.parameter key.otsSecret key.ftsSecret labels residual)).root } = _
  rw [← hroot]

theorem referenceTwoWitnessRest_program (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))
    referenceTwoWitnessRest key f labels auxiliary.selections dummy adversary =
      (fun result => decide (completedTwoGuesses { key with root := canonicalGraphRoot labels } f result)) <$>
        simulateQ (fixedAnswers (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy)
          (FtsGuessSigning.secretTable key.ftsSecret)) (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) := by
  dsimp only
  rw [fixed_reference_completedForgeryRest key inputs hencoding labels auxiliary hauxiliary dummy adversary,
    referenceTwoWitnessRest, Functor.map_map]
  congr 1
  funext before
  rw [sourceTwoWitnesses, rootedKey_programmedHash key labels _ dummy]
  simp only [completedReferenceContact, reference_root, completedTwoGuesses, completedAtRoot]

theorem referenceTwoWitnessRest_initial_bound (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun hit => hit = true | 𝒟[sampleFtsSecrets] >>= fun ftsSecret =>
      𝒟[referenceTwoWitnessRest ⟨parameter, 0, otsSecret, ftsSecret⟩
        (programmedHash parameter otsSecret ftsSecret labels
          (finiteHashAnswer ∅ (canonicalGraphGameInputs adversary)
            (canonicalReferenceResidual parameter (canonicalGraphGameInputs adversary)
              (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary.rows auxiliary.seed)))
        labels auxiliary.selections dummy adversary]] ≤ pairRate budget := by
  have h := initial_original_two_witnesses dummy adversary budget hbudget parameter otsSecret labels auxiliary hauxiliary
  dsimp only at h
  have hprior := congrArg (fun law : SPMF (Coordinate → Digest) => law >>= fun secrets =>
      (fun result => (secrets, result)) <$> 𝒟[simulateQ
        (fixedAnswers (originalAnswers dummy adversary parameter otsSecret labels auxiliary) secrets)
        (completedRun parameter (canonicalGraphRoot labels) labels adversary)]) FtsGuessSigning.sampleFtsSecrets_table
  rw [bind_map_left] at hprior
  rw [← hprior] at h
  have hprogram (ftsSecret : Index → FtsTree → FtsLeaf → Digest) := referenceTwoWitnessRest_program
    ⟨parameter, 0, otsSecret, ftsSecret⟩ (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary parameter) labels auxiliary hauxiliary dummy adversary
  simp only [hprogram, evalDist_map, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Equiv.symm_apply_apply, decide_eq_true_eq] at h ⊢
  exact h

private theorem pmf_support {Result : Type} (law : PMF Result) (result : Result) (hr : result ∈ support 𝒟[law]) :
    result ∈ law.support := by
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply, SPMF.liftM_apply, PMF.mem_support_iff] using hr

theorem referenceForgeryGame_two_guesses (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) :
    Pr[referenceTwoGuesses dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤ pairRate budget := by
  have hsource := referenceForgeryGame_bind_auxiliary (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
    (fun key f labels selections before => pure (decide (sourceTwoWitnesses key f labels selections dummy before)))
  simp only [evalDist_pure, bind_pure_comp] at hsource
  have hprojected := congrArg (fun law : SPMF Bool => Pr[fun hit => hit = true | law]) hsource
  simp only [probEvent_map, Function.comp_def, decide_eq_true_eq] at hprojected
  change Pr[referenceTwoGuesses dummy | referenceForgeryGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] = _ at hprojected
  rw [hprojected]
  apply probEvent_bind_le_of_forall_le
  intro parameter _
  apply probEvent_bind_le_of_forall_le
  intro otsSecret _
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[referenceAuxiliarySample (canonicalGraphGameInputs adversary)]]
  apply probEvent_bind_le_of_forall_le
  intro auxiliary hauxiliary
  rw [RetainedObservation.bind_comm 𝒟[sampleFtsSecrets] 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]]
  apply probEvent_bind_le_of_forall_le
  intro labels _
  have h := referenceTwoWitnessRest_initial_bound dummy adversary budget hbudget parameter otsSecret labels auxiliary
    (pmf_support _ auxiliary hauxiliary)
  simpa only [referenceTwoWitnessRest, evalDist_map] using h

end SphincsSecurity.Concrete.FtsGuessHash
