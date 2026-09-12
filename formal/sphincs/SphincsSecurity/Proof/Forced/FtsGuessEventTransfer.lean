import SphincsSecurity.Proof.Forced.FtsGuessPairBound
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State fixedRun lazyRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval referenceAnswers completedRun complete

private theorem support_nonzero {Result : Type} (law : SPMF Result) (result : Result) (hr : result ∈ support law) :
    law result ≠ 0 := by
  simpa only [mem_support_iff, SPMF.probOutput_eq_apply] using hr

theorem initialRun_posterior {Result : Type} (auxiliary : QueryImpl Auxiliary ProbComp)
    (computation : OracleComp World Result) :
    (complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
      (fun value => (secrets, value)) <$> 𝒟[simulateQ (fixedAnswers auxiliary secrets) computation]) =
      (lazyRun (SecretGuessObservation.environment auxiliary) computation (initialState PUnit.unit) >>= fun result =>
        (fun secrets => (secrets, result.1)) <$> complete result.2.allowed) := by
  have h := congrArg (Functor.map (fun result : (Coordinate → Digest) × Result × State Coordinate Digest PUnit =>
    (result.1, result.2.1)))
    (SecretGuessObservation.run_posterior (SecretGuessObservation.environment auxiliary) computation (initialState PUnit.unit))
  simp only [map_bind, Functor.map_map] at h
  rw [← h]
  apply congrArg (complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= ·)
  funext secrets
  rw [← SecretGuessObservation.fixedRun_projection auxiliary secrets computation (initialState PUnit.unit), Functor.map_map]

theorem initialEvent_le {Result : Type} (auxiliary : QueryImpl Auxiliary ProbComp)
    (computation : OracleComp World Result) (event : (Coordinate → Digest) → Result → Prop)
    (good : Result × State Coordinate Digest PUnit → Prop)
    (hevent : ∀ result,
      lazyRun (SecretGuessObservation.environment auxiliary) computation (initialState PUnit.unit) result ≠ 0 →
      ∀ secrets, complete result.2.allowed secrets ≠ 0 → event secrets result.1 → good result) :
    Pr[fun result => event result.1 result.2 |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒟[simulateQ (fixedAnswers auxiliary secrets) computation]] ≤
      Pr[good | lazyRun (SecretGuessObservation.environment auxiliary) computation (initialState PUnit.unit)] := by
  rw [initialRun_posterior]
  apply probEvent_bind_le_probEvent
  intro result hr hgood
  rw [probEvent_map, probEvent_eq_zero_iff]
  intro secrets hs he
  exact hgood (hevent result
    (support_nonzero (lazyRun (SecretGuessObservation.environment auxiliary) computation (initialState PUnit.unit)) result hr)
    secrets (support_nonzero (complete result.2.allowed) secrets hs) he)

def completedTwoGuesses (key : SecretKey) (f : QueryImpl HashSpec Id) (result : Completed) : Prop :=
  ReferenceFtsCoverage.TwoGuesses key f result.1.1.1.2 (result.1.2 * result.2.2) result.1.1.1.1

theorem lazy_reference_two_guesses (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : Completed × State Coordinate Digest PUnit)
    (hr : lazyRun
      (SecretGuessObservation.environment (referenceAnswers key.parameter key.root key.otsSecret labels inputs hencoding auxiliary dummy))
      (completedRun key.parameter key.root labels adversary) (initialState PUnit.unit) result ≠ 0)
    (hsecrets : complete result.2.allowed (FtsGuessSigning.secretTable key.ftsSecret) ≠ 0)
    (hevent : completedTwoGuesses key (programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result.1) :
    2 ≤ result.2.guesses.card := by
  have tracking := lazy_reference_completedRun_tracking key inputs hencoding labels auxiliary hauxiliary dummy adversary
    (initialState PUnit.unit) result hr hsecrets
  exact tracking.two_guesses rfl _ hevent

theorem initial_reference_two_witnesses (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => completedTwoGuesses ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm result.1⟩
      (programmedHash parameter otsSecret (FtsGuessSigning.secretTable.symm result.1) labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result.2 |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒟[simulateQ
          (fixedAnswers (referenceAnswers parameter root otsSecret labels inputs hencoding auxiliary dummy) secrets)
          (completedRun parameter root labels adversary)]] ≤
      Pr[fun result => 2 ≤ result.2.guesses.card | lazyRun
        (SecretGuessObservation.environment (referenceAnswers parameter root otsSecret labels inputs hencoding auxiliary dummy))
        (completedRun parameter root labels adversary) (initialState PUnit.unit)] := by
  apply initialEvent_le _ _ (fun secrets result => completedTwoGuesses
    ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
    (programmedHash parameter otsSecret (FtsGuessSigning.secretTable.symm secrets) labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result)
    (fun result => 2 ≤ result.2.guesses.card)
  intro result hr secrets hs hevent
  refine lazy_reference_two_guesses ⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
    inputs hencoding labels auxiliary hauxiliary dummy adversary result ?_ ?_ ?_
  · exact hr
  · have htable : FtsGuessSigning.secretTable
        (⟨parameter, root, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ : SecretKey).ftsSecret = secrets :=
      Equiv.apply_symm_apply FtsGuessSigning.secretTable secrets
    exact (congrArg (fun table => complete result.2.allowed table ≠ 0) htable).mpr hs
  · exact hevent

theorem initial_original_two_witnesses (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let residual := finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed)
    Pr[fun result => completedTwoGuesses
      ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm result.1⟩
      (programmedHash parameter otsSecret (FtsGuessSigning.secretTable.symm result.1) labels residual) result.2 |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒟[simulateQ
          (fixedAnswers (originalAnswers dummy adversary parameter otsSecret labels auxiliary) secrets)
          (completedRun parameter (canonicalGraphRoot labels) labels adversary)]] ≤ pairRate budget := by
  exact (initial_reference_two_witnesses parameter (canonicalGraphRoot labels) otsSecret
    (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary parameter)
    labels auxiliary hauxiliary dummy adversary).trans
    (lazy_original_two_guesses dummy adversary budget hbudget parameter otsSecret labels auxiliary hauxiliary)

end SphincsSecurity.Concrete.FtsGuessHash
