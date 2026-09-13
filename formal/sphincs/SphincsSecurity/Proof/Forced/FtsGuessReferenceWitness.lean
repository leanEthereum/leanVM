import SphincsSecurity.Proof.Forced.FtsGuessWitness
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State fixedRun lazyRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval programmedHash fixedBoundaryRun signWithView publicSigningRecord

private theorem map_nonzero {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

private theorem signing_record_view (key : SecretKey) (f : QueryImpl HashSpec Id) (message : Message)
    (record : (Option Signature × Option FewTimeView) × SigningBoundaryTrace)
    (hr : 𝒟[fixedBoundaryRun key.parameter f (signWithView key message)] record ≠ 0)
    (signature : Signature) (hs : record.1.1 = some signature) :
    record.1.2 = some (RetainedResidual.signingView key f message signature) := by
  have hrecord : 𝒟[fixedBoundaryRun key.parameter f (signWithView key message)]
      ((some signature, record.1.2), record.2) ≠ 0 := by
    simpa only [← hs] using hr
  exact (RetainedResidual.fixedBoundaryRun_signing_origin key f message signature record.1.2 record.2 hrecord).1

theorem fixed_signingProgram_view (auxiliary : QueryImpl Auxiliary ProbComp) (key : SecretKey) (f : QueryImpl HashSpec Id)
    (hsigner : ∀ message, completePublicSigningRecord key.ftsSecret <$> auxiliary (.inr message) =
      fixedBoundaryRun key.parameter f (signWithView key message))
    (message : Message) (state : State Coordinate Digest PUnit)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × State Coordinate Digest PUnit)
    (hr : fixedRun (SecretGuessObservation.environment auxiliary) (FtsGuessSigning.secretTable key.ftsSecret)
      (signingProgram message) state result ≠ 0)
    (signature : Signature) (hs : result.1.1.1 = some signature) :
    result.1.1.2 = some (RetainedResidual.signingView key f message signature) := by
  have hprojected := (map_nonzero Prod.fst _ result.1).mpr ⟨result, hr, rfl⟩
  rw [SecretGuessObservation.fixedRun_projection, fixed_signingProgram] at hprojected
  change 𝒟[completePublicSigningRecord key.ftsSecret <$> auxiliary (.inr message)] result.1 ≠ 0 at hprojected
  rw [hsigner] at hprojected
  exact signing_record_view key f message result.1 hprojected signature hs

theorem fixed_reference_signingProgram_view (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (message : Message) (state : State Coordinate Digest PUnit)
    (result : ((Option Signature × Option FewTimeView) × SigningBoundaryTrace) × State Coordinate Digest PUnit)
    (hr : fixedRun
      (SecretGuessObservation.environment (referenceAnswers key.parameter key.root key.otsSecret labels inputs hencoding auxiliary dummy))
      (FtsGuessSigning.secretTable key.ftsSecret) (signingProgram message) state result ≠ 0)
    (signature : Signature) (hs : result.1.1.1 = some signature) :
    result.1.1.2 = some (RetainedResidual.signingView key
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
      message signature) := by
  apply fixed_signingProgram_view _ key _ _ message state result hr signature hs
  intro message
  change (completePublicSigningRecord key.ftsSecret <$>
    publicSigningRecord key.parameter key.root
      (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding (known key.otsSecret labels) auxiliary.rows auxiliary.seed))
      (known key.otsSecret labels) (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message) = _
  exact (fixedBoundaryRun_signWithView_auxiliary_public key inputs hencoding labels auxiliary hauxiliary dummy
    (fun _ _ _ => False) (known key.otsSecret labels) (known_agrees key.otsSecret key.ftsSecret labels _) message).symm

theorem fixed_reference_completedRun_tracking (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) (state : State Coordinate Digest PUnit)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : fixedRun
      (SecretGuessObservation.environment (referenceAnswers key.parameter key.root key.otsSecret labels inputs hencoding auxiliary dummy))
      (FtsGuessSigning.secretTable key.ftsSecret) (completedRun key.parameter key.root labels adversary) state result ≠ 0) :
    Tracking key
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
      state result.2 result.1.1.1.1.2 (result.1.1.2 * result.1.2.2) := by
  apply fixed_completedRun_tracking _ key _ labels _ adversary state result hr
  exact fixed_reference_signingProgram_view key inputs hencoding labels auxiliary hauxiliary dummy

theorem fixedRun_nonzero_of_lazy_posterior {Memory Result : Type}
    (environment : SecretGuessObservation.Environment Auxiliary Coordinate Digest Memory)
    (computation : OracleComp World Result) (state : State Coordinate Digest Memory)
    (result : Result × State Coordinate Digest Memory) (secrets : Coordinate → Digest)
    (hr : lazyRun environment computation state result ≠ 0)
    (hsecrets : UniformTableCompletion.complete result.2.allowed secrets ≠ 0) :
    fixedRun environment secrets computation state result ≠ 0 := by
  have hjoint : (lazyRun environment computation state >>= fun result =>
      (fun secrets => (secrets, result)) <$> UniformTableCompletion.complete result.2.allowed) (secrets, result) ≠ 0 :=
    (RetainedObservation.bind_nonzero _ _ _).mpr ⟨result, hr, (map_nonzero _ _ _).mpr ⟨secrets, hsecrets, rfl⟩⟩
  rw [← SecretGuessObservation.run_posterior, RetainedObservation.bind_nonzero] at hjoint
  obtain ⟨draw, _, hjoint⟩ := hjoint
  obtain ⟨outcome, houtcome, heq⟩ := (map_nonzero _ _ _).mp hjoint
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
  exact houtcome

theorem lazy_reference_completedRun_tracking (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) (state : State Coordinate Digest PUnit)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : lazyRun
      (SecretGuessObservation.environment (referenceAnswers key.parameter key.root key.otsSecret labels inputs hencoding auxiliary dummy))
      (completedRun key.parameter key.root labels adversary) state result ≠ 0)
    (hsecrets : UniformTableCompletion.complete result.2.allowed (FtsGuessSigning.secretTable key.ftsSecret) ≠ 0) :
    Tracking key
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
      state result.2 result.1.1.1.1.2 (result.1.1.2 * result.1.2.2) :=
  fixed_reference_completedRun_tracking key inputs hencoding labels auxiliary hauxiliary dummy adversary state result
    (fixedRun_nonzero_of_lazy_posterior _ _ state result _ hr hsecrets)

end SphincsSecurity.Concrete.FtsGuessHash
