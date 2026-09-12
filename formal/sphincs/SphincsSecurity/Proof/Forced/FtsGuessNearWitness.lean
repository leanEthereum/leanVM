import SphincsSecurity.Proof.Forced.FtsGuessRemaining
import SphincsSecurity.Proof.Forced.SecretGuessHitPayoff

/-! ## FtsGuessForcedBudget -/

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State forcedRun initialState)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

theorem forced_original_completedRun_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q slot : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support)
    (result : Completed × State Coordinate Digest PUnit)
    (hr : forcedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit) result ≠ 0) :
    1212415 + completedWork result.1 ≤ q ∧ result.2.probes ≤ completedWork result.1 :=
  lazy_original_completedRun_budget dummy adversary q hbound parameter otsSecret labels auxiliary hauxiliary result
    (SecretGuessObservation.forcedRun_nonzero _ slot _ _ result hr)

end SphincsSecurity.Concrete.FtsGuessHash

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State fixedRun lazyRun initialState)
open RetainedResidual (signingInput)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval honestNode canonicalGraphLabels

def completedNearGuess (key : SecretKey) (f : QueryImpl HashSpec Id) (result : Completed) : Prop :=
  SigningTranscript.Valid result.1.1.1.2 ∧ ReferenceFtsCoverage.NearGuess key f result.1.1.1.2 result.1.1.2
    (result.1.2 * result.2.2) result.1.1.1.1

noncomputable def completedNearCertificate (parameter : PublicParameter) (root : Digest) (result : Completed) : Prop :=
  let key : SecretKey := ⟨parameter, root, fun _ _ _ _ => 0, fun _ _ _ => 0⟩
  SigningTranscript.Valid result.1.1.1.2 ∧ ∃ omitted : FtsTree,
    TargetCertificateAt key (Finset.univ.erase omitted)
      (hashRowsCache (result.1.1.2 * result.2.1.2).messageCalls, result.1.1.1.2)
      (signingInput key result.1.1.1.1.message result.1.1.1.1.signature)

theorem completedNearCertificate_iff (key : SecretKey) (result : Completed) :
    completedNearCertificate key.parameter key.root result ↔
      SigningTranscript.Valid result.1.1.1.2 ∧ ∃ omitted : FtsTree,
        TargetCertificateAt key (Finset.univ.erase omitted)
          (hashRowsCache (result.1.1.2 * result.2.1.2).messageCalls, result.1.1.1.2)
          (signingInput key result.1.1.1.1.message result.1.1.1.1.signature) := Iff.rfl

theorem reference_completed_nearCertificate (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (hroot : root = (ReferenceVerifierWitness.rootedKey key f).root)
    (dummy : OtsReferenceWords) (adversary : Adversary) (before : AdversaryTrace)
    (hb : before ∈ support (referenceForgeryRest key f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (referenceTableSelection key f) dummy adversary))
    (hevent : completedNearGuess { key with root := root } f (completedAtRoot key.parameter root f before)) :
    completedNearCertificate key.parameter root (completedAtRoot key.parameter root f before) := by
  rw [completedNearCertificate_iff { key with root := root }]
  obtain ⟨hvalid, omitted, hcertificate, _⟩ := hevent
  refine ⟨hvalid, omitted, ?_⟩
  have h := referenceForgeryRest_certificate_atRoot key f root hroot dummy adversary before hb _ _ hcertificate
  simpa only [completeCertificateRest, completedAtRoot] using h

private theorem map_nonzero {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

private theorem supported_probComp {Result : Type} (law : ProbComp Result) (result : Result) (hr : 𝒟[law] result ≠ 0) :
    result ∈ support law := by
  simpa only [mem_support_iff, probOutput_def] using hr

theorem fixed_reference_completed_nearCertificate (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : Completed)
    (hr : 𝒟[simulateQ
      (fixedAnswers (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy)
        (FtsGuessSigning.secretTable key.ftsSecret)) (completedRun key.parameter (canonicalGraphRoot labels) labels adversary)] result ≠ 0)
    (hevent : completedNearGuess { key with root := canonicalGraphRoot labels }
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result) :
    completedNearCertificate key.parameter (canonicalGraphRoot labels) result := by
  rw [fixed_reference_completedForgeryRest key inputs hencoding labels auxiliary hauxiliary dummy adversary, evalDist_map,
    map_nonzero] at hr
  obtain ⟨before, hb, rfl⟩ := hr
  apply reference_completed_nearCertificate key _ (canonicalGraphRoot labels) _ dummy adversary before _ hevent
  · exact (congrArg SecretKey.root (rootedKey_programmedHash key labels _ dummy)).symm
  · rw [canonicalGraphLabels_programmedHash, referenceTableSelection_auxiliary key inputs hencoding labels auxiliary hauxiliary]
    exact supported_probComp _ before hb

theorem lazy_reference_near_witnesses (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) (result : Completed × State Coordinate Digest PUnit)
    (hr : lazyRun
      (SecretGuessObservation.environment
        (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy))
      (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit) result ≠ 0)
    (hsecrets : complete result.2.allowed (FtsGuessSigning.secretTable key.ftsSecret) ≠ 0)
    (hevent : completedNearGuess { key with root := canonicalGraphRoot labels }
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result.1) :
    result.2.guesses.Nonempty ∧ completedNearCertificate key.parameter (canonicalGraphRoot labels) result.1 := by
  have hfixed := fixedRun_nonzero_of_lazy_posterior _ _ (initialState PUnit.unit) result _ hr hsecrets
  have hprojected := (map_nonzero Prod.fst _ result.1).mpr ⟨result, hfixed, rfl⟩
  rw [SecretGuessObservation.fixedRun_projection] at hprojected
  have htable : FtsGuessSigning.secretTable ({ key with root := canonicalGraphRoot labels } : SecretKey).ftsSecret =
      FtsGuessSigning.secretTable key.ftsSecret := rfl
  have tracking := lazy_reference_completedRun_tracking { key with root := canonicalGraphRoot labels }
    inputs hencoding labels auxiliary hauxiliary dummy adversary (initialState PUnit.unit) result hr
    ((congrArg (fun table => complete result.2.allowed table ≠ 0) htable).mpr hsecrets)
  have hnear := tracking.near_guess rfl _ _ hevent.2
  obtain ⟨omitted, _, hguess⟩ := hnear
  exact ⟨⟨_, hguess⟩, fixed_reference_completed_nearCertificate key inputs hencoding labels auxiliary hauxiliary
    dummy adversary result.1 hprojected hevent⟩

end SphincsSecurity.Concrete.FtsGuessHash
