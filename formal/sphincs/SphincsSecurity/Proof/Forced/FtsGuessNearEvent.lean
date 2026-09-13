import SphincsSecurity.Proof.Forced.FtsGuessNearWitness
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal UniformTableCompletion
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State lazyRun forcedRun initialState)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

noncomputable def forcedNearProbability (dummy : OtsReferenceWords) (adversary : Adversary) (slot : Nat)
    (parameter : PublicParameter) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (labels : CanonicalGraphLabels) (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary)) : ENNReal :=
  Pr[fun result => completedNearCertificate parameter (canonicalGraphRoot labels) result.1 |
    forcedRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary)) slot
      (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)]

theorem lazy_original_near_event_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : HasHashQueryBound scheme adversary budget) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary (canonicalGraphGameInputs adversary))
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample (canonicalGraphGameInputs adversary)).support) :
    Pr[fun result => result.2.guesses.Nonempty ∧ completedNearCertificate parameter (canonicalGraphRoot labels) result.1 |
      lazyRun (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary))
        (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)] ≤
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ *
        ∑ slot ∈ Finset.range budget, forcedNearProbability dummy adversary slot parameter otsSecret labels auxiliary := by
  have h := SecretGuessObservation.lazyRun_event_le_forced
    (SecretGuessObservation.environment (originalAnswers dummy adversary parameter otsSecret labels auxiliary))
    (completedRun parameter (canonicalGraphRoot labels) labels adversary) PUnit.unit budget
    (fun result hr => (Nat.le_add_left _ _).trans
      (lazy_original_completedRun_probes dummy adversary budget hbudget parameter otsSecret labels auxiliary hauxiliary result hr))
    (fun result => result.2.guesses.Nonempty ∧ completedNearCertificate parameter (canonicalGraphRoot labels) result.1)
    (fun result => if completedNearCertificate parameter (canonicalGraphRoot labels) result.1 then 1 else 0)
    (fun _ _ he => ⟨he.1, by rw [if_pos he.2]⟩)
  simpa only [forcedNearProbability, probEvent_eq_tsum_ite, mul_ite, mul_one, mul_zero,
    show Fintype.card Digest = 2 ^ 128 by simp [digestBits]] using h

theorem initial_reference_near_witnesses (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Pr[fun result => completedNearGuess ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm result.1⟩
      (programmedHash parameter otsSecret (FtsGuessSigning.secretTable.symm result.1) labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result.2 |
      complete (fun _ : Coordinate => (Finset.univ : Finset Digest)) >>= fun secrets =>
        (fun value => (secrets, value)) <$> 𝒟[simulateQ
          (fixedAnswers (referenceAnswers parameter (canonicalGraphRoot labels) otsSecret labels inputs hencoding auxiliary dummy) secrets)
          (completedRun parameter (canonicalGraphRoot labels) labels adversary)]] ≤
      Pr[fun result => result.2.guesses.Nonempty ∧ completedNearCertificate parameter (canonicalGraphRoot labels) result.1 |
        lazyRun (SecretGuessObservation.environment
          (referenceAnswers parameter (canonicalGraphRoot labels) otsSecret labels inputs hencoding auxiliary dummy))
          (completedRun parameter (canonicalGraphRoot labels) labels adversary) (initialState PUnit.unit)] := by
  apply initialEvent_le _ _ (fun secrets result => completedNearGuess
    ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
    (programmedHash parameter otsSecret (FtsGuessSigning.secretTable.symm secrets) labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) result)
    (fun result => result.2.guesses.Nonempty ∧ completedNearCertificate parameter (canonicalGraphRoot labels) result.1)
  intro result hr secrets hs hevent
  refine lazy_reference_near_witnesses ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩
    inputs hencoding labels auxiliary hauxiliary dummy adversary result hr ?_ hevent
  have htable : FtsGuessSigning.secretTable
      (⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm secrets⟩ : SecretKey).ftsSecret = secrets :=
    Equiv.apply_symm_apply FtsGuessSigning.secretTable secrets
  exact (congrArg (fun table => complete result.2.allowed table ≠ 0) htable).mpr hs

end SphincsSecurity.Concrete.FtsGuessHash
