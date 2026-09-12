import SphincsSecurity.Proof.Forced.FtsGuessProgram
namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec OtsContactTrace CanonicalProbeRouting
open FtsGuessSigning (Coordinate)
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

def known (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels) : Labels :=
  CanonicalCoordinate.value otsSecret (fun _ _ _ => 0) labels

theorem known_agrees (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) :
    PublicAgreement words (fun _ _ _ => False) (known otsSecret labels) (CanonicalCoordinate.value otsSecret ftsSecret labels) := by
  intro coordinate hpublic
  cases coordinate with
  | otsStart => rfl
  | graph => rfl
  | ftsStart => exact (hpublic (by change ¬False; exact not_false)).elim

noncomputable def referenceAnswers (parameter : PublicParameter) (root : Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
    (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (auxiliary : ReferenceAuxiliary inputs) (dummy : OtsReferenceWords) : QueryImpl Auxiliary ProbComp :=
  auxiliaryAnswers parameter otsSecret labels
    (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs hencoding labels auxiliary.rows auxiliary.seed))
    (publicSigningRecord parameter root
      (finiteHashAnswer ∅ inputs (knownReferenceResidual parameter inputs hencoding (known otsSecret labels) auxiliary.rows auxiliary.seed))
      (known otsSecret labels) (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections)

theorem reference_signer (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (message : Message) :
    (Prod.map Prod.fst id) <$> (completePublicSigningRecord key.ftsSecret <$>
      publicSigningRecord key.parameter root
        (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding (known key.otsSecret labels)
          auxiliary.rows auxiliary.seed))
        (known key.otsSecret labels) (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message) =
      frontierSigningRun key.parameter root
        (maskOtsPrefixes key.parameter (referenceFamilyWords auxiliary.selections dummy)
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels
            (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))))
        key.ftsSecret (referenceFamilyWords auxiliary.selections dummy)
        (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords auxiliary.selections dummy)) message := by
  rw [← frontierSigningRun_eq_of_agree key.parameter _ _ _ (maskOtsPrefixes_agrees key.parameter _ _),
    frontierSigningRun, frontierSigningRecord_auxiliary_public key root inputs hencoding labels auxiliary hauxiliary dummy
      (fun _ _ _ => False) (known key.otsSecret labels) (known_agrees key.otsSecret key.ftsSecret labels _) message]

theorem fixed_reference_adversaryRun {Result : Type} (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    simulateQ (fixedAnswers (referenceAnswers key.parameter root key.otsSecret labels inputs hencoding auxiliary dummy)
      (FtsGuessSigning.secretTable key.ftsSecret)) (adversaryRun key.parameter labels computation) =
      fixedTrace
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
        (CausalFrontierProgram.adversaryRun key.parameter root
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels
            (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
          key.ftsSecret (referenceFamilyWords auxiliary.selections dummy)
          (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords auxiliary.selections dummy)) computation) := by
  rw [referenceAnswers, fixed_adversaryRun]
  simp only [reference_signer key root inputs hencoding labels auxiliary hauxiliary dummy]
  exact (native_adversaryRun _ _ _ _ _ _ computation).symm

noncomputable def completedAtRoot (parameter : PublicParameter) (root : Digest) (f : QueryImpl HashSpec Id)
    (before : AdversaryTrace) : AdversaryTrace × (Bool × SigningBoundaryTrace) × Trace :=
  (before, boundaryEval parameter f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature),
    answerTrace f (verify ⟨root, parameter⟩ before.1.1.1.message before.1.1.1.signature))

theorem fixed_reference_completedRun (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    simulateQ (fixedAnswers (referenceAnswers key.parameter root key.otsSecret labels inputs hencoding auxiliary dummy)
      (FtsGuessSigning.secretTable key.ftsSecret)) (completedRun key.parameter root labels adversary) =
      completedAtRoot key.parameter root
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) <$>
        fixedTrace
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels
            (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
          (CausalFrontierProgram.adversaryRun key.parameter root
            (programmedHash key.parameter key.otsSecret key.ftsSecret labels
              (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
            key.ftsSecret (referenceFamilyWords auxiliary.selections dummy)
            (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords auxiliary.selections dummy))
            (adversary.main ⟨root, key.parameter⟩)) := by
  rw [completedRun, simulateQ_bind, fixed_reference_adversaryRun key root inputs hencoding labels auxiliary hauxiliary dummy,
    map_eq_bind_pure_comp]
  apply bind_congr
  intro before
  simp only [simulateQ_bind, referenceAnswers, fixed_verifyProgram, pure_bind, simulateQ_pure, Function.comp_def, completedAtRoot]

theorem reference_root (key : SecretKey) (labels : CanonicalGraphLabels) (residual : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) :
    frontierRoot key.parameter
      (maskOtsPrefixes key.parameter words (programmedHash key.parameter key.otsSecret key.ftsSecret labels residual))
      words (canonicalGraphFrontier key.otsSecret labels words) = canonicalGraphRoot labels := by
  rw [← frontierRoot_eq_of_agree key.parameter words _ _ (maskOtsPrefixes_agrees key.parameter words _)]
  exact frontierRoot_of_graph key _ labels words (canonicalGraphLabels_programmedHash _ _ _ _ _)

theorem fixed_reference_completedForgeryRest (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    simulateQ (fixedAnswers (referenceAnswers key.parameter (canonicalGraphRoot labels) key.otsSecret labels inputs hencoding auxiliary dummy)
      (FtsGuessSigning.secretTable key.ftsSecret)) (completedRun key.parameter (canonicalGraphRoot labels) labels adversary) =
      completedAtRoot key.parameter (canonicalGraphRoot labels)
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) <$>
        referenceForgeryRest key
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels
            (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
          labels auxiliary.selections dummy adversary := by
  rw [referenceForgeryRest, reference_root]
  exact fixed_reference_completedRun key (canonicalGraphRoot labels) inputs hencoding labels auxiliary hauxiliary dummy adversary

end SphincsSecurity.Concrete.FtsGuessHash
