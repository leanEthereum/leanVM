import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.PublicSigningRecord
import SphincsSecurity.Proof.Reference.ReferenceResidualSeeds
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem referenceAuxiliarySample_select (inputs : Finset HashInput) (auxiliary : ReferenceAuxiliary inputs)
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) (position : EncodingPosition) :
    FirstSuccessTable.select decodeEncodingOutput (fun counter => auxiliary.rows (position, counter)) =
      auxiliary.selections position := by
  rw [referenceAuxiliarySample, PMF.mem_support_bind_iff] at hauxiliary
  obtain ⟨selections, hselections, hauxiliary⟩ := hauxiliary
  rw [PMF.mem_support_bind_iff] at hauxiliary
  obtain ⟨rows, hrows, hauxiliary⟩ := hauxiliary
  rw [PMF.mem_support_map_iff] at hauxiliary
  obtain ⟨seed, _, rfl⟩ := hauxiliary
  have hselected : FirstSuccessFamily.select decodeEncodingOutput encodingAttemptLimit rows = selections := by
    by_contra hne
    have hmass := FirstSuccessFamily.selected_mul_afterSelect decodeEncodingOutput encodingAttemptLimit
      decodeEncodingOutput_invalid_nonempty selections rows
    rw [if_neg hne] at hmass
    exact mul_ne_zero ((PMF.mem_support_iff _ _).mp hselections) ((PMF.mem_support_iff _ _).mp hrows) hmass
  exact congrFun hselected position

theorem referenceTableSelection_auxiliary (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) :
    referenceTableSelection key (programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) =
        auxiliary.selections := by
  funext position
  rw [referenceTableSelection_programmedHash key inputs hencoding]
  simp only [canonicalReferenceResidual, UniformTableSplit.overwrite_embed]
  exact referenceAuxiliarySample_select inputs auxiliary hauxiliary position

theorem referenceAuxiliary_words (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) :
    referenceFamilyWords auxiliary.selections dummy = canonicalReferenceWords key
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))) dummy := by
  rw [← referenceTableSelection_auxiliary key inputs hencoding labels auxiliary hauxiliary, referenceFamilyWords_selected]

theorem decodePosition_message (parameter : PublicParameter) (payload : HashInput) :
    decodePosition parameter (tweakableHashInput parameter .message payload) = none := by
  apply (decodePosition_none_iff parameter _).mpr
  rintro position ⟨other, heq⟩
  have hdomain := (tweakableHashInput_injective parameter (by trivial) position.domain_inRange heq).1
  cases position <;> simp [Position.domain] at hdomain

theorem frontierSigningRecord_auxiliary_public (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels)) (message : Message) :
    frontierSigningRecord key.parameter root
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
        key.ftsSecret (referenceFamilyWords auxiliary.selections dummy)
        (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords auxiliary.selections dummy)) message =
      completePublicSigningRecord key.ftsSecret <$>
        publicSigningRecord key.parameter root
          (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding known auxiliary.rows auxiliary.seed))
          known (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message := by
  have h := frontierSigningRecord_eq_public key root
    (programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
    (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding known auxiliary.rows auxiliary.seed))
    (referenceFamilyWords auxiliary.selections dummy) disclosed known
    (by simpa only [canonicalGraphLabels_programmedHash] using hagrees) message
    (fun randomness => programmedReferenceResidual_outside key.parameter inputs hencoding _ disclosed known
      key.otsSecret key.ftsSecret labels hagrees auxiliary.rows auxiliary.seed _
      (decodePosition_message key.parameter (messageDigestPayload root message randomness)))
  simpa only [canonicalGraphLabels_programmedHash,
    referenceTableSelection_auxiliary key inputs hencoding labels auxiliary hauxiliary] using h

theorem fixedBoundaryRun_signWithView_auxiliary_public (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels)) (message : Message) :
    fixedBoundaryRun key.parameter
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed)))
        (signWithView key message) =
      completePublicSigningRecord key.ftsSecret <$>
        publicSigningRecord key.parameter key.root
          (finiteHashAnswer ∅ inputs (knownReferenceResidual key.parameter inputs hencoding known auxiliary.rows auxiliary.seed))
          known (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message := by
  rw [fixedBoundaryRun_signWithView_canonical _ _ dummy,
    ← canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret _ _ key.root,
    canonicalGraphLabels_programmedHash, ← referenceAuxiliary_words key inputs hencoding labels auxiliary hauxiliary dummy]
  exact frontierSigningRecord_auxiliary_public key key.root inputs hencoding labels auxiliary hauxiliary dummy disclosed known hagrees message

end SphincsSecurity.Concrete
