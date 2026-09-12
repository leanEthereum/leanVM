import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.ReferenceAuxiliarySigning
import SphincsSecurity.Proof.Ots.ReferencePrefixResidual
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem referenceTableSelection_prefix (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) :
    referenceTableSelection key (programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding labels
        auxiliary.selections auxiliary.rows auxiliary.seed))) = auxiliary.selections := by
  funext position
  rw [referenceTableSelection_programmedHash key inputs hencoding]
  apply FirstSuccessPrefix.select_eq_of_kept decodeEncodingOutput
    (fun counter => auxiliary.rows (position, counter)) _ (auxiliary.selections position)
    (referenceAuxiliarySample_select inputs auxiliary hauxiliary position)
  intro counter hkept
  simp only [canonicalPrefixResidual, UnrestrictedRowSwap.prefixOverwrite_embed,
    show FirstSuccessPrefix.familyKept auxiliary.selections (position, counter) from hkept, if_true]

theorem referencePrefix_words (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) :
    referenceFamilyWords auxiliary.selections dummy = canonicalReferenceWords key
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels
        (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding labels
          auxiliary.selections auxiliary.rows auxiliary.seed))) dummy := by
  conv_lhs => rw [← referenceTableSelection_prefix key inputs hencoding labels auxiliary hauxiliary]
  rw [referenceFamilyWords_selected]

theorem programmedPrefixResidual_outside (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels))
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : HashInput)
    (houtside : decodePosition parameter input = none) :
    programmedHash parameter otsSecret ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding labels selections rows seed)) input =
      finiteHashAnswer ∅ inputs (knownPrefixResidual parameter inputs hencoding known selections rows seed) input := by
  rw [canonicalPrefixResidual_eq_known parameter inputs hencoding words disclosed known otsSecret ftsSecret labels hagrees]
  simp only [programmedHash, houtside, Option.elim_none]

theorem frontierSigningRecord_prefix_public (key : SecretKey) (root : Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels)) (message : Message) :
    frontierSigningRecord key.parameter root
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding labels
            auxiliary.selections auxiliary.rows auxiliary.seed)))
        key.ftsSecret (referenceFamilyWords auxiliary.selections dummy)
        (canonicalGraphFrontier key.otsSecret labels (referenceFamilyWords auxiliary.selections dummy)) message =
      completePublicSigningRecord key.ftsSecret <$>
        publicSigningRecord key.parameter root
          (finiteHashAnswer ∅ inputs (knownPrefixResidual key.parameter inputs hencoding known
            auxiliary.selections auxiliary.rows auxiliary.seed))
          known (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message := by
  have h := frontierSigningRecord_eq_public key root
    (programmedHash key.parameter key.otsSecret key.ftsSecret labels
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding labels
        auxiliary.selections auxiliary.rows auxiliary.seed)))
    (finiteHashAnswer ∅ inputs (knownPrefixResidual key.parameter inputs hencoding known
      auxiliary.selections auxiliary.rows auxiliary.seed))
    (referenceFamilyWords auxiliary.selections dummy) disclosed known
    (by simpa only [canonicalGraphLabels_programmedHash] using hagrees) message
    (fun randomness => programmedPrefixResidual_outside key.parameter inputs hencoding _ disclosed known
      key.otsSecret key.ftsSecret labels hagrees auxiliary.selections auxiliary.rows auxiliary.seed _
      (decodePosition_message key.parameter (messageDigestPayload root message randomness)))
  simpa only [canonicalGraphLabels_programmedHash,
    referenceTableSelection_prefix key inputs hencoding labels auxiliary hauxiliary] using h

theorem fixedBoundaryRun_signWithView_prefix_public (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (auxiliary : ReferenceAuxiliary inputs) (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support)
    (dummy : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement (referenceFamilyWords auxiliary.selections dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret labels)) (message : Message) :
    fixedBoundaryRun key.parameter
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalPrefixResidual key.parameter inputs hencoding labels
            auxiliary.selections auxiliary.rows auxiliary.seed))) (signWithView key message) =
      completePublicSigningRecord key.ftsSecret <$>
        publicSigningRecord key.parameter key.root
          (finiteHashAnswer ∅ inputs (knownPrefixResidual key.parameter inputs hencoding known
            auxiliary.selections auxiliary.rows auxiliary.seed))
          known (referenceFamilyWords auxiliary.selections dummy) auxiliary.selections message := by
  rw [fixedBoundaryRun_signWithView_canonical _ _ dummy,
    ← canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret _ _ key.root,
    canonicalGraphLabels_programmedHash, ← referencePrefix_words key inputs hencoding labels auxiliary hauxiliary dummy]
  exact frontierSigningRecord_prefix_public key key.root inputs hencoding labels auxiliary hauxiliary dummy disclosed known hagrees message

end SphincsSecurity.Concrete
