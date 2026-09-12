import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Base.FirstSuccessPrefix
import SphincsSecurity.Proof.Fts.HiddenLabelProbe
import SphincsSecurity.Proof.Ots.OtsProbeCompletionSampling
import SphincsSecurity.Proof.Ots.OtsProbeOrigin
import SphincsSecurity.Proof.Fts.FtsProbeSampling
import SphincsSecurity.Proof.Base.RomQueryChargeBind
import SphincsSecurity.Proof.Residual.PublicReferenceResidual
namespace SphincsSecurity.Concrete.PublicEncodingMatch

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

def referenceInput (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (position : EncodingPosition) : Option HashInput :=
  (selections position).map (fun selected => encodingRetryInput parameter position (messages position) selected.1.val)

def Match (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (input : HashInput) (answer : HashOutput) : Prop :=
  ∃ position, AtEncodingPosition parameter input position ∧
    referenceInput parameter messages selections position ≠ some input ∧
    decodeEncodingOutput answer = some (words position.lay position.tree position.leafIdx)

theorem known_eq_original (parameter : PublicParameter) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels))
    (selections : ReferenceFamily) :
    Match parameter (knownEncodingMessage known) words selections =
      Match parameter (canonicalGraphMessage labels) words selections := by
  rw [knownEncodingMessage_eq words disclosed known otsSecret ftsSecret labels hagrees]

theorem protected_not_match (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (known : Labels)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
    (row : EncodingRow)
    (hselect : FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (row.1, counter)) = selections row.1)
    (hkept : FirstSuccessPrefix.familyKept selections row) :
    ¬Match parameter (knownEncodingMessage known) words selections
      (knownEncodingCell parameter inputs hencoding known row).val (rows row) := by
  rintro ⟨position, hat, hnonreference, hdecode⟩
  have hrow : AtEncodingPosition parameter (knownEncodingCell parameter inputs hencoding known row).val row.1 := ⟨_, rfl⟩
  obtain rfl := atEncodingPosition_unique hat hrow
  have hnot : (selections row.1).map Prod.fst ≠ some row.2 := by
    intro heq
    apply hnonreference
    unfold referenceInput
    cases hselected : selections row.1 with
    | none => simp only [hselected, Option.map_none, reduceCtorEq] at heq
    | some selected =>
        have hcounter : selected.1 = row.2 := by simpa only [hselected, Option.map_some, Option.some.injEq] using heq
        simp only [Option.map_some, hcounter]
        rfl
  have hinvalid := FirstSuccessPrefix.kept_nonselected_invalid decodeEncodingOutput
    (fun counter => rows (row.1, counter)) (selections row.1) hselect row.2 hkept hnot
  rw [hdecode] at hinvalid
  contradiction

theorem prob_decode_word_le (word : Encoding) :
    Pr[fun answer => decodeEncodingOutput answer = some word | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ := by
  by_cases hexists : ∃ digest, TargetSum.decodeDigest digest = some word
  · obtain ⟨digest, hdigest⟩ := hexists
    calc
      _ ≤ Pr[fun answer => truncateHash answer = digest |
          (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] :=
        probEvent_mono fun _ _ hdecode => TargetSum.decodeDigest_some_injective hdecode hdigest
      _ = _ := HiddenLabelProbe.prob_truncate_eq digest
  · have hfalse (answer : HashOutput) : ¬decodeEncodingOutput answer = some word :=
      fun hdecode => hexists ⟨truncateHash answer, hdecode⟩
    simp only [probEvent_eq_tsum_ite, hfalse, if_false, tsum_zero, zero_le]

theorem prob_match_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (words : OtsReferenceWords) (selections : ReferenceFamily) (input : HashInput) :
    Pr[Match parameter messages words selections input | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ := by
  by_cases hexists : ∃ position, AtEncodingPosition parameter input position
  · obtain ⟨position, hat⟩ := hexists
    calc
      _ ≤ Pr[fun answer => decodeEncodingOutput answer = some (words position.lay position.tree position.leafIdx) |
          (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] := by
        apply probEvent_mono
        rintro answer _ ⟨other, hother, _, hdecode⟩
        obtain rfl := atEncodingPosition_unique hother hat
        exact hdecode
      _ ≤ _ := prob_decode_word_le _
  · have hfalse (answer : HashOutput) : ¬Match parameter messages words selections input answer := by
      rintro ⟨position, hat, _⟩
      exact hexists ⟨position, hat⟩
    simp only [probEvent_eq_tsum_ite, hfalse, if_false, tsum_zero, zero_le]

end SphincsSecurity.Concrete.PublicEncodingMatch
