import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.ReferencePrefixResidual
import SphincsSecurity.Proof.Residual.ResidualByteAction
namespace SphincsSecurity.Concrete.ResidualByteAction

open _root_.OracleComp OracleSpec CanonicalProbeRouting HiddenLabelObservation
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def freshPrefix (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (input : inputs) : Action inputs :=
  match route parameter words disclosed known input.val with
  | .outside => (knownEncodingRowAt parameter inputs hencoding known input).elim (.read input)
      (fun row => if FirstSuccessPrefix.familyKept selections row then .known (rows row) else .read input)
  | .canonical position => .known (publicReplies position)
  | .probe test => .probe input test

theorem freshPrefix_local (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (input : inputs) :
    Local input (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input) := by
  unfold freshPrefix
  cases route parameter words disclosed known input.val with
  | outside =>
      cases knownEncodingRowAt parameter inputs hencoding known input with
      | none => rfl
      | some row => simp only [Option.elim_some]; split <;> trivial
  | canonical _ => trivial
  | probe _ => rfl

theorem freshPrefix_eq_routed (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known actual : Labels)
    (hagrees : PublicAgreement words disclosed known actual) (publicReplies : CanonicalGraphLabels)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : inputs) :
    eval actual seed (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input) =
      routedTableReply publicReplies actual
        (finiteHashAnswer ∅ inputs (knownPrefixResidual parameter inputs hencoding known selections rows seed)) input.val
        (route parameter words disclosed known input.val) := by
  have hspec := route_spec parameter words disclosed known actual hagrees input.val
  rw [freshPrefix]
  cases hroute : route parameter words disclosed known input.val with
  | outside =>
      rw [routedTableReply, finiteHashAnswer_none ∅ inputs _ input.val input.property (by simp), knownPrefixResidual_lookup]
      cases knownEncodingRowAt parameter inputs hencoding known input with
      | none => rfl
      | some row => simp only [Option.elim_some]; split <;> rfl
  | canonical position => rfl
  | probe test =>
      rw [hroute] at hspec
      have hat : ∃ position, AtPosition parameter input.val position := by
        cases test with
        | pair child parent hne candidate => exact ⟨hspec.choose, hspec.choose_spec.1⟩
        | output parent => exact ⟨hspec.choose, hspec.choose_spec.1⟩
      obtain ⟨position, hat⟩ := hat
      rw [routedTableReply, finiteHashAnswer_none ∅ inputs _ input.val input.property (by simp),
        knownPrefixResidual_structural parameter inputs hencoding known selections rows seed input position hat]
      rfl

theorem freshPrefix_eq_original (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (replies publicReplies : CanonicalGraphLabels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret replies))
    (hreplies : ∀ position, ¬CanonicalCoordinate.Hidden words disclosed (.graph position) → publicReplies position = replies position)
    (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (seed : inputs → HashOutput) (input : inputs) :
    let actual := CanonicalCoordinate.value otsSecret ftsSecret replies
    let answer := programmedHash parameter otsSecret ftsSecret replies
      (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hencoding replies selections rows seed)) input.val
    eval actual seed (freshPrefix parameter inputs hencoding words disclosed known publicReplies selections rows input) =
      if CanonicalProbeRouting.Bad parameter words disclosed actual input.val answer then none else some answer := by
  dsimp only
  rw [freshPrefix_eq_routed parameter inputs hencoding words disclosed known _ hagrees publicReplies selections rows seed input,
    ← stoppedTableReply_route parameter words disclosed known _ hagrees replies publicReplies hreplies,
    stoppedTableReply, tableReply_programmed,
    canonicalPrefixResidual_eq_known parameter inputs hencoding words disclosed known otsSecret ftsSecret replies hagrees]

end SphincsSecurity.Concrete.ResidualByteAction
