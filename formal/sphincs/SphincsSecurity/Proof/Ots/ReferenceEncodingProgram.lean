import SphincsSecurity.Proof.Hypertree.FrontierEncodingCongruence
import SphincsSecurity.Proof.Reference.CausalFrontierProgram
import SphincsSecurity.Proof.Ots.ReferenceFamilyGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs frontierSigningRun frontierRoot

theorem joinEncodingTable_agrees_outside (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
    (left right : canonicalEncodingInputs parameter → HashOutput)
    (outside : NonencodingRows parameter inputs hencoding) :
    AgreeOutsideEncoding parameter
      (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding left outside))
      (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding right outside)) := by
  intro input hnot
  by_cases hin : input ∈ inputs
  · rw [finiteHashAnswer_none ∅ inputs _ _ hin (by simp), finiteHashAnswer_none ∅ inputs _ _ hin (by simp)]
    let cell : UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) :=
      ⟨⟨input, hin⟩, UniformTableSplit.inclusion_not_range hencoding ⟨input, hin⟩ hnot⟩
    exact (UniformTableSplit.join_outside _ _ left outside cell).trans
      (UniformTableSplit.join_outside _ _ right outside cell).symm
  · simp only [finiteHashAnswer, QueryCache.empty_apply, Option.getD_none, dif_neg hin]

theorem frontierLayerSearch_eq_referenceSelection (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (selections : ReferenceFamily)
    (hselected : referenceTableSelection key f = selections) (index : Index) (lay : Layer) :
    frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay =
      referenceSelectionResult (selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) := by
  rw [frontierLayerSearch, eval_frontierLayerMessage key f words frontier hfrontier,
    ← canonicalEncodingSearch_at,
    ← referenceSelectionResult_eq_search key f ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩, hselected]

namespace CausalFrontierProgram

theorem game_eq_of_encoding (parameter : PublicParameter) (f g : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) (h : AgreeOutsideEncoding parameter f g)
    (hsearch : ∀ index lay, frontierLayerSearch parameter f ftsSecret words frontier index lay =
      frontierLayerSearch parameter g ftsSecret words frontier index lay) :
    game parameter f ftsSecret words frontier adversary = game parameter g ftsSecret words frontier adversary := by
  have hsign (root : Digest) (message : Message) :
      frontierSigningRun parameter root (maskOtsPrefixes parameter words f) ftsSecret words frontier message =
        frontierSigningRun parameter root (maskOtsPrefixes parameter words g) ftsSecret words frontier message := by
    rw [← frontierSigningRun_eq_of_agree parameter words f _ (maskOtsPrefixes_agrees parameter words f),
      ← frontierSigningRun_eq_of_agree parameter words g _ (maskOtsPrefixes_agrees parameter words g)]
    exact h.frontierSigningRun root ftsSecret words frontier hsearch message
  have himpl (root : Digest) : adversaryImpl parameter root f ftsSecret words frontier =
      adversaryImpl parameter root g ftsSecret words frontier := by
    funext input
    cases input with
    | inl input => rfl
    | inr message => simp only [adversaryImpl_signing, hsign]
  rw [game, game,
    ← frontierRoot_eq_of_agree parameter words f _ (maskOtsPrefixes_agrees parameter words f),
    ← frontierRoot_eq_of_agree parameter words g _ (maskOtsPrefixes_agrees parameter words g),
    h.frontierRoot words frontier]
  simp only [gameRest, adversaryRun, himpl]

end CausalFrontierProgram

theorem joinedEncoding_isSigningFrontier (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs key.parameter → HashOutput)
    (outside : NonencodingRows key.parameter inputs hencoding) (words : OtsReferenceWords) :
    IsSigningFrontier key (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside))
      words (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
        (nonencodingAnswer key.parameter inputs hencoding outside)) words) := by
  have hfrontier := canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret
    (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) words key.root
  rw [canonicalGraphLabels_joinEncodingTable _ _ _ _ hencoding hgraph] at hfrontier
  rw [hfrontier]
  exact isSigningFrontier_canonical key _ words

theorem joinedEncoding_program_eq (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (left right : canonicalEncodingInputs key.parameter → HashOutput)
    (outside : NonencodingRows key.parameter inputs hencoding) (selections : ReferenceFamily)
    (hleft : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding left outside)) = selections)
    (hright : referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding right outside)) = selections)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    let words := referenceFamilyWords selections dummy
    let frontier := canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
      (nonencodingAnswer key.parameter inputs hencoding outside)) words
    CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding left outside))
        key.ftsSecret words frontier adversary =
      CausalFrontierProgram.game key.parameter
        (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding right outside))
        key.ftsSecret words frontier adversary := by
  dsimp only
  apply CausalFrontierProgram.game_eq_of_encoding
  · exact joinEncodingTable_agrees_outside _ _ _ _ _ _
  · intro index lay
    rw [frontierLayerSearch_eq_referenceSelection key _ _ _
      (joinedEncoding_isSigningFrontier key inputs hencoding hgraph left outside _) selections hleft,
      frontierLayerSearch_eq_referenceSelection key _ _ _
      (joinedEncoding_isSigningFrontier key inputs hencoding hgraph right outside _) selections hright]

end SphincsSecurity.Concrete
