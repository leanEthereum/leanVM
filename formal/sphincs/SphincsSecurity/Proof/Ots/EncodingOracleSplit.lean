import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.CanonicalEncodingSampling
import SphincsSecurity.Proof.Hypertree.CanonicalGraphSampling
import SphincsSecurity.Proof.Base.UniformTableSplit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

noncomputable def encodingInputCell (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (input : canonicalEncodingInputs parameter) : inputs :=
  Set.inclusion hencoding input

theorem encodingInputCell_injective (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) : Function.Injective (encodingInputCell parameter inputs hencoding) := by
  exact Set.inclusion_injective hencoding

abbrev NonencodingRows (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :=
  UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) → HashOutput

noncomputable def joinEncodingTable (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (encoding : canonicalEncodingInputs parameter → HashOutput)
    (outside : NonencodingRows parameter inputs hencoding) : inputs → HashOutput :=
  UniformTableSplit.join (encodingInputCell parameter inputs hencoding)
    (encodingInputCell_injective parameter inputs hencoding) encoding outside

noncomputable def nonencodingAnswer (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl HashSpec Id := finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding (fun _ => 0) outside)

theorem canonicalGraphInput_not_encodingInputs (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (position : Position) (labels : CanonicalGraphLabels) :
    canonicalGraphInput parameter otsSecret ftsSecret position labels ∉ canonicalEncodingInputs parameter := by
  intro h
  rw [canonicalEncodingInputs] at h
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at h
  obtain ⟨encodingPosition, pair, heq⟩ := h
  have hencoding : AtEncodingPosition parameter (canonicalGraphInput parameter otsSecret ftsSecret position labels)
      encodingPosition := ⟨_, heq.symm⟩
  exact hencoding.not_atPosition position ⟨_, rfl⟩

theorem canonicalGraphCell_not_encodingRange (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (position : Position) (labels : CanonicalGraphLabels) :
    canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position labels ∉
      Set.range (encodingInputCell parameter inputs hencoding) := by
  exact UniformTableSplit.inclusion_not_range hencoding
    (canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position labels)
    (canonicalGraphInput_not_encodingInputs parameter otsSecret ftsSecret position labels)

theorem canonicalGraphLabels_joinEncodingTable (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (hgraph : canonicalGraphInputs parameter ⊆ inputs)
    (encoding : canonicalEncodingInputs parameter → HashOutput) (outside : NonencodingRows parameter inputs hencoding) :
    canonicalGraphLabels parameter otsSecret ftsSecret
        (finiteHashAnswer ∅ inputs (joinEncodingTable parameter inputs hencoding encoding outside)) =
      canonicalGraphLabels parameter otsSecret ftsSecret (nonencodingAnswer parameter inputs hencoding outside) := by
  apply FiniteGraphSampling.read_congr
  intro position labels
  have hrow := hgraph (canonicalGraphInput_mem parameter otsSecret ftsSecret position labels)
  rw [finiteHashAnswer_none ∅ inputs _ _ hrow (by simp), nonencodingAnswer,
    finiteHashAnswer_none ∅ inputs _ _ hrow (by simp)]
  let cell : UniformTableSplit.Outside (encodingInputCell parameter inputs hencoding) :=
    ⟨canonicalGraphCell parameter otsSecret ftsSecret inputs hgraph position labels,
      canonicalGraphCell_not_encodingRange parameter otsSecret ftsSecret inputs hencoding hgraph position labels⟩
  exact (UniformTableSplit.join_outside _ _ encoding outside cell).trans
    (UniformTableSplit.join_outside _ _ (fun _ => 0) outside cell).symm

noncomputable def referenceCounterCell (parameter : PublicParameter) (position : EncodingPosition) (message : Digest)
    (counter : Fin encodingAttemptLimit) : canonicalEncodingInputs parameter :=
  ⟨encodingRetryInput parameter position message counter.val,
    encodingRetryInput_mem_canonicalEncodingInputs parameter position message counter⟩

theorem referenceCounterCell_injective (parameter : PublicParameter) (position : EncodingPosition) (message : Digest) :
    Function.Injective (referenceCounterCell parameter position message) := by
  intro left right heq
  exact Fin.ext (encodingRetryInput_injective_of_lt left.isLt right.isLt (congrArg Subtype.val heq))

noncomputable def outsideGraphMessage (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (outside : NonencodingRows key.parameter inputs hencoding)
    (position : EncodingPosition) : Digest :=
  canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret
    (nonencodingAnswer key.parameter inputs hencoding outside)) position

end SphincsSecurity.Concrete
