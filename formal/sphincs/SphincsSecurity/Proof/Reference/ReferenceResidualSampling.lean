import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Residual.CanonicalResidualQuery
import SphincsSecurity.Proof.Ots.EncodingFamilyOracleSplit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem readCanonicalEncodingRows_programmedHash (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (labels encodingLabels : CanonicalGraphLabels)
    (residual : QueryImpl HashSpec Id) :
    readCanonicalEncodingRows parameter encodingLabels (programmedHash parameter otsSecret ftsSecret labels residual) =
      readCanonicalEncodingRows parameter encodingLabels residual := by
  funext row
  apply programmedHash_other
  intro position heq
  have hencoding : AtEncodingPosition parameter (canonicalEncodingRowInput parameter encodingLabels row) row.1 := ⟨_, rfl⟩
  exact hencoding.not_atPosition position ⟨_, heq⟩

theorem referenceTableSelection_programmedHash (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels)
    (residual : inputs → HashOutput) (position : EncodingPosition) :
    referenceTableSelection key
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)) position =
      FirstSuccessTable.select decodeEncodingOutput
        (fun counter => residual (canonicalEncodingCell key.parameter inputs hencoding labels (position, counter))) := by
  rw [referenceTableSelection, canonicalGraphLabels_programmedHash, readCanonicalEncodingRows_programmedHash,
    readCanonicalEncodingRows_finite key.parameter inputs hencoding]
  rfl

noncomputable def residualReferenceSample (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (labels : CanonicalGraphLabels) :
    PMF (ReferenceFamily × (inputs → HashOutput)) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
    (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
      (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside (canonicalEncodingCell parameter inputs hencoding labels) → HashOutput)).map
        (fun remaining => (selections, UniformTableSplit.join (canonicalEncodingCell parameter inputs hencoding labels)
          (canonicalEncodingCell_injective parameter inputs hencoding labels) (Function.uncurry rows) remaining))))

theorem uniform_joint_residualReference (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (labels : CanonicalGraphLabels) :
    (PMF.uniformOfFintype (inputs → HashOutput)).map (fun residual =>
      (referenceTableSelection key
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)), residual)) =
      residualReferenceSample key.parameter inputs hencoding labels := by
  have hselection (residual : inputs → HashOutput) :
      referenceTableSelection key
        (programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)) =
      fun position => FirstSuccessTable.select decodeEncodingOutput
        (fun counter => residual (canonicalEncodingCell key.parameter inputs hencoding labels (position, counter))) := by
    funext position
    exact referenceTableSelection_programmedHash key inputs hencoding labels residual position
  have h := UniformTableSplit.uniform_bind_firstSuccessFamily
    (canonicalEncodingCell key.parameter inputs hencoding labels)
    (canonicalEncodingCell_injective key.parameter inputs hencoding labels)
    decodeEncodingOutput decodeEncodingOutput_invalid_nonempty (fun selections residual => PMF.pure (selections, residual))
  simpa only [hselection, residualReferenceSample, PMF.map, Function.comp_def] using h

noncomputable def graphReferenceSample (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :
    PMF (ReferenceFamily × (CanonicalGraphLabels × (inputs → HashOutput))) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun selections =>
    (PMF.uniformOfFintype CanonicalGraphLabels).bind (fun labels =>
      (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty selections).bind
        (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside (canonicalEncodingCell parameter inputs hencoding labels) → HashOutput)).map
          (fun remaining => (selections, (labels, UniformTableSplit.join (canonicalEncodingCell parameter inputs hencoding labels)
            (canonicalEncodingCell_injective parameter inputs hencoding labels) (Function.uncurry rows) remaining))))))

theorem uniformGraph_bind_residualReference (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) :
    (PMF.uniformOfFintype CanonicalGraphLabels).bind (fun labels =>
      (residualReferenceSample parameter inputs hencoding labels).map (fun result => (result.1, (labels, result.2)))) =
      graphReferenceSample parameter inputs hencoding := by
  simp only [residualReferenceSample, graphReferenceSample, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_comm]

theorem uniform_joint_graphReference (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) :
    (PMF.uniformOfFintype CanonicalGraphLabels).bind (fun labels =>
      (PMF.uniformOfFintype (inputs → HashOutput)).map (fun residual =>
        (referenceTableSelection key
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)), (labels, residual)))) =
      graphReferenceSample key.parameter inputs hencoding := by
  rw [← uniformGraph_bind_residualReference]
  apply congrArg (PMF.uniformOfFintype CanonicalGraphLabels).bind
  funext labels
  rw [← uniform_joint_residualReference key inputs hencoding labels, PMF.map_comp]
  rfl

noncomputable local instance referenceResidualLabelsSampleable : SampleableType CanonicalGraphLabels := SampleableType.ofFintype CanonicalGraphLabels
noncomputable local instance referenceResidualTableSampleable (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

theorem graphReferenceSample_bind_selected {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (next : ReferenceFamily → CanonicalGraphLabels → (inputs → HashOutput) → ProbComp Result) :
    (𝒟[graphReferenceSample key.parameter inputs hencoding] >>= fun result => 𝒟[next result.1 result.2.1 result.2.2]) =
      𝒟[do
        let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
        let residual ← sampleHashTable inputs
        next (referenceTableSelection key
          (programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual))) labels residual] := by
  rw [← uniform_joint_graphReference key inputs hencoding]
  simp only [← PMF.monad_map_eq_map, ← PMF.monad_bind_eq_bind, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    evalDist_bind, evalDist_pure, Function.comp_apply, sampleHashTable, evalDist_uniformSample]

end SphincsSecurity.Concrete
