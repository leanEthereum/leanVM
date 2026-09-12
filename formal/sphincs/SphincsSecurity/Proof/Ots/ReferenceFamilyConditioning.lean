import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.EncodingFamilyOracleSplit
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs
set_option backward.isDefEq.respectTransparency false

theorem uniform_bind_referenceFamily {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (next : ReferenceFamily → (inputs → HashOutput) → PMF Result) :
    (PMF.uniformOfFintype (inputs → HashOutput)).bind
        (fun table => next (referenceTableSelection key (finiteHashAnswer ∅ inputs table)) table) =
      (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind (fun outside =>
        (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun results =>
          (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty results).bind
            (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside
              (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput)).bind
                (fun remaining => next results (referenceFamilyOracleTable key inputs hencoding outside rows remaining))))) := by
  rw [UniformTableSplit.uniform_bind_split (encodingInputCell key.parameter inputs hencoding)
    (encodingInputCell_injective key.parameter inputs hencoding), PMF.bind_comm]
  apply congrArg (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind
  funext outside
  change ((PMF.uniformOfFintype (canonicalEncodingInputs key.parameter → HashOutput)).bind
    (fun encoding => next (fun position => referenceTableSelection key
      (finiteHashAnswer ∅ inputs (joinEncodingTable key.parameter inputs hencoding encoding outside)) position)
      (joinEncodingTable key.parameter inputs hencoding encoding outside))) = _
  simp only [referenceTableSelection_joinEncodingTable key inputs hencoding hgraph]
  exact UniformTableSplit.uniform_bind_firstSuccessFamily
    (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside))
    (referenceFamilyCell_injective key.parameter (outsideGraphMessage key inputs hencoding outside))
    decodeEncodingOutput decodeEncodingOutput_invalid_nonempty
    (fun results encoding => next results (joinEncodingTable key.parameter inputs hencoding encoding outside))

noncomputable def referenceFamilyOracleSample (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) : PMF (ReferenceFamily × (inputs → HashOutput)) :=
  (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).bind (fun results =>
    (PMF.uniformOfFintype (NonencodingRows key.parameter inputs hencoding)).bind (fun outside =>
      (FirstSuccessFamily.afterSelect decodeEncodingOutput encodingAttemptLimit decodeEncodingOutput_invalid_nonempty results).bind
        (fun rows => (PMF.uniformOfFintype (UniformTableSplit.Outside
          (referenceFamilyCell key.parameter (outsideGraphMessage key inputs hencoding outside)) → HashOutput)).map
            (fun remaining => (results, referenceFamilyOracleTable key inputs hencoding outside rows remaining)))))

theorem uniform_joint_eq_referenceFamilyOracleSample (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) :
    (PMF.uniformOfFintype (inputs → HashOutput)).map
        (fun table => (referenceTableSelection key (finiteHashAnswer ∅ inputs table), table)) =
      referenceFamilyOracleSample key inputs hencoding := by
  have h := uniform_bind_referenceFamily key inputs hencoding hgraph (fun results table => PMF.pure (results, table))
  rw [PMF.bind_comm] at h
  exact h

theorem referenceFamilyOracleSample_selections (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (result : ReferenceFamily × (inputs → HashOutput))
    (hresult : result ∈ (referenceFamilyOracleSample key inputs hencoding).support) :
    result.1 = referenceTableSelection key (finiteHashAnswer ∅ inputs result.2) := by
  rw [← uniform_joint_eq_referenceFamilyOracleSample key inputs hencoding hgraph, PMF.mem_support_map_iff] at hresult
  obtain ⟨table, _, rfl⟩ := hresult
  rfl

noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_4 (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype (inputs → HashOutput)

theorem referenceFamilyOracleSample_bind_selected {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (next : ReferenceFamily → (inputs → HashOutput) → ProbComp Result) :
    (𝒟[referenceFamilyOracleSample key inputs hencoding] >>= fun result => 𝒟[next result.1 result.2]) =
      𝒟[do
        let table ← sampleHashTable inputs
        next (referenceTableSelection key (finiteHashAnswer ∅ inputs table)) table] := by
  rw [← uniform_joint_eq_referenceFamilyOracleSample key inputs hencoding hgraph]
  simp only [← PMF.monad_map_eq_map, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    evalDist_bind, evalDist_pure, Function.comp_apply, sampleHashTable, evalDist_uniformSample]

end SphincsSecurity.Concrete
