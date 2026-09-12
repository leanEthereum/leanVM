import SphincsSecurity.Proof.Hypertree.StructuralOracleSplit
import SphincsSecurity.Proof.Reference.ReferenceInstrumentedGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition Finset.univ

noncomputable local instance (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _

noncomputable local instance : SampleableType CanonicalGraphLabels := SampleableType.ofFintype _

theorem referenceFamilyOracleSample_graph_bind {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (next : QueryImpl HashSpec Id → CanonicalGraphLabels → ReferenceFamily → ProbComp Result) :
    (𝒟[referenceFamilyOracleSample key inputs hencoding] >>= fun reference =>
      let f := finiteHashAnswer ∅ inputs reference.2
      𝒟[next f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) reference.1]) =
      𝒟[do
        let labels ← ($ᵗ CanonicalGraphLabels : ProbComp _)
        let residual ← sampleHashTable inputs
        let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)
        next f labels (referenceTableSelection key f)] := by
  rw [referenceFamilyOracleSample_bind_selected key inputs hencoding hgraph
    (fun selections table => next (finiteHashAnswer ∅ inputs table)
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret (finiteHashAnswer ∅ inputs table)) selections)]
  rw [evalDist_canonicalGraph_bind_eq_plant key.parameter key.otsSecret key.ftsSecret inputs hgraph
    (fun labels table => next (finiteHashAnswer ∅ inputs table) labels (referenceTableSelection key (finiteHashAnswer ∅ inputs table)))]
  rw [evalDist_plantCanonicalGraph_bind_eq_residual key.parameter key.otsSecret key.ftsSecret inputs hgraph
    (fun labels table => next (finiteHashAnswer ∅ inputs table) labels (referenceTableSelection key (finiteHashAnswer ∅ inputs table)))]
  simp only [finiteHashAnswer_program_eq]

noncomputable def referenceGraphContextRest {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (CanonicalGraphLabels × ReferenceFamily × Result) := do
  let reference ← 𝒟[referenceFamilyOracleSample key inputs hencoding]
  let f := finiteHashAnswer ∅ inputs reference.2
  let labels := canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f
  let result ← 𝒟[referenceInstrumentedRest observer key f labels reference.1 dummy adversary]
  pure (labels, reference.1, result)

theorem referenceGraphContextRest_residual {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceGraphContextRest observer key inputs hencoding dummy adversary = (do
      let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
      let residual ← 𝒟[PMF.uniformOfFintype (inputs → HashOutput)]
      let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)
      let selections := referenceTableSelection key f
      let result ← 𝒟[referenceInstrumentedRest observer key f labels selections dummy adversary]
      pure (labels, selections, result)) := by
  have h := referenceFamilyOracleSample_graph_bind key inputs hencoding hgraph
    (fun f labels selections => do
      let result ← referenceInstrumentedRest observer key f labels selections dummy adversary
      pure (labels, selections, result))
  simpa only [referenceGraphContextRest, evalDist_bind, evalDist_pure, evalDist_uniformSample, sampleHashTable] using h

theorem uniformStructural_split (parameter : PublicParameter) (inputs : Finset HashInput) :
    𝒟[PMF.uniformOfFintype (inputs → HashOutput)] = (do
      let outside ← 𝒟[PMF.uniformOfFintype (NonstructuralRows parameter inputs)]
      let rows ← 𝒟[PMF.uniformOfFintype (structuralInputs parameter inputs → HashOutput)]
      pure (joinStructuralTable parameter inputs rows outside)) := by
  have h := (UniformTableSplit.uniform_join (structuralInputCell parameter inputs) (structuralInputCell_injective parameter inputs)
    (Answer := HashOutput)).trans (PMF.bind_comm
      (PMF.uniformOfFintype (structuralInputs parameter inputs → HashOutput))
      (PMF.uniformOfFintype (NonstructuralRows parameter inputs))
      (fun rows outside => PMF.pure (joinStructuralTable parameter inputs rows outside)))
  have hd := congrArg (fun law : PMF (inputs → HashOutput) => 𝒟[law]) h
  simpa only [← PMF.monad_bind_eq_bind, ← PMF.monad_pure_eq_pure, evalDist_bind, evalDist_pure,
    Function.comp_def, joinStructuralTable] using hd

theorem referenceGraphContextRest_conditioned {Result : Type} (observer : FrontierObserver Result)
    (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
    (hgraph : canonicalGraphInputs key.parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary) :
    referenceGraphContextRest observer key inputs hencoding dummy adversary = (do
      let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
      let outside ← 𝒟[PMF.uniformOfFintype (NonstructuralRows key.parameter inputs)]
      let selections := referenceTableSelection key (structuralAnswer key inputs labels outside (fun _ => 0))
      let words := referenceFamilyWords selections dummy
      let rows ← 𝒟[PMF.uniformOfFintype (structuralInputs key.parameter inputs → HashOutput)]
      let result ← 𝒟[simulateQ (fixedHashWorld (structuralAnswer key inputs labels outside rows))
        (observer key.parameter words (canonicalGraphFrontier key.otsSecret labels words)
          (structuralProgram key inputs labels outside words adversary))]
      pure (labels, selections, result)) := by
  rw [referenceGraphContextRest_residual observer key inputs hencoding hgraph dummy adversary, uniformStructural_split]
  simp only [bind_assoc, pure_bind]
  apply congrArg (𝒟[PMF.uniformOfFintype CanonicalGraphLabels] >>= ·)
  funext labels
  apply congrArg (𝒟[PMF.uniformOfFintype (NonstructuralRows key.parameter inputs)] >>= ·)
  funext outside
  apply congrArg (𝒟[PMF.uniformOfFintype (structuralInputs key.parameter inputs → HashOutput)] >>= ·)
  funext rows
  change (𝒟[referenceInstrumentedRest observer key (structuralAnswer key inputs labels outside rows) labels
      (referenceTableSelection key (structuralAnswer key inputs labels outside rows)) dummy adversary] >>= fun result =>
        pure (labels, referenceTableSelection key (structuralAnswer key inputs labels outside rows), result)) = _
  rw [structuralAnswer_selections key inputs labels outside rows (fun _ => 0), referenceInstrumentedRest, structuralProgram_eq]

abbrev GraphContextResult (Result : Type) := SecretKey × CanonicalGraphLabels × ReferenceFamily × Result

noncomputable def referenceGraphContextGame {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (GraphContextResult Result) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let result ← referenceGraphContextRest observer key inputs (hencoding parameter) dummy adversary
  pure (key, result)

theorem referenceGraphContextGame_erased {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : GraphContextResult Result => (result.1.parameter, result.2.2.1, result.2.2.2)) <$>
      referenceGraphContextGame observer inputs hencoding dummy adversary =
        referenceInstrumentedGame observer inputs hencoding dummy adversary := by
  simp only [referenceGraphContextGame, referenceGraphContextRest, referenceInstrumentedGame,
    map_bind, map_pure, bind_assoc, pure_bind]

end SphincsSecurity.Concrete
