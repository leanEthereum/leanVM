import SphincsSecurity.Proof.Forced.FtsGuessReference
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition
  frontierRoot maskOtsPrefixes frontierSigningRun boundaryEval

theorem referenceFamilyOracleSample_auxiliary_bind {Result : Type} (key : SecretKey) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs) (hgraph : canonicalGraphInputs key.parameter ⊆ inputs)
    (next : QueryImpl HashSpec Id → CanonicalGraphLabels → ReferenceFamily → ProbComp Result) :
    (𝒟[referenceFamilyOracleSample key inputs hencoding] >>= fun reference =>
      let f := finiteHashAnswer ∅ inputs reference.2
      𝒟[next f (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) reference.1]) = (do
        let auxiliary ← 𝒟[referenceAuxiliarySample inputs]
        let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
        let f := programmedHash key.parameter key.otsSecret key.ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual key.parameter inputs hencoding labels auxiliary.rows auxiliary.seed))
        𝒟[next f labels auxiliary.selections]) := by
  have hfirst := referenceFamilyOracleSample_graph_bind key inputs hencoding hgraph next
  have hsecond := graphReferenceSample_bind_selected key inputs hencoding
    (fun selections labels residual => next
      (programmedHash key.parameter key.otsSecret key.ftsSecret labels (finiteHashAnswer ∅ inputs residual)) labels selections)
  have h := hfirst.trans hsecond.symm
  rw [h]
  simp only [graphReferenceSample_eq_auxiliary, ← PMF.monad_bind_eq_bind, ← PMF.monad_map_eq_map,
    evalDist_bind, evalDist_map, bind_assoc, bind_map_left]

theorem referenceForgeryGame_bind_auxiliary {Result : Type} (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (next : SecretKey → QueryImpl HashSpec Id → CanonicalGraphLabels → ReferenceFamily → AdversaryTrace → ProbComp Result) :
    (referenceForgeryGame inputs hencoding dummy adversary >>= fun sample =>
      let f := finiteHashAnswer ∅ inputs sample.2.1.2
      𝒟[next sample.1 f (canonicalGraphLabels sample.1.parameter sample.1.otsSecret sample.1.ftsSecret f) sample.2.1.1 sample.2.2]) = (do
        let parameter ← 𝒟[sampleParameter]
        let otsSecret ← 𝒟[sampleOtsSecrets]
        let ftsSecret ← 𝒟[sampleFtsSecrets]
        let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
        let auxiliary ← 𝒟[referenceAuxiliarySample inputs]
        let labels ← 𝒟[PMF.uniformOfFintype CanonicalGraphLabels]
        let f := programmedHash parameter otsSecret ftsSecret labels
          (finiteHashAnswer ∅ inputs (canonicalReferenceResidual parameter inputs (hencoding parameter) labels auxiliary.rows auxiliary.seed))
        let before ← 𝒟[referenceForgeryRest key f labels auxiliary.selections dummy adversary]
        𝒟[next key f labels auxiliary.selections before]) := by
  simp only [referenceForgeryGame, bind_assoc, pure_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  have h := referenceFamilyOracleSample_auxiliary_bind ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs
    (hencoding parameter) (hgraph parameter) (fun f labels selections => do
      let before ← referenceForgeryRest ⟨parameter, 0, otsSecret, ftsSecret⟩ f labels selections dummy adversary
      next ⟨parameter, 0, otsSecret, ftsSecret⟩ f labels selections before)
  simpa only [evalDist_bind] using h

end SphincsSecurity.Concrete
