import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.ReferenceFamilyGame
import SphincsSecurity.Proof.Reference.ReferenceResidualSampling
import SphincsSecurity.Proof.Residual.ResidualGraphGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def referenceResidualGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) : SPMF (ReferenceFamily × (Bool × SigningBoundaryTrace)) := do
  let parameter ← 𝒟[sampleParameter]
  let otsSecret ← 𝒟[sampleOtsSecrets]
  let ftsSecret ← 𝒟[sampleFtsSecrets]
  let key : SecretKey := ⟨parameter, 0, otsSecret, ftsSecret⟩
  let sampled ← 𝒟[graphReferenceSample parameter inputs (hencoding parameter)]
  let f := programmedHash parameter otsSecret ftsSecret sampled.2.1 (finiteHashAnswer ∅ inputs sampled.2.2)
  let result ← 𝒟[referenceFamilyFrontierRest key f sampled.2.1 sampled.1 dummy adversary]
  pure (sampled.1, result)

theorem referenceResidualGame_erased (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    Prod.snd <$> referenceResidualGame inputs hencoding dummy adversary =
      𝒟[residualGraphOracleGame inputs dummy adversary] := by
  rw [referenceResidualGame, residualGraphOracleGame]
  simp only [map_bind, map_pure, bind_pure, evalDist_bind]
  apply congrArg (𝒟[sampleParameter] >>= ·)
  funext parameter
  apply congrArg (𝒟[sampleOtsSecrets] >>= ·)
  funext otsSecret
  apply congrArg (𝒟[sampleFtsSecrets] >>= ·)
  funext ftsSecret
  have h := graphReferenceSample_bind_selected ⟨parameter, 0, otsSecret, ftsSecret⟩ inputs (hencoding parameter)
    (fun selections labels residual => referenceFamilyFrontierRest ⟨parameter, 0, otsSecret, ftsSecret⟩
      (programmedHash parameter otsSecret ftsSecret labels (finiteHashAnswer ∅ inputs residual)) labels selections dummy adversary)
  simpa only [referenceFamilyFrontierRest_selected, evalDist_bind] using h

theorem evalDist_boundaryGameCore_referenceResidual (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary)
    (hinputs : hashInputs (boundaryGameCore adversary) ⊆ inputs) :
    𝒟[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referenceResidualGame inputs hencoding dummy adversary := by
  rw [referenceResidualGame_erased]
  exact evalDist_boundaryGameCore_residualGraph inputs hgraph dummy adversary hinputs

theorem referenceResidualGame_hashCalls_le (dummy : OtsReferenceWords) (adversary : Adversary)
    (q : Nat) (hbound : HasHashQueryBound scheme adversary q) (result : ReferenceFamily × (Bool × SigningBoundaryTrace))
    (hresult : result ∈ support (referenceResidualGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)) :
    result.2.2.hashCalls ≤ q := by
  apply boundaryGameCore_hashCalls_le adversary q hbound result.2
  apply (mem_support_iff_of_evalDist_eq
    (mx' := Prod.snd <$> referenceResidualGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)
    (evalDist_boundaryGameCore_referenceResidual (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary)
      (canonicalGraphInputs_subset_gameInputs adversary) dummy adversary
      (hashInputs_subset_canonicalGraphGameInputs adversary)) result.2).mpr
  rw [support_map]
  exact ⟨result, hresult, rfl⟩

end SphincsSecurity.Concrete
