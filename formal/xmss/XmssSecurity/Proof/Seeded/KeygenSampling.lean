import XmssSecurity.Proof.Seeded.KeygenExpansion

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev ChainSecrets := Epoch → ChainIndex → Digest

def chainOutputHalves : ChainOutputs ≃ (ChainSecrets × ChainSecrets) where
  toFun outputs := (fun epoch chain => (Rom.hashOutputEquivDigestPair (outputs epoch chain)).1,
    outputSecrets outputs)
  invFun halves := fun epoch chain =>
    Rom.hashOutputEquivDigestPair.symm (halves.1 epoch chain, halves.2 epoch chain)
  left_inv outputs := by
    funext epoch chain
    exact Rom.hashOutputEquivDigestPair.symm_apply_apply (outputs epoch chain)
  right_inv halves := by
    apply Prod.ext <;> funext epoch chain
    · exact congrArg Prod.fst (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (halves.1 epoch chain, halves.2 epoch chain))
    · exact congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply
        (halves.1 epoch chain, halves.2 epoch chain))

theorem outputSecrets_from_halves (high low : ChainSecrets) :
    outputSecrets (chainOutputHalves.symm (high, low)) = low :=
  congrArg Prod.snd (chainOutputHalves.apply_symm_apply (high, low))

theorem truncate_from_halves (high low : Digest) :
    truncateHash (Rom.hashOutputEquivDigestPair.symm (high, low)) = low :=
  congrArg Prod.snd (Rom.hashOutputEquivDigestPair.apply_symm_apply (high, low))

theorem evalDist_chainOutputs_from_halves :
    𝒟[$ᵗ ChainOutputs] = 𝒟[do
      let low ← $ᵗ ChainSecrets
      let high ← $ᵗ ChainSecrets
      pure (chainOutputHalves.symm (high, low))] := by
  calc
    _ = 𝒟[chainOutputHalves.symm <$> ($ᵗ (ChainSecrets × ChainSecrets))] :=
      (evalDist_map_bijective_uniform_cross (α := ChainSecrets × ChainSecrets) (β := ChainOutputs)
        chainOutputHalves.symm chainOutputHalves.symm.bijective).symm
    _ = 𝒟[chainOutputHalves.symm <$> (do
        let high ← $ᵗ ChainSecrets
        let low ← $ᵗ ChainSecrets
        pure (high, low))] := by
      rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

def programmedCache (seed : MasterSeed) (parameter : PublicParameter) (secret : ChainSecrets)
    (parameterHigh : Digest) (secretHigh : ChainSecrets) : QueryCache HashSpec :=
  derivationCache seed (Rom.hashOutputEquivDigestPair.symm (parameterHigh, parameter))
    (chainOutputHalves.symm (secretHigh, secret))

theorem evalDist_parameterOutput_from_halves :
    𝒟[$ᵗ HashOutput] = 𝒟[do
      let low ← $ᵗ Digest
      let high ← $ᵗ Digest
      pure (Rom.hashOutputEquivDigestPair.symm (high, low))] := by
  calc
    _ = 𝒟[Rom.hashOutputEquivDigestPair.symm <$> ($ᵗ (Digest × Digest))] :=
      (evalDist_map_bijective_uniform_cross (α := Digest × Digest) (β := HashOutput)
        Rom.hashOutputEquivDigestPair.symm Rom.hashOutputEquivDigestPair.symm.bijective).symm
    _ = 𝒟[Rom.hashOutputEquivDigestPair.symm <$> (do
        let high ← $ᵗ Digest
        let low ← $ᵗ Digest
        pure (high, low))] := by
      rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _

theorem evalDist_samplePublicParameter : 𝒟[Concrete.samplePublicParameter] = 𝒟[$ᵗ Digest] := by
  unfold Concrete.samplePublicParameter
  rw [evalDist_uniformSample, evalDist_uniformSample]
  rfl

theorem evalDist_sampleSecret : 𝒟[Concrete.sampleSecret] = 𝒟[$ᵗ ChainSecrets] := by
  apply evalDist_ext
  intro secret
  unfold Concrete.sampleSecret
  simp only [probOutput_uniformSample]

/-- The same independent parameter and secret sampler as the existing proof, with full derivation answers retained. -/
theorem evalDist_deriveParametersAndSecrets_eq_independent (seed : MasterSeed) :
    𝒟[(simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅] =
      𝒟[do
        let parameter ← Concrete.samplePublicParameter
        let secret ← Concrete.sampleSecret
        let parameterHigh ← $ᵗ Digest
        let secretHigh ← Concrete.sampleSecret
        pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)] := by
  rw [evalDist_deriveParametersAndSecrets]
  trans 𝒟[do
    let parameter ← $ᵗ Digest
    let secret ← $ᵗ ChainSecrets
    let parameterHigh ← $ᵗ Digest
    let secretHigh ← $ᵗ ChainSecrets
    pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)]
  · rw [evalDist_bind, evalDist_parameterOutput_from_halves, ← evalDist_bind]
    simp only [bind_assoc, pure_bind, truncate_from_halves]
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro parameter
    trans 𝒟[do
      let parameterHigh ← $ᵗ Digest
      let secret ← $ᵗ ChainSecrets
      let secretHigh ← $ᵗ ChainSecrets
      pure ((parameter, secret), programmedCache seed parameter secret parameterHigh secretHigh)]
    · apply OracleComp.DeferredSampling.evalDist_bind_congr_left
      intro parameterHigh
      rw [evalDist_bind, evalDist_chainOutputs_from_halves, ← evalDist_bind]
      simp only [bind_assoc, pure_bind, outputSecrets_from_halves, programmedCache]
    · exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  · rw [evalDist_bind, evalDist_bind, evalDist_samplePublicParameter]
    apply bind_congr
    intro parameter
    rw [evalDist_bind, evalDist_bind, evalDist_sampleSecret]
    apply bind_congr
    intro secret
    apply OracleComp.DeferredSampling.evalDist_bind_congr_left
    intro parameterHigh
    rw [evalDist_bind, evalDist_bind, evalDist_sampleSecret]

end XmssSecurity.Seeded
