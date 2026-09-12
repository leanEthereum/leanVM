import SphincsSecurity.Proof.Seeded.AlgorithmErasure
import SphincsSecurity.Proof.Fts.FewTimeUniform

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512

abbrev OtsSecrets := Layer → TreeIndex → LeafIndex → ChainIndex → Digest
abbrev FtsSecrets := Index → FtsTree → FtsLeaf → Digest
abbrev Secrets := OtsSecrets × FtsSecrets

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType
noncomputable local instance : SampleableType OtsSecrets := Concrete.otsSecretsSampleableType
noncomputable local instance : SampleableType FtsSecrets := Concrete.ftsSecretsSampleableType
noncomputable opaque secretsSampleableType : SampleableType Secrets := SampleableType.ofFintype Secrets
noncomputable local instance : SampleableType Secrets := secretsSampleableType
noncomputable opaque secretHalvesSampleableType : SampleableType (Secrets × Secrets) :=
  SampleableType.ofFintype (Secrets × Secrets)
noncomputable local instance : SampleableType (Secrets × Secrets) := secretHalvesSampleableType

def flattenSecrets (secrets : Secrets) : SecretValues
  | .inl (lay, tree, leaf, chain) => secrets.1 lay tree leaf chain
  | .inr (index, tree, leaf) => secrets.2 index tree leaf

noncomputable def outputHalves : HashOutput ≃ (Digest × Digest) :=
  splitHashOutputEquiv digestBits (by decide)

theorem outputHalves_low (output : HashOutput) : (outputHalves output).1 = truncateHash output := rfl

noncomputable def secretHalves : SecretOutputs ≃ (Secrets × Secrets) where
  toFun outputs := ((tableOts outputs, tableFts outputs),
    ((fun lay tree leaf chain => (outputHalves (outputs (.inl (lay, tree, leaf, chain)))).2),
      fun index tree leaf => (outputHalves (outputs (.inr (index, tree, leaf)))).2))
  invFun halves := fun position => outputHalves.symm (flattenSecrets halves.1 position, flattenSecrets halves.2 position)
  left_inv outputs := by
    funext position
    cases position <;> exact outputHalves.symm_apply_apply (outputs _)
  right_inv halves := by
    rcases halves with ⟨⟨ots, fts⟩, ⟨otsHigh, ftsHigh⟩⟩
    apply Prod.ext <;> apply Prod.ext
    · funext lay tree leaf chain
      exact congrArg Prod.fst (outputHalves.apply_symm_apply (ots lay tree leaf chain, otsHigh lay tree leaf chain))
    · funext index tree leaf
      exact congrArg Prod.fst (outputHalves.apply_symm_apply (fts index tree leaf, ftsHigh index tree leaf))
    · funext lay tree leaf chain
      exact congrArg Prod.snd (outputHalves.apply_symm_apply (ots lay tree leaf chain, otsHigh lay tree leaf chain))
    · funext index tree leaf
      exact congrArg Prod.snd (outputHalves.apply_symm_apply (fts index tree leaf, ftsHigh index tree leaf))

theorem tableOts_from_halves (low high : Secrets) : tableOts (secretHalves.symm (low, high)) = low.1 :=
  congrArg (fun halves => halves.1.1) (secretHalves.apply_symm_apply (low, high))

theorem tableFts_from_halves (low high : Secrets) : tableFts (secretHalves.symm (low, high)) = low.2 :=
  congrArg (fun halves => halves.1.2) (secretHalves.apply_symm_apply (low, high))

theorem truncate_from_halves (low high : Digest) : truncateHash (outputHalves.symm (low, high)) = low :=
  congrArg Prod.fst (outputHalves.apply_symm_apply (low, high))

noncomputable def sampleSecrets : ProbComp Secrets := do
  let ots ← Concrete.sampleOtsSecrets
  let fts ← Concrete.sampleFtsSecrets
  pure (ots, fts)

theorem evalDist_sampleSecrets : 𝒟[sampleSecrets] = 𝒟[$ᵗ Secrets] := by
  unfold sampleSecrets Concrete.sampleOtsSecrets Concrete.sampleFtsSecrets
  exact evalDist_independent_uniform_pair (α := OtsSecrets) (β := FtsSecrets)

theorem evalDist_secretOutputs_from_halves :
    𝒟[sampleSecretOutputs] = 𝒟[do
      let low ← sampleSecrets
      let high ← sampleSecrets
      pure (secretHalves.symm (low, high))] := by
  calc
    _ = 𝒟[secretHalves.symm <$> ($ᵗ (Secrets × Secrets))] :=
      (evalDist_map_bijective_uniform_cross (α := Secrets × Secrets) (β := SecretOutputs) secretHalves.symm secretHalves.symm.bijective).symm
    _ = 𝒟[secretHalves.symm <$> (do
        let low ← $ᵗ Secrets
        let high ← $ᵗ Secrets
        pure (low, high))] := by
      rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      rw [evalDist_bind, evalDist_bind, evalDist_sampleSecrets]
      apply bind_congr
      intro low
      rw [evalDist_bind, evalDist_bind, evalDist_sampleSecrets]

theorem evalDist_sampleParameter : 𝒟[Concrete.sampleParameter] = 𝒟[$ᵗ Digest] := by
  unfold Concrete.sampleParameter
  rw [evalDist_uniformSample, evalDist_uniformSample]
  rfl

theorem evalDist_parameterOutput_from_halves :
    𝒟[$ᵗ HashOutput] = 𝒟[do
      let low ← Concrete.sampleParameter
      let high ← $ᵗ Digest
      pure (outputHalves.symm (low, high))] := by
  calc
    _ = 𝒟[outputHalves.symm <$> ($ᵗ (Digest × Digest))] :=
      (evalDist_map_bijective_uniform_cross (α := Digest × Digest) (β := HashOutput) outputHalves.symm outputHalves.symm.bijective).symm
    _ = 𝒟[outputHalves.symm <$> (do
        let low ← $ᵗ Digest
        let high ← $ᵗ Digest
        pure (low, high))] := by
      rw [evalDist_map, evalDist_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      rw [evalDist_bind, evalDist_bind, evalDist_sampleParameter]
      rfl

noncomputable def programmedCache (seed : MasterSeed) (parameter : PublicParameter) (secret : Secrets)
    (parameterHigh : Digest) (secretHigh : Secrets) : QueryCache HashSpec :=
  derivationCache seed (outputHalves.symm (parameter, parameterHigh)) (secretHalves.symm (secret, secretHigh))

end SphincsSecurity.Seeded
