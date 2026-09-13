import XmssSecurity.Proof.Seeded.KeyDerivation

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option backward.isDefEq.respectTransparency false

theorem randomizerHashInput_injective {p₁ p₂ : PublicParameter} {s₁ s₂ : MasterSeed}
    {e₁ e₂ : Epoch} {m₁ m₂ : Message} {a₁ a₂ : BitVec 32}
    (h : randomizerHashInput p₁ s₁ e₁ m₁ a₁ = randomizerHashInput p₂ s₂ e₂ m₂ a₂) :
    p₁ = p₂ ∧ s₁ = s₂ ∧ e₁ = e₂ ∧ m₁ = m₂ ∧ a₁ = a₂ := by
  unfold randomizerHashInput at h
  obtain ⟨hprefix, hm⟩ := List.append_inj' h (by simp [length_bytesLE])
  obtain ⟨hprefix, hs⟩ := List.append_inj' hprefix (by simp [length_bytesLE])
  obtain ⟨htweak, hp⟩ := List.append_inj' hprefix (by simp [length_bytesLE])
  have hf := fieldBytes_injective htweak
  have he : e₁ = e₂ := by
    apply Fin.ext
    have h := congrArg BitVec.toNat (congrArg TweakFields.epoch hf)
    simpa [Epoch, lifetime, BitVec.toNat_ofNat, Nat.mod_eq_of_lt e₁.isLt, Nat.mod_eq_of_lt e₂.isLt] using h
  exact ⟨bytesLE_injective 16 hp, bytesLE_injective 32 hs, he, bytesLE_injective 32 hm,
    congrArg TweakFields.position hf⟩

theorem randomizerHashInput_ne_keygenHashInput (p₁ p₂ : PublicParameter)
    (s₁ s₂ : MasterSeed) (epoch : Epoch) (message : Message) (trial : BitVec 32) (domain : KeygenDomain) :
    randomizerHashInput p₁ s₁ epoch message trial ≠ keygenHashInput p₂ domain s₂ := by
  intro h
  have := congrArg List.length h
  simp [randomizerHashInput, keygenHashInput, fieldBytes, length_bytesLE] at this

theorem randomizerHashInput_ne_tweakableHashInput (p₁ p₂ : PublicParameter)
    (seed : MasterSeed) (epoch : Epoch) (message : Message) (trial : BitVec 32)
    (domain : HashDomain) (payload : HashInput) :
    randomizerHashInput p₁ seed epoch message trial ≠ tweakableHashInput p₂ domain payload := by
  intro h
  simp only [randomizerHashInput, tweakableHashInput, tweakBytes, List.append_assoc] at h
  obtain ⟨htweak, _⟩ := List.append_inj h (by simp [fieldBytes, length_bytesLE])
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  cases domain <;> simp [hashDomainFields, tweakFields] at htag

/-- Every seed-derived input puts the complete seed in bytes 32 through 63. -/
def DerivationSeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (input.drop 32).take 32 = bytesLE 32 seed

theorem derivationSeedHit_keygen (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    DerivationSeedHit (keygenHashInput parameter domain seed) seed := by
  simp [DerivationSeedHit, keygenHashInput, fieldBytes, bytesLE]

theorem derivationSeedHit_randomizer (parameter : PublicParameter) (seed : MasterSeed)
    (epoch : Epoch) (message : Message) (trial : BitVec 32) :
    DerivationSeedHit (randomizerHashInput parameter seed epoch message trial) seed := by
  simp [DerivationSeedHit, randomizerHashInput, fieldBytes, bytesLE]

theorem derivationSeedHit_unique {input : HashInput} {left right : MasterSeed}
    (hl : DerivationSeedHit input left) (hr : DerivationSeedHit input right) : left = right :=
  bytesLE_injective 32 (hl.symm.trans hr)

theorem probEvent_derivationSeedHit_le (input : HashInput) :
    Pr[DerivationSeedHit input | sampleMasterSeed] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hexists : ∃ seed, DerivationSeedHit input seed
  · obtain ⟨seed, hseed⟩ := hexists
    have hevent : DerivationSeedHit input = fun other => other = seed := by
      funext other
      exact propext ⟨fun h => derivationSeedHit_unique h hseed, fun h => h ▸ hseed⟩
    rw [hevent]
    simp [sampleMasterSeed, MasterSeed]
  · have hempty : DerivationSeedHit input = fun _ => False := by
      funext seed
      exact propext ⟨fun h => hexists ⟨seed, h⟩, False.elim⟩
    simp [hempty]

end XmssSecurity
