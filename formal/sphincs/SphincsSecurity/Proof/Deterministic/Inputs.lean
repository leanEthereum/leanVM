import SphincsSecurity.Proof.Seeded.KeyDerivation

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

set_option backward.isDefEq.respectTransparency false

theorem randomizerHashInput_injective {p₁ p₂ : PublicParameter} {s₁ s₂ : MasterSeed}
    {m₁ m₂ : Message} {a₁ a₂ : BitVec 32}
    (h : randomizerHashInput p₁ s₁ m₁ a₁ = randomizerHashInput p₂ s₂ m₂ a₂) :
    p₁ = p₂ ∧ s₁ = s₂ ∧ m₁ = m₂ ∧ a₁ = a₂ := by
  unfold randomizerHashInput at h
  obtain ⟨hprefix, hm⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hprefix, hs⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  obtain ⟨htweak, hp⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hp, bytesLE_injective hs, bytesLE_injective hm,
    congrArg TweakFields.position (fieldBytes_injective htweak)⟩

theorem randomizerHashInput_ne_keygenHashInput (p₁ p₂ : PublicParameter)
    (s₁ s₂ : MasterSeed) (message : Message) (trial : BitVec 32) (domain : KeygenDomain) :
    randomizerHashInput p₁ s₁ message trial ≠ keygenHashInput p₂ domain s₂ := by
  intro h
  have := congrArg List.length h
  simp [randomizerHashInput, keygenHashInput, fieldBytes, bytesLE_length] at this

theorem randomizerHashInput_ne_tweakableHashInput (p₁ p₂ : PublicParameter)
    (seed : MasterSeed) (message : Message) (trial : BitVec 32)
    (domain : HashDomain) (payload : HashInput) :
    randomizerHashInput p₁ seed message trial ≠ tweakableHashInput p₂ domain payload := by
  intro h
  simp only [randomizerHashInput, tweakableHashInput, tweakBytes, List.append_assoc] at h
  obtain ⟨htweak, _⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  have htag := congrArg TweakFields.tag (fieldBytes_injective htweak)
  cases domain <;> simp [hashDomainFields, tweakFields] at htag

/-- Every seed-derived input puts the complete seed in bytes 32 through 63. -/
def DerivationSeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (input.drop 32).take 32 = bytesLE 32 seed

theorem derivationSeedHit_keygen (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    DerivationSeedHit (keygenHashInput parameter domain seed) seed := by
  simp [DerivationSeedHit, keygenHashInput, fieldBytes, bytesLE]

theorem derivationSeedHit_randomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) :
    DerivationSeedHit (randomizerHashInput parameter seed message trial) seed := by
  simp [DerivationSeedHit, randomizerHashInput, fieldBytes, bytesLE]

theorem derivationSeedHit_unique {input : HashInput} {left right : MasterSeed}
    (hl : DerivationSeedHit input left) (hr : DerivationSeedHit input right) : left = right :=
  bytesLE_injective (hl.symm.trans hr)

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

end SphincsSecurity
