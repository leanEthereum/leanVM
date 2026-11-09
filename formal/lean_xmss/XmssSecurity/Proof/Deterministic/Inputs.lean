module

public import XmssSecurity.Proof.EvalDistEq
public import XmssSecurity.Proof.Seeded.KeyDerivation

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

set_option backward.isDefEq.respectTransparency false

/-- Every seed-derived input puts the complete seed in bytes 32 through 63. -/
def DerivationSeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  (input.drop 32).take 32 = bytesLE 32 seed

theorem derivationSeedHit_unique {input : HashInput} {left right : MasterSeed}
    (hl : DerivationSeedHit input left) (hr : DerivationSeedHit input right) : left = right :=
  bytesLE_injective 32 (hl.symm.trans hr)

theorem probEvent_derivationSeedHit_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(DerivationSeedHit input) x] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hexists : ∃ seed, DerivationSeedHit input seed
  · obtain ⟨seed, hseed⟩ := hexists
    have hevent : DerivationSeedHit input = fun other => other = seed := by
      funext other
      exact propext ⟨fun h => derivationSeedHit_unique h hseed, fun h => h ▸ hseed⟩
    rw [hevent]
    simp [sampleMasterSeed, MasterSeed, SampleableType.prEvent_uniformSample_eq_singleton]
  · have hempty : DerivationSeedHit input = fun _ => False := by
      funext seed
      exact propext ⟨fun h => hexists ⟨seed, h⟩, False.elim⟩
    simp [hempty]

end XmssSecurity
