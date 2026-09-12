import SphincsSecurity.Proof.Seeded.KeyDerivation

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

def SeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  ∃ parameter domain, keygenHashInput parameter domain seed = input

theorem probEvent_seedHit_le (input : HashInput) :
    Pr[SeedHit input | sampleMasterSeed] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  by_cases hexists : ∃ seed, SeedHit input seed
  · obtain ⟨seed, hseed⟩ := hexists
    have hevent : SeedHit input = fun other => other = seed := by
      funext other
      apply propext
      exact ⟨fun h => keygenHashInput_seed_unique input h hseed, fun h => h ▸ hseed⟩
    rw [hevent]
    simp [sampleMasterSeed, MasterSeed]
  · have hempty : SeedHit input = fun _ => False := by
      funext seed
      exact propext ⟨fun h => hexists ⟨seed, h⟩, False.elim⟩
    simp [hempty]

def SeedHitLog (inputs : List HashInput) (seed : MasterSeed) : Prop :=
  ∃ input ∈ inputs, SeedHit input seed

/-- A list chosen independently of the seed contributes at most one 256-bit guess per input. -/
theorem probEvent_seedHitLog_le (inputs : List HashInput) :
    Pr[SeedHitLog inputs | sampleMasterSeed] ≤ inputs.length / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  induction inputs with
  | nil => simp [SeedHitLog]
  | cons input inputs ih =>
      have hevent : SeedHitLog (input :: inputs) = fun seed =>
          SeedHit input seed ∨ SeedHitLog inputs seed := by
        funext seed
        simp [SeedHitLog]
      rw [hevent]
      calc
        _ ≤ Pr[SeedHit input | sampleMasterSeed] + Pr[SeedHitLog inputs | sampleMasterSeed] :=
          probEvent_or_le _ _ _
        _ ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) + inputs.length / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
          add_le_add (probEvent_seedHit_le input) ih
        _ = _ := by simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]

end SphincsSecurity
