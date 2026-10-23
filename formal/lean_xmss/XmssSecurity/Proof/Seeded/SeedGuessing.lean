import XmssSecurity.Proof.Deterministic.Inputs

open OracleComp OracleSpec ENNReal

namespace XmssSecurity

abbrev SeedHit := DerivationSeedHit

theorem probEvent_seedHit_le (input : HashInput) :
    Pr{let x ← sampleMasterSeed}[(SeedHit input) x] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
  probEvent_derivationSeedHit_le input

/-- `hit input seed`, an input naming a seed, holds for at most one uniform seed in `2^256`. -/
def GuessBound (hit : HashInput → MasterSeed → Prop) : Prop :=
  ∀ input, Pr{let x ← sampleMasterSeed}[(hit input) x] ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞)

theorem guessBound_seedHit : GuessBound SeedHit := probEvent_seedHit_le

def SeedHitLog (hit : HashInput → MasterSeed → Prop) (inputs : List HashInput) (seed : MasterSeed) :
    Prop :=
  ∃ input ∈ inputs, hit input seed

/-- A list chosen independently of the seed contributes at most one 256-bit guess per input. -/
theorem probEvent_seedHitLog_le {hit : HashInput → MasterSeed → Prop} (hhit : GuessBound hit)
    (inputs : List HashInput) :
    Pr{let x ← sampleMasterSeed}[(SeedHitLog hit inputs) x] ≤ inputs.length / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  induction inputs with
  | nil =>
      have hempty : SeedHitLog hit [] = fun _ => False := by
        funext seed
        simp [SeedHitLog]
      simp [hempty]
  | cons input inputs ih =>
      have hevent : SeedHitLog hit (input :: inputs) = fun seed =>
          hit input seed ∨ SeedHitLog hit inputs seed := by
        funext seed
        simp [SeedHitLog]
      rw [hevent]
      calc
        _ ≤ Pr{let x ← sampleMasterSeed}[(hit input) x] + Pr{let x ← sampleMasterSeed}[(SeedHitLog hit inputs) x] :=
          prEvent_or_le _ _ _
        _ ≤ 1 / ((2 ^ 256 : Nat) : ℝ≥0∞) + inputs.length / ((2 ^ 256 : Nat) : ℝ≥0∞) :=
          add_le_add (hhit input) ih
        _ = _ := by simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]

end XmssSecurity
