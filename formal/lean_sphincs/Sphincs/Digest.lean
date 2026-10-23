import Sphincs.Search
import Sphincs.Decay
import Sphincs.Bytes
import Sphincs.Landing

/-!
Randomizer grinding for the candidate: the digest input of a trial, the share of fresh answers the
landing test rejects, and the per-trial failure share `digestFactor`, which also accounts for
repeated randomizers, with its numerical bound after `2^32` trials. Adapted from leanVM b7a107256.
-/

open OracleComp OracleSpec ENNReal Finset

namespace Sphincs.Completeness

variable [Params]

open Concrete

/-- The input a digest trial hashes to test its randomizer. -/
abbrev msgInput (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    HashInput :=
  tweakableHashInput secretKey.parameter .message
    (messageDigestPayload secretKey.root message randomness)

omit [Params] in
theorem msgInput_inj (secretKey : Seeded.SecretKey) (message : Message)
    {randomness randomness' : Randomness}
    (h : msgInput secretKey message randomness = msgInput secretKey message randomness') :
    randomness = randomness' := by
  simp only [msgInput, tweakableHashInput, messageDigestPayload, List.append_assoc] at h
  exact Sphincs.bytesLE_injective (List.append_cancel_left (List.append_cancel_left
    (List.append_cancel_left h)))

omit [Params] in
theorem cached_run (input : HashInput) (cache : QueryCache HashSpec) (answer : HashOutput)
    (hcached : cache input = some answer) :
    (randomOracle (spec := HashSpec) input).run cache = pure (answer, cache) :=
  QueryImpl.withCaching_run_some _ hcached

/-- The share of fresh answers the admissibility test rejects. -/
noncomputable def digestReject (parameter : PublicParameter) : ℝ≥0∞ :=
  Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[¬ Landed parameter (blockIndex u)]

theorem digestReject_add (parameter : PublicParameter) :
    digestReject parameter + ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ = 1 := by
  have h : Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[Landed parameter (blockIndex u)]
      + Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[¬ Landed parameter (blockIndex u)] = 1 := by
    rw [OracleComp.prEvent_not_eq_one_sub]
    exact add_tsub_cancel_of_le (prEvent_le_one _)
  rw [fresh_landing_probability_inv] at h
  rw [add_comm]
  exact h

theorem digestReject_le_one (parameter : PublicParameter) : digestReject parameter ≤ 1 := (prEvent_le_one _)

omit [Params] in
/-- Averaging a two-valued function over one uniform answer. -/
theorem tsum_uniform_ite (P : HashOutput → Prop) [DecidablePred P] (x y : ℝ≥0∞) :
    ∑' u : HashOutput, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ * (if P u then x else y)
      = x * Pr{let x ← ($ᵗ HashOutput : ProbComp HashOutput)}[P x]
        + y * Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[¬ P u] := by
  rw [OracleComp.prEvent_eq_tsum_ite ($ᵗ HashOutput : ProbComp HashOutput) P,
    OracleComp.prEvent_eq_tsum_ite ($ᵗ HashOutput : ProbComp HashOutput) (fun u => ¬ P u),
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine tsum_congr fun u => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  by_cases hu : P u <;> simp [hu, mul_comm]

/-- One trial's failure share. -/
noncomputable def digestFactor (parameter : PublicParameter) : ℝ≥0∞ := digestReject parameter + (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128

/-- Even after accounting for repeated randomizers, each trial has at least half the fresh
landing probability available. -/
theorem digestFactor_room (parameter : PublicParameter) :
    digestFactor parameter +
      ((2 ^ (totalHeight - subtreeHeight + 1) : Nat) : ℝ≥0∞)⁻¹ ≤ 1 := by
  have hcoll : (2 : ℝ≥0∞) ^ 32 / (2 : ℝ≥0∞) ^ 128 = (2⁻¹ : ℝ≥0∞) ^ 96 :=
    two_pow_div_two_pow 32 96
  have hcast (k : Nat) : ((2 ^ k : Nat) : ℝ≥0∞)⁻¹ = (2⁻¹ : ℝ≥0∞) ^ k := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
  have hsmall : totalHeight - subtreeHeight + 1 ≤ 96 := by unfold totalHeight; omega
  rw [digestFactor, hcoll, hcast, add_assoc, ← digestReject_add parameter, hcast]
  apply add_le_add le_rfl
  calc
    (2⁻¹ : ℝ≥0∞) ^ 96 + (2⁻¹ : ℝ≥0∞) ^ (totalHeight - subtreeHeight + 1)
      ≤ (2⁻¹ : ℝ≥0∞) ^ (totalHeight - subtreeHeight + 1) +
        (2⁻¹ : ℝ≥0∞) ^ (totalHeight - subtreeHeight + 1) :=
          add_le_add (inv_two_pow_anti hsmall) le_rfl
    _ = (2⁻¹ : ℝ≥0∞) ^ (totalHeight - subtreeHeight) := inv_two_pow_succ_add _

/-- Numerical grinding bound: `2^32` trials leave at most `2^(-2^(b+5))` failure mass. -/
theorem digestFactor_pow_bound (parameter : PublicParameter) :
    digestFactor parameter ^ digestAttemptLimit ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) := by
  have hhalf := pow_le_half_ennreal (2 ^ (totalHeight - subtreeHeight + 1))
    (Nat.two_pow_pos _) (digestFactor parameter) (digestFactor_room parameter)
  have hb : subtreeHeight ≤ 26 := Params.subtreeHeight_le
  have hsplit : digestAttemptLimit =
      2 ^ (totalHeight - subtreeHeight + 1) * 2 ^ (subtreeHeight + 5) := by
    rw [digestAttemptLimit, ← pow_add]
    congr 1
    change 32 = 26 - subtreeHeight + 1 + (subtreeHeight + 5)
    omega
  rw [hsplit, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hhalf _

end Sphincs.Completeness
