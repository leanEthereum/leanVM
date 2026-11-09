module

public import XmssSecurity.Proof.HashInputLemmas
public import XmssSecurity.Proof.StatementLemmas
public import XmssSecurity.Proof.Execution
public import XmssSecurity.Proof.RandomOracle

@[expose] public section

open OracleComp ENNReal

namespace XmssSecurity.Rom

/-- A uniform 256-bit oracle output has any fixed 128-bit truncation with probability exactly `2^-128`. -/
theorem uniform_truncate_probability (target : Digest) :
    Pr{let output ← $ᵗ HashOutput}[truncateHash output = target] =
      ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
  rw [SampleableType.prEvent_uniformSample]
  change ((matchingOutputs target).card : ℝ≥0∞) /
      (Fintype.card HashOutput : ℝ≥0∞) = _
  rw [card_matchingOutputs, card_hashOutput, hashOutputBits_eq, Nat.pow_add,
    Nat.cast_mul, div_eq_mul_inv]
  have hzero : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ 0 := by positivity
  have htop : ((2 ^ digestBits : Nat) : ℝ≥0∞) ≠ ∞ := by simp
  rw [ENNReal.mul_inv (Or.inl hzero) (Or.inl htop)]
  calc
    ((2 ^ digestBits : Nat) : ℝ≥0∞) *
        (((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ *
          ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) =
      (((2 ^ digestBits : Nat) : ℝ≥0∞) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹) *
        ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by ac_rfl
    _ = ((2 ^ digestBits : Nat) : ℝ≥0∞)⁻¹ := by
      rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

open OracleSpec

noncomputable local instance : UniformAnswerMeasure HashSpec :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-- Each fresh query may select its own target digest without adding an index-set loss. -/
def AdaptiveFreshDigestCollisionWith (initialCache finalCache : QueryCache HashSpec)
    (targetInput : HashInput → HashInput) : Prop :=
  ∃ input output targetOutput,
    finalCache input = some output ∧ initialCache input = none ∧
      initialCache (targetInput input) = some targetOutput ∧
      Concrete.CacheView.digestAt finalCache input =
        Concrete.CacheView.digestAt finalCache (targetInput input)

end XmssSecurity.Rom
