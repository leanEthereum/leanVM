module

public import FORS.Scheme.Code
public import FORS.Scheme.Counter
public import FORS.Scheme.Uniform

@[expose] public section

/-!
# What one encoding trial rejects

A trial keeps the low `128` bits of a uniform answer, and that truncation is uniform on digests
(`probEvent_uniform_truncateHash_mem`). So one trial accepts exactly as often as a uniform digest
decodes, which by `Scheme/Code.lean` is at least `2 ^ 114` times in `2 ^ 128`.
-/

open Finset ENNReal OracleComp OracleSpec

namespace FORS.Completeness

variable [Params]

open TargetSum

/-- The accepted share is the code's size over the digest space. -/
theorem probEvent_accept :
    Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[(decodeDigest (truncateHash u)).isSome]
      = ((univ.filter fun d : Digest => (decodeDigest d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞) := by
  rw [← FORS.probEvent_uniform_truncateHash_mem
    (univ.filter fun d : Digest => (decodeDigest d).isSome)]
  exact prEvent_congr _ _ _ fun u => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- One trial rejects at most `1 - 2 ^ -14` of the answers. -/
theorem failMass_encoding_add_le :
    failMass (fun out => decodeDigest (truncateHash out)) + ((2 : ℝ≥0∞) ^ 14)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (decodeDigest d).isSome).card = n := ⟨_, rfl⟩
  have hnat : (2 : Nat) ^ 114 ≤ accepted := haccepted ▸ two_pow_le_card_accepting
  have hcard : (Fintype.card Digest : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 128 := by
    rw [show Fintype.card Digest = 2 ^ 128 by simp [digestBits], Nat.cast_pow, Nat.cast_ofNat]
  have hcompl : Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[(decodeDigest (truncateHash u)).isSome]
      + Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[¬ (decodeDigest (truncateHash u)).isSome = true]
      = 1 := by
    rw [OracleComp.prEvent_not_eq_one_sub]
    exact add_tsub_cancel_of_le (prEvent_le_one _)
  have hreject : Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[¬ (decodeDigest (truncateHash u)).isSome = true]
      = failMass (fun out => decodeDigest (truncateHash out)) := by
    rw [failMass_eq_probEvent]
    exact prEvent_congr _ _ _ fun u => by cases decodeDigest (truncateHash u) <;> simp
  rw [hreject, probEvent_accept, hcard, haccepted] at hcompl
  have hshare : ((2 : ℝ≥0∞) ^ 14)⁻¹ ≤ (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)),
      show (2 : ℝ≥0∞) ^ 128 = 2 ^ 14 * 2 ^ 114 by rw [← pow_add],
      ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    exact_mod_cast hnat
  exact (add_le_add le_rfl hshare).trans_eq ((add_comm _ _).trans hcompl)

end FORS.Completeness
