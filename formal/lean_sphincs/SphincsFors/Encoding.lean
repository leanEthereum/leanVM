import SphincsFors.Code
import SphincsFors.Counter
import SphincsFors.Decay
import SphincsFors.Uniform

/-!
# What one encoding trial rejects

A trial keeps the low `128` bits of a uniform answer, and that truncation is uniform on digests
(`probEvent_uniform_truncateHash_mem`). So one trial accepts exactly as often as a uniform digest
decodes, which by `Code.lean` is at least `2 ^ 118` times in `2 ^ 128`.
-/

open Finset ENNReal OracleComp OracleSpec

namespace SphincsFors.Completeness

open TargetSum

/-- The accepted share is the code's size over the digest space. -/
theorem probEvent_accept :
    Pr{let u ← ($ᵗ HashOutput : ProbComp HashOutput)}[(decodeDigest (truncateHash u)).isSome]
      = ((univ.filter fun d : Digest => (decodeDigest d).isSome).card : ℝ≥0∞)
          / (Fintype.card Digest : ℝ≥0∞) := by
  rw [← SphincsFors.probEvent_uniform_truncateHash_mem
    (univ.filter fun d : Digest => (decodeDigest d).isSome)]
  exact prEvent_congr _ _ _ fun u => by simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- One trial rejects at most `1 - 2 ^ -10` of the answers. -/
theorem failMass_encoding_add_le :
    failMass (fun out => decodeDigest (truncateHash out)) + ((2 : ℝ≥0∞) ^ 10)⁻¹ ≤ 1 := by
  obtain ⟨accepted, haccepted⟩ :
      ∃ n, (univ.filter fun d : Digest => (decodeDigest d).isSome).card = n := ⟨_, rfl⟩
  have hnat : (2 : Nat) ^ 118 ≤ accepted := haccepted ▸ two_pow_le_card_accepting
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
  have hshare : ((2 : ℝ≥0∞) ^ 10)⁻¹ ≤ (accepted : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)),
      show (2 : ℝ≥0∞) ^ 128 = 2 ^ 10 * 2 ^ 118 by rw [← pow_add],
      ← mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]
    exact_mod_cast hnat
  exact (add_le_add le_rfl hshare).trans_eq ((add_comm _ _).trans hcompl)

/-- All 2^32 WOTS+C encoding attempts fail with probability at most 2^(-2^22),
provided these counter inputs are initially fresh. -/
theorem encoding_exhaustion_bound (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (seed : MasterSeed) (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : ∀ c, c < encodingAttemptLimit →
      cache (encodeInput parameter lay tree leaf message c) = none) :
    Pr{let r ← ((simulateQ randomOracle
        (Seeded.otsSign parameter lay tree leaf seed message
          : OracleComp HashSpec (Option (Counter × (ChainIndex → Digest))))).run cache)}[r.1 = none]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22) := by
  apply (probEvent_otsSign parameter lay tree leaf seed message cache hfresh).trans
  have hhalf := pow_le_half_ennreal (2 ^ 10) (by positivity)
    (failMass (fun out => TargetSum.decodeDigest (truncateHash out)))
    (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using failMass_encoding_add_le)
  rw [show encodingAttemptLimit = 2 ^ 10 * 2 ^ 22 by decide, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hhalf _

end SphincsFors.Completeness
