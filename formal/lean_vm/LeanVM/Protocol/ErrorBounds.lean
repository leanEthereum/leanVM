/-
  LeanVM.Protocol.ErrorBounds

  The errors of `LeanVM.Protocol.Errors` bounded in bits: the arithmetic of the end statements.
-/

module

public import LeanVM.Protocol.Errors
public import Common.Linear

/-!
# The errors in bits

`LeanVM.Protocol.Errors` defines the errors the proofs establish; the end statements bound them
in bits. With `V = verifierQueries = 13261`:

* `soundnessRpm_le_statement`: for `Q ≤ 2^128`, `soundnessError Q` plus the transfer's
  `rpmError (Q + V · 2^32)` is at most `(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`, the bound of
  `KnowledgeSoundness`: the verifier's `V / 2^256` and the transfer's error are each at most
  `2^-125`, and `Q + V + 2 ≤ Q + 2^14`;
* `soundnessRpm_le_bits`: for `Q ≤ 2^120`, at most `(Q + 2^14) · 2^-124`;
* `soundnessRpm_le`: for `Q ≤ 2^64`, at most `2^-60`, as `soundnessError Q` alone
  (`soundnessError_le`);
* `rpmError_completenessPermCalls_le`: at a fuel of `2^33` nonces per proof of work, the
  completeness transfer's error is at most `2^-257`.
-/

namespace LeanVM

open scoped ENNReal

@[expose] public section

/-- `2^-k` as `2^(n - k) / 2^n`. -/
theorem inv_two_pow_eq_div (k n : ℕ) (h : k ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ k = ((2 ^ (n - k) : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ENNReal.div_eq_inv_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, pow_add, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

theorem verifierQueries_eq : verifierQueries = 13261 := rfl

theorem soundnessError_eq (Q : ℕ) :
    soundnessError Q = (((Q + 13261) * (2 ^ 131 + 5 * (Q + 13261)) + 13261 : ℕ) : ℝ≥0∞) /
      ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
  have h2 : ((2 ^ 256 : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 256 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  have hV : (verifierQueries : ℝ≥0∞) = ((13261 : ℕ) : ℝ≥0∞) := rfl
  rw [soundnessError, hV, verifierQueries_eq, inv_two_pow_eq_div 125 256 (by norm_num), ← h2,
    ENNReal.div_add_div_same, ← mul_div_assoc, ← Nat.cast_add, ← Nat.cast_mul,
    ENNReal.div_add_div_same, ← Nat.cast_add]

theorem rpmError_eq (q : ℕ) :
    rpmError q = ((q ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 508 : ℕ) : ℝ≥0∞) := by
  rw [rpmError, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]

theorem verifierPermCalls_eq : verifierPermCalls = 13261 * 2 ^ 32 := rfl

/-- **The random-oracle soundness error against `2^64` queries**: at most `2^-60`. -/
theorem soundnessError_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 60 := by
  rw [soundnessError_eq, inv_two_pow_eq_div 60 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  have hN : Q + 13261 ≤ 2 ^ 64 + 13261 := by omega
  calc (Q + 13261) * (2 ^ 131 + 5 * (Q + 13261)) + 13261
      ≤ (2 ^ 64 + 13261) * (2 ^ 131 + 5 * (2 ^ 64 + 13261)) + 13261 :=
        Nat.add_le_add_right (Nat.mul_le_mul hN (Nat.add_le_add_left
          (Nat.mul_le_mul_left 5 hN) _)) _
    _ ≤ 2 ^ (256 - 60) := by norm_num

/-- **The knowledge-soundness bound against `2^64` queries**: at most `2^-60`. -/
theorem soundnessRpm_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) :
    soundnessError Q + rpmError (Q + verifierPermCalls) ≤ (2 : ℝ≥0∞)⁻¹ ^ 60 := by
  have hc : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hc' : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [soundnessError_eq, rpmError_eq, inv_two_pow_eq_div 60 508 (by norm_num),
    ← ENNReal.mul_div_mul_right _ _ hc hc', ← Nat.cast_mul, ← Nat.cast_mul,
    ← pow_add, ENNReal.div_add_div_same, ← Nat.cast_add, show 256 + 252 = 508 from rfl]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [verifierPermCalls_eq]
  calc ((Q + 13261) * (2 ^ 131 + 5 * (Q + 13261)) + 13261) * 2 ^ 252 +
        (Q + 13261 * 2 ^ 32) ^ 2
      ≤ ((2 ^ 64 + 13261) * (2 ^ 131 + 5 * (2 ^ 64 + 13261)) + 13261) * 2 ^ 252 +
        (2 ^ 64 + 13261 * 2 ^ 32) ^ 2 := by gcongr
    _ ≤ 2 ^ 196 * 2 ^ 252 := by norm_num
    _ = 2 ^ (508 - 60) := by rw [← pow_add]

/-- **The knowledge-soundness bound in bits**: for `Q ≤ 2^120` queries, at most
`(Q + 2^14) · 2^-124`. -/
theorem soundnessRpm_le_bits {Q : ℕ} (hQ : Q ≤ 2 ^ 120) :
    soundnessError Q + rpmError (Q + verifierPermCalls) ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 124 := by
  have hc : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hc' : ((2 ^ 252 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hQ' : (Q + 2 ^ 14 : ℝ≥0∞) = ((Q + 2 ^ 14 : ℕ) : ℝ≥0∞) := by norm_cast
  rw [soundnessError_eq, rpmError_eq,
    ← ENNReal.mul_div_mul_right _ _ hc hc', ← Nat.cast_mul, ← Nat.cast_mul,
    ← pow_add, ENNReal.div_add_div_same, ← Nat.cast_add, show 256 + 252 = 508 from rfl,
    inv_two_pow_eq_div 124 508 (by norm_num), hQ', ← mul_div_assoc, ← Nat.cast_mul]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [verifierPermCalls_eq, show 508 - 124 = 384 from rfl]
  have h5 : 5 * (Q + 13261) ≤ 2 ^ 131 :=
    calc 5 * (Q + 13261) ≤ 5 * (2 ^ 120 + 13261) := by gcongr
      _ ≤ 2 ^ 131 := by norm_num
  have hP : Q + 13261 * 2 ^ 32 ≤ 2 ^ 121 :=
    calc Q + 13261 * 2 ^ 32 ≤ 2 ^ 120 + 13261 * 2 ^ 32 := by gcongr
      _ ≤ 2 ^ 121 := by norm_num
  calc ((Q + 13261) * (2 ^ 131 + 5 * (Q + 13261)) + 13261) * 2 ^ 252 + (Q + 13261 * 2 ^ 32) ^ 2
      ≤ ((Q + 13261) * (2 ^ 131 + 2 ^ 131) + 13261) * 2 ^ 252 + (2 ^ 121) ^ 2 := by gcongr
    _ ≤ ((Q + 13261) * (2 ^ 131 + 2 ^ 131) + 13261) * 2 ^ 252 + 2 ^ 252 :=
        Nat.add_le_add_left (by norm_num) _
    _ = ((Q + 13261) * (2 ^ 131 + 2 ^ 131) + 13261 + 1) * 2 ^ 252 := by ring
    _ ≤ (Q + 2 ^ 14) * 2 ^ 132 * 2 ^ 252 := by
        gcongr
        calc (Q + 13261) * (2 ^ 131 + 2 ^ 131) + 13261 + 1
            = Q * 2 ^ 132 + (13261 * 2 ^ 132 + 13262) := by ring
          _ ≤ Q * 2 ^ 132 + 2 ^ 14 * 2 ^ 132 := Nat.add_le_add_left (by norm_num) _
          _ = (Q + 2 ^ 14) * 2 ^ 132 := by ring
    _ = (Q + 2 ^ 14) * 2 ^ 384 := by rw [mul_assoc, ← pow_add]

/-- **The knowledge-soundness bound of the end statement**: for `Q ≤ 2^128` queries, at most
`(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`. The random-oracle error is
`A · 2^-125 + 5 A² · 2^-256 + V / 2^256` with `A = Q + V`; the verifier's `V / 2^256` and the
transfer's `(Q + verifierPermCalls)² / 2^508` are each at most `2^-125`, and `A + 2 ≤ Q + 2^14`. -/
theorem soundnessRpm_le_statement {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    soundnessError Q + rpmError (Q + verifierPermCalls) ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have hA2 : ((Q + verifierQueries : ℕ) : ℝ≥0∞) + 2 ≤ (Q + 2 ^ 14 : ℝ≥0∞) := by
    have h : Q + verifierQueries + 2 ≤ Q + 2 ^ 14 := by
      rw [Nat.add_assoc]
      exact Nat.add_le_add_left (by rw [verifierQueries_eq]; norm_num) Q
    exact_mod_cast h
  have hV : (verifierQueries : ℝ≥0∞) / 2 ^ 256 ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 :=
    calc (verifierQueries : ℝ≥0∞) / 2 ^ 256 = (verifierQueries : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
          rw [div_eq_mul_inv, ENNReal.inv_pow]
      _ ≤ (2 : ℝ≥0∞) ^ 131 * (2 : ℝ≥0∞)⁻¹ ^ (131 + 125) := by
          gcongr
          exact_mod_cast (show verifierQueries ≤ 2 ^ 131 by rw [verifierQueries_eq]; norm_num)
      _ = (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.two_pow_mul_inv_pow 131 125
  have hq : Q + verifierPermCalls ≤ 2 ^ 129 :=
    calc Q + verifierPermCalls ≤ 2 ^ 128 + verifierPermCalls := Nat.add_le_add_right hQ _
      _ ≤ 2 ^ 129 := by rw [verifierPermCalls_eq]; norm_num
  have hR : rpmError (Q + verifierPermCalls) ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 :=
    calc rpmError (Q + verifierPermCalls)
        ≤ ((Q + verifierPermCalls : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 379 :=
          Common.sq_div_le_mul_inv_pow (k := 129) 379 hq
      _ ≤ (2 : ℝ≥0∞) ^ 129 * (2 : ℝ≥0∞)⁻¹ ^ (129 + 250) := by
          gcongr
          exact_mod_cast hq
      _ = (2 : ℝ≥0∞)⁻¹ ^ 250 := Common.two_pow_mul_inv_pow 129 250
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.inv_two_pow_le_of_le (by norm_num)
  have h5 : ((5 * (Q + verifierQueries) : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
    rw [Nat.cast_mul, div_eq_mul_inv, ENNReal.inv_pow, Nat.cast_ofNat]
  unfold soundnessError
  rw [h5]
  calc ((Q + verifierQueries : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256) +
        (verifierQueries : ℝ≥0∞) / 2 ^ 256 + rpmError (Q + verifierPermCalls)
      = ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          ((verifierQueries : ℝ≥0∞) / 2 ^ 256 + rpmError (Q + verifierPermCalls)) := by ring
    _ ≤ ((Q + verifierQueries : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          ((2 : ℝ≥0∞)⁻¹ ^ 125 + (2 : ℝ≥0∞)⁻¹ ^ 125) := add_le_add le_rfl (add_le_add hV hR)
    _ = (((Q + verifierQueries : ℕ) : ℝ≥0∞) + 2) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + verifierQueries : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by ring
    _ ≤ (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
        have hA : ((Q + verifierQueries : ℕ) : ℝ≥0∞) ≤ (Q + 2 ^ 14 : ℝ≥0∞) := le_self_add.trans hA2
        gcongr

/-- The completeness transfer's error at a fuel of `2^33` nonces per proof of work. -/
theorem rpmError_completenessPermCalls_le :
    rpmError (completenessPermCalls (2 ^ 33)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 := by
  rw [rpmError_eq, inv_two_pow_eq_div 257 508 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [completenessPermCalls, completenessQueries]
  norm_num

end

end LeanVM
