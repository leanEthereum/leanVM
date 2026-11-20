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
in bits (knowledge soundness's in `LeanVM.Protocol.LeanVMSoundAS`, `soundnessRpmAS_le_statement`).
With `V = verifierQueries = 13708`:

* `rpmError_completenessPermCalls_le`: at a fuel of `2^35` nonces per proof of work, the
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

theorem verifierQueries_eq : verifierQueries = 13708 := rfl

theorem rpmError_eq (q : ℕ) :
    rpmError q = ((q ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 508 : ℕ) : ℝ≥0∞) := by
  rw [rpmError, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]

theorem verifierPermCalls_eq : verifierPermCalls = 13708 * 2 ^ 30 := rfl

/-- The completeness transfer's error at a fuel of `2^35` nonces per proof of work. -/
theorem rpmError_completenessPermCalls_le :
    rpmError (completenessPermCalls (2 ^ 35)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 := by
  rw [rpmError_eq, inv_two_pow_eq_div 257 508 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  rw [completenessPermCalls, completenessQueries]
  norm_num

end

end LeanVM
