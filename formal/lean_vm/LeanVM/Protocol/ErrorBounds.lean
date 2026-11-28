/-
  LeanVM.Protocol.ErrorBounds

  The random-permutation transfer's error in bits.
-/

module

public import LeanVM.Protocol.Errors

/-!
# The errors in bits

`LeanVM.Protocol.Errors` defines the random-permutation transfer's error; `rpmError_eq` reads it
over the naturals, and `inv_two_pow_eq_div` writes `2^-k` as a fraction of naturals, for bounds in
bits.
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

theorem rpmError_eq (q : ℕ) :
    rpmError q = ((q ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ 508 : ℕ) : ℝ≥0∞) := by
  rw [rpmError, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]

end

end LeanVM
