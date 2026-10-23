/-
  LeanVM.Protocol.Spine.Errors

  Knowledge errors as fractions of the challenge field's size.
-/

module

public import LeanVM.Protocol.Spine.Instance

/-!
# Errors as fractions of `|E|`

Every knowledge error of the protocol is a count of bad challenges over the size of the challenge
field `E`: `overE c = c / |E|`, with the arithmetic the slots' bounds use. The slots, their
schedules and the errors charged to each challenge are in `LeanVM.Protocol.Spine.Slots`.
-/

namespace LeanVM.Protocol

open LeanVM.Parameters
open scoped NNReal

@[expose] public section

/-! ## Errors as fractions of `|E|` -/

/-- `c / |E|`. -/
noncomputable def overE (c : ℕ) : ℝ≥0 := (c : ℝ≥0) / (Fintype.card E : ℝ≥0)

theorem overE_add (a b : ℕ) : overE (a + b) = overE a + overE b := by
  simp only [overE, Nat.cast_add, add_div]

theorem overE_mono {a b : ℕ} (h : a ≤ b) : overE a ≤ overE b := by
  unfold overE
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr h) (by positivity)

theorem nat_mul_overE (n c : ℕ) : (n : ℝ≥0) * overE c = overE (n * c) := by
  simp only [overE, Nat.cast_mul]
  ring

/-- The unit `overE 1` is `1 / |E|` with `|E|` counted by `Nat.card`, the form of a generic
component's error. -/
theorem overE_one : overE 1 = (1 / Nat.card E : ℝ≥0) := by
  rw [overE, Nat.card_eq_fintype_card, Nat.cast_one]

/-- `k / |E|` with `|E|` counted by `Nat.card`, the form a generic component's error takes, is
`overE k`. -/
theorem natCast_div_card_eq_overE (k : ℕ) : ((k : ℝ≥0) / Nat.card E) = overE k := by
  rw [overE, Nat.card_eq_fintype_card]

end
end LeanVM.Protocol
