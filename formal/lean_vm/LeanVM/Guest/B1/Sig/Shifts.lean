/-
  LeanVM.Guest.B1.Sig.Shifts

  The integer of hinted bits, and a right shift split at its lowest bit.
-/

module

public import LeanVM.Guest.B1.Sig.Merkle
public import LeanVM.Guest.Value.Bits

/-!
# Shifts of bits

`bitsOf σ bitBase n`: the integer of the `n` bits from `bitBase`. `shiftRight_split`:
`N >>> k = 2 (N >>> (k + 1)) + bit k`, one Horner step of a field's right shifts.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader} {σ : Val}

/-- The integer of the `n` bits from `bitBase`, the cell holding `1` a set bit. -/
noncomputable def bitsOf (σ : Val) (bitBase n : Nat) : Nat :=
  bitsVal (fun j => decide (σ (.n (bitBase + j)) = 1)) n

theorem shiftRight_split (N k : Nat) : N >>> k = 2 * (N >>> (k + 1)) + (N.testBit k).toNat := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.testBit, Nat.shiftRight_eq_div_pow,
    pow_succ, ← Nat.div_div_eq_div_mul]
  have := Nat.div_add_mod (N / 2 ^ k) 2
  rcases Nat.mod_two_eq_zero_or_one (N / 2 ^ k) with h | h <;> simp [h] <;> omega

end
end LeanVM.Guest.B1.Sig
