module

public import LeanVMCircuits.BooleanOps
public import LeanVMCircuits.WordValues

@[expose] public section

namespace LeanVMCircuits.AluWord

open Adder

def complement {n : ℕ} (word : Vector Bit n) : Vector Bit n := word.map (1 + ·)

theorem complement_bit_value (bit : Bit) : (1 + bit).val + bit.val = 1 := by
  rcases bit_zero_or_one bit with rfl | rfl <;> simp

theorem complement_value {n : ℕ} (word : Vector Bit n) :
    value (complement word) + value word = 2 ^ n - 1 := by
  induction n with
  | zero => simp [value_zero]
  | succ n ih =>
    rw [value_pop (complement word), value_pop word]
    simp only [complement, ← Vector.map_pop, Vector.getElem_map]
    change value (complement word.pop) + 2 ^ n * (1 + word[n]).val +
      (value word.pop + 2 ^ n * word[n].val) = _
    calc
      _ = (value (complement word.pop) + value word.pop) +
          2 ^ n * ((1 + word[n]).val + word[n].val) := by ring
      _ = (2 ^ n - 1) + 2 ^ n := by rw [ih, complement_bit_value]; simp
      _ = 2 ^ (n + 1) - 1 := by
        rw [pow_succ]
        have h : 0 < (2 : ℕ) ^ n := by positivity
        omega

def signed (word : Vector Bit 64) : ℤ := (value word : ℤ) - 2 ^ 64 * (word[63].val : ℤ)

theorem sum_add {x y sum : Vector Bit 64} {carry : Bit}
    (h : value sum + 2 ^ 64 * carry.val = value x + value y) :
    sum = Words.ofNat 64 (value x + value y) := by
  apply value_injective
  rw [Words.value_ofNat, ← h]
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt (value_lt sum)).symm

theorem sum_sub {x y sum : Vector Bit 64} {carry : Bit}
    (h : value sum + 2 ^ 64 * carry.val = value x + value (complement y) + 1) :
    sum = Words.ofNat 64 (value x + 2 ^ 64 - value y) := by
  have hc := complement_value y
  have hb : 0 < (2 : ℕ) ^ 64 := by positivity
  have he : value sum + 2 ^ 64 * carry.val = value x + 2 ^ 64 - value y := by omega
  apply value_injective
  rw [Words.value_ofNat, ← he]
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]
  exact (Nat.mod_eq_of_lt (value_lt sum)).symm

theorem borrow {x y sum : Vector Bit 64} {carry : Bit}
    (h : value sum + 2 ^ 64 * carry.val = value x + value (complement y) + 1) :
    carry = 0 ↔ value x < value y := by
  have hc := complement_value y
  have hs := value_lt sum
  rcases bit_zero_or_one carry with rfl | rfl <;> simp at h ⊢ <;> omega

theorem signed_less (x y : Vector Bit 64) (less : Bit)
    (h : less = 1 ↔ value x < value y) :
    less + x[63] + y[63] = 1 ↔ signed x < signed y := by
  have hx := value_pop x
  have hy := value_pop y
  have hxl := value_lt x.pop
  have hyl := value_lt y.pop
  rcases bit_zero_or_one x[63] with hsx | hsx <;>
    rcases bit_zero_or_one y[63] with hsy | hsy <;>
    rcases bit_zero_or_one less with hl | hl <;>
    simp [signed, hsx, hsy, hl] at h hx hy ⊢ <;>
    norm_num at hx hy hxl hyl ⊢ <;> omega

end LeanVMCircuits.AluWord
