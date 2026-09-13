import SphincsSecurity.Proof.Base.Prelude
/-!
# Index arithmetic

The facts every Merkle argument needs: a node's index one level up is half of it, the sibling of an
index is that index with its low bit flipped, and the bit the fold tests is that low bit.
-/

namespace SphincsSecurity

/-- The statement writes `Nat.xor`, the bit library `^^^`; rewriting needs them bridged. -/
theorem nat_xor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl

theorem div_pow_succ (x k : Nat) : x / 2 ^ (k + 1) = x / 2 ^ k / 2 := by
  rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem xor_one_div_two (j : Nat) : Nat.xor (2 * j) 1 / 2 = j := by
  rw [nat_xor_eq, show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib, Nat.shiftRight_eq_div_pow]
  simp

theorem xor_one_two_mul (j : Nat) : Nat.xor (2 * j) 1 = 2 * j + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => rw [nat_xor_eq]; simp [Nat.testBit_zero]
  | succ i =>
      rw [Nat.testBit_succ, Nat.testBit_succ, xor_one_div_two, Nat.mul_add_div (by omega)]
      simp

theorem xor_one_two_mul_add_one (j : Nat) : Nat.xor (2 * j + 1) 1 = 2 * j := by
  rw [← xor_one_two_mul j, nat_xor_eq, nat_xor_eq, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- An index and its sibling are the two children of the index one level up; the low bit says which
of them is the left one. -/
theorem index_sibling_cases (c : Nat) :
    ∃ j, (c = 2 * j ∧ Nat.xor c 1 = 2 * j + 1 ∧ c % 2 = 0)
      ∨ (c = 2 * j + 1 ∧ Nat.xor c 1 = 2 * j ∧ c % 2 = 1) := by
  obtain ⟨j, hj⟩ : ∃ j, c / 2 = j := ⟨c / 2, rfl⟩
  have hdm := Nat.div_add_mod c 2
  rcases Nat.mod_two_eq_zero_or_one c with hmod | hmod
  · have hc : c = 2 * j := by omega
    exact ⟨j, Or.inl ⟨hc, by rw [hc]; exact xor_one_two_mul j, hmod⟩⟩
  · have hc : c = 2 * j + 1 := by omega
    exact ⟨j, Or.inr ⟨hc, by rw [hc]; exact xor_one_two_mul_add_one j, hmod⟩⟩

theorem testBit_iff_div_mod (x k : Nat) : x.testBit k = true ↔ x / 2 ^ k % 2 = 1 := by
  rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff]

end SphincsSecurity
