/-
  LeanVM.Guest.B1.Sig.SphincsDigest

  The fields of the leanSPHINCS message digest as the guest rebuilds them: the sixteen codeword
  bytes of the first cell, and the index, super-children, children and unused bits the second
  cell's fields add up to.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsCoord
public import LeanVM.Guest.B1.Sig.Codeword

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Digits in base `2^w` -/

theorem baseW_lt (w : Nat) {d : Nat → Nat} : ∀ n, (∀ k < n, d k < 2 ^ w) →
    ∑ k ∈ Finset.range n, d k * 2 ^ (w * k) < 2 ^ (w * n)
  | 0, _ => by simp
  | n + 1, hd => by
      rw [Finset.sum_range_succ, show w * (n + 1) = w * n + w by ring, pow_add]
      have hS := baseW_lt w n fun k hk => hd k (by omega)
      have h1 : d n + 1 ≤ 2 ^ w := hd n (by omega)
      have h2 : ∑ k ∈ Finset.range n, d k * 2 ^ (w * k) + d n * 2 ^ (w * n) < (d n + 1) * 2 ^ (w * n) := by
        rw [Nat.add_mul, one_mul]; omega
      calc _ < (d n + 1) * 2 ^ (w * n) := h2
        _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_right _ h1
        _ = 2 ^ (w * n) * 2 ^ w := Nat.mul_comm _ _

theorem baseW_digit (w : Nat) {d : Nat → Nat} : ∀ n, (∀ k < n, d k < 2 ^ w) → ∀ i < n,
    (∑ k ∈ Finset.range n, d k * 2 ^ (w * k)) / 2 ^ (w * i) % 2 ^ w = d i
  | 0, _, _, h => absurd h (by omega)
  | n + 1, hd, i, hi => by
      rw [Finset.sum_range_succ]
      have hlt := baseW_lt w n fun k hk => hd k (by omega)
      by_cases h : i = n
      · subst h
        rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add,
          Nat.mod_eq_of_lt (hd i (by omega))]
      · obtain ⟨r, rfl⟩ : ∃ r, n = i + 1 + r := ⟨n - i - 1, by omega⟩
        rw [show d (i + 1 + r) * 2 ^ (w * (i + 1 + r)) = 2 ^ (w * i) * (2 ^ w * (d (i + 1 + r) * 2 ^ (w * r))) by
            rw [show w * (i + 1 + r) = w * i + w + w * r by ring, pow_add, pow_add]; ring,
          Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left,
          baseW_digit w (i + 1 + r) (fun k hk => hd k (by omega)) i (by omega)]

/-- Fields of width `w` from bit `p` add up as literals. -/
theorem lit_sum_fields (w p : Nat) {d : Nat → Nat} : ∀ n, (∀ k < n, d k < 2 ^ w) →
    ∑ k ∈ Finset.range n, lit (d k * 2 ^ (p + w * k)) = lit (2 ^ p * ∑ k ∈ Finset.range n, d k * 2 ^ (w * k))
  | 0, _ => by simp [lit_zero]
  | n + 1, hd => by
      have hlt : 2 ^ p * ∑ k ∈ Finset.range n, d k * 2 ^ (w * k) < 2 ^ (p + w * n) := by
        rw [pow_add]
        exact Nat.mul_lt_mul_of_pos_left (baseW_lt w n fun k hk => hd k (by omega)) (by positivity)
      rw [Finset.sum_range_succ, Finset.sum_range_succ, lit_sum_fields w p n fun k hk => hd k (by omega),
        Nat.mul_add, show 2 ^ p * (d n * 2 ^ (w * n)) = 2 ^ (p + w * n) * d n by rw [pow_add]; ring,
        show d n * 2 ^ (p + w * n) = 2 ^ (p + w * n) * d n by ring,
        add_comm (2 ^ p * ∑ k ∈ Finset.range n, d k * 2 ^ (w * k)), lit_add_of_lt hlt, add_comm]

theorem sum_pairs {M : Type} [AddCommMonoid M] (f : Nat → M) :
    ∀ n, ∑ c ∈ Finset.range n, (f (2 * c) + f (2 * c + 1)) = ∑ k ∈ Finset.range (2 * n), f k
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, sum_pairs f n, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, add_assoc]

theorem lit_eOfNat {N : Nat} (h : N < 2 ^ 64) : lit N = eOfNat N := by
  rw [lit, Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h, Nat.zero_mod, word_eq_eOfNat]

/-! ## The second cell -/

/-- The second cell's number: the index, then from bit 26 the super-children (4 bits each), from
bit 58 the children (3 bits each), from bit 106 the unused bits. -/
def digestHi (N U : Nat) (s a : Nat → Nat) : Nat :=
  N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 58 * ∑ k ∈ Finset.range 16, a k * 2 ^ (3 * k) +
    2 ^ 106 * U

/-- **The bound is the second cell's literal.** -/
theorem lit_digestHi {N U : Nat} {s a : Nat → Nat} (hN : N < 2 ^ 26) (hs : ∀ c < 8, s c < 2 ^ 4)
    (ha : ∀ k < 16, a k < 2 ^ 3) :
    eOfNat N + lit (U * 2 ^ 106) + ∑ c ∈ Finset.range 8, (lit (a (2 * c) * 2 ^ (58 + 3 * (2 * c))) +
      lit (a (2 * c + 1) * 2 ^ (58 + 3 * (2 * c + 1))) + lit (s c * 2 ^ (26 + 4 * c))) =
      lit (digestHi N U s a) := by
  have hS := baseW_lt 4 8 hs
  have hA := baseW_lt 3 16 ha
  rw [Finset.sum_add_distrib, sum_pairs (fun k => lit (a k * 2 ^ (58 + 3 * k))) 8, lit_sum_fields 3 58 16 ha,
    lit_sum_fields 4 26 8 hs, ← lit_eOfNat (by omega), digestHi]
  rw [show N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 58 * ∑ k ∈ Finset.range 16, a k * 2 ^ (3 * k) +
      2 ^ 106 * U = 2 ^ 106 * U + (2 ^ 58 * ∑ k ∈ Finset.range 16, a k * 2 ^ (3 * k) +
        (2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + N)) by ring,
    lit_add_of_lt (by norm_num at hS hA ⊢; omega), lit_add_of_lt (by norm_num at hS ⊢; omega),
    lit_add_of_lt hN, show U * 2 ^ 106 = 2 ^ 106 * U by ring]
  abel

theorem digestHi_lt {N U : Nat} {s a : Nat → Nat} (hN : N < 2 ^ 26) (hU : U < 2 ^ 22) (hs : ∀ c < 8, s c < 2 ^ 4)
    (ha : ∀ k < 16, a k < 2 ^ 3) : digestHi N U s a < 2 ^ 128 := by
  have hS := baseW_lt 4 8 hs
  have hA := baseW_lt 3 16 ha
  unfold digestHi
  norm_num at hS hA ⊢
  omega

theorem digestHi_index {N U : Nat} {s a : Nat → Nat} (hN : N < 2 ^ 26) :
    digestHi N U s a % 2 ^ 26 = N := by
  unfold digestHi
  rw [show N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 58 * ∑ k ∈ Finset.range 16, a k * 2 ^ (3 * k) +
      2 ^ 106 * U = N + 2 ^ 26 * (∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 32 * ∑ k ∈ Finset.range 16,
        a k * 2 ^ (3 * k) + 2 ^ 80 * U) by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hN]

theorem digestHi_super {N U : Nat} {s a : Nat → Nat} (hN : N < 2 ^ 26) (hs : ∀ c < 8, s c < 2 ^ 4) {c : Nat}
    (hc : c < 8) : digestHi N U s a / 2 ^ (26 + 4 * c) % 2 ^ 4 = s c := by
  have hS := baseW_lt 4 8 hs
  unfold digestHi
  rw [show N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 58 * ∑ k ∈ Finset.range 16, a k * 2 ^ (3 * k) +
      2 ^ 106 * U = N + 2 ^ 26 * (∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 32 * (∑ k ∈ Finset.range 16,
        a k * 2 ^ (3 * k) + 2 ^ 48 * U)) by ring, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hN, Nat.zero_add]
  rw [show (2 : Nat) ^ 32 = 2 ^ (4 * c) * 2 ^ 4 * 2 ^ (28 - 4 * c) by
      rw [← pow_add, ← pow_add]; congr 1; omega, Nat.mul_assoc, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, baseW_digit 4 8 hs c hc]

theorem digestHi_child {N U : Nat} {s a : Nat → Nat} (hN : N < 2 ^ 26) (hs : ∀ c < 8, s c < 2 ^ 4)
    (ha : ∀ k < 16, a k < 2 ^ 3) {k : Nat} (hk : k < 16) : digestHi N U s a / 2 ^ (58 + 3 * k) % 2 ^ 3 = a k := by
  have hS := baseW_lt 4 8 hs
  have hlo : N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) < 2 ^ 58 := by norm_num at hS ⊢; omega
  unfold digestHi
  rw [show N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c) + 2 ^ 58 * ∑ k ∈ Finset.range 16, a k * 2 ^ (3 * k) +
      2 ^ 106 * U = (N + 2 ^ 26 * ∑ c ∈ Finset.range 8, s c * 2 ^ (4 * c)) + 2 ^ 58 * (∑ k ∈ Finset.range 16,
        a k * 2 ^ (3 * k) + 2 ^ 48 * U) by ring, pow_add, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [show (2 : Nat) ^ 48 = 2 ^ (3 * k) * 2 ^ 3 * 2 ^ (45 - 3 * k) by
      rw [← pow_add, ← pow_add]; congr 1; omega, Nat.mul_assoc, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, baseW_digit 3 16 ha k hk]

end
end LeanVM.Guest.B1.Sig
