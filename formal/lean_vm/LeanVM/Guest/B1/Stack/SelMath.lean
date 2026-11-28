/-
  LeanVM.Guest.B1.Stack.SelMath

  The selector tables' entries as products over an offset's bits, and an offset from its nibbles.
-/

module

public import LeanVM.Guest.B1.Stack.SelTables
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The selectors' arithmetic

* `selLev_prod`: level `w`'s entry `k` of nibble `j` is the product over its `w + 1` bits of
  `point` (bit set) or `point1` at the coordinates `4 j + 3 - w ..`;
* `selLev_nib`: at `k·2^lo` the nibble of `idx` at `j`, the entry of level `3 - lo` is
  `Π_{4j + lo ≤ t < 4j + 4} selBit p p1 idx t`;
* `nibSum`, `nibSum_digit`: the offset rebuilt from its hinted nibbles `e_i` (`Σ e_i 16^(j0 + i)`, each
  below `16`) has them as its nibbles.
-/

namespace LeanVM.Guest.B1.Stack

open LeanVM.Parameters

@[expose] public section

/-- The point's factor at bit `t` of the offset `idx`: `point_t` at a set bit, `point1_t` else. -/
def selBit (p p1 : ℕ → E) (idx t : ℕ) : E := if idx.testBit t then p t else p1 t

theorem selLev_prod (p p1 : ℕ → E) (j : ℕ) : ∀ w < 4, ∀ k < 2 ^ (w + 1),
    selLev p p1 j w k = ∏ u ∈ Finset.range (w + 1),
      (if k.testBit u then p (4 * j + 3 - w + u) else p1 (4 * j + 3 - w + u)) := by
  intro w
  induction w with
  | zero =>
    intro _ k hk
    interval_cases k <;> simp [selLev]
  | succ w ih =>
    intro hw k hk
    rw [selLev, ih (by omega) (k / 2) (by rw [pow_succ] at hk; omega), Finset.prod_range_succ' _ (w + 1)]
    congr 1
    · refine Finset.prod_congr rfl fun u hu ↦ ?_
      rw [← Nat.testBit_div_two, show 4 * j + 3 - (w + 1) + (u + 1) = 4 * j + 3 - w + u by
        have := Finset.mem_range.1 hu; omega]
    · rw [Nat.testBit_zero, show 4 * j + 3 - (w + 1) + 0 = 4 * j + 2 - w by omega]
      rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]

/-- `idx`'s nibble `j`. -/
def nibOf (idx j : ℕ) : ℕ := idx >>> (4 * j) % 16

theorem nibOf_testBit (idx j t : ℕ) (ht : t < 4) : (nibOf idx j).testBit t = idx.testBit (4 * j + t) := by
  rw [nibOf, show (16 : ℕ) = 2 ^ 4 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [ht]

/-- **A nibble's entry**: at `k·2^lo = nibOf idx j`, level `3 - lo`'s entry is the product of the
nibble's factors from bit `lo` up. -/
theorem selLev_nib (p p1 : ℕ → E) (idx j lo k : ℕ) (hlo : lo < 4) (hk : k * 2 ^ lo = nibOf idx j) :
    selLev p p1 j (3 - lo) k = ∏ t ∈ Finset.Ico (4 * j + lo) (4 * j + 4), selBit p p1 idx t := by
  have hkb : k < 2 ^ (3 - lo + 1) := by
    have h16 : nibOf idx j < 16 := Nat.mod_lt _ (by decide)
    rw [← hk] at h16
    rw [show 3 - lo + 1 = 4 - lo by omega]
    have : k * 2 ^ lo < 2 ^ (4 - lo) * 2 ^ lo := by
      rw [← pow_add, show 4 - lo + lo = 4 by omega]; exact h16
    exact Nat.lt_of_mul_lt_mul_right this
  rw [selLev_prod p p1 j (3 - lo) (by omega) k hkb, Finset.prod_Ico_eq_prod_range,
    show 4 * j + 4 - (4 * j + lo) = 3 - lo + 1 by omega]
  refine Finset.prod_congr rfl fun u hu ↦ ?_
  have hu' := Finset.mem_range.1 hu
  have hbit : k.testBit u = idx.testBit (4 * j + lo + u) := by
    rw [show 4 * j + lo + u = 4 * j + (lo + u) by omega, ← nibOf_testBit idx j (lo + u) (by omega),
      ← hk, Nat.testBit_mul_two_pow]
    simp
  rw [selBit, hbit, show 4 * j + 3 - (3 - lo) + u = 4 * j + lo + u by omega]

/-! ## The nibbles -/

/-- The offset rebuilt from the digits `e` of nibbles `j0 ..< j0 + c`. -/
def nibSum (e : ℕ → ℕ) (j0 : ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 => nibSum e j0 c + e c * 16 ^ (j0 + c)

theorem nibSum_lt (e : ℕ → ℕ) (j0 : ℕ) : ∀ c, (∀ i < c, e i < 16) → nibSum e j0 c < 16 ^ (j0 + c) := by
  intro c
  induction c with
  | zero => intro _; simp [nibSum]
  | succ c ih =>
    intro he
    have h1 := ih (fun i hi ↦ he i (by omega))
    have h2 := he c (by omega)
    rw [nibSum, show j0 + (c + 1) = j0 + c + 1 by omega, pow_succ]
    have : e c * 16 ^ (j0 + c) ≤ 15 * 16 ^ (j0 + c) := Nat.mul_le_mul_right _ (by omega)
    nlinarith

theorem nibSum_dvd (e : ℕ → ℕ) (j0 : ℕ) : ∀ c, 16 ^ j0 ∣ nibSum e j0 c
  | 0 => by simp [nibSum]
  | c + 1 => by
    rw [nibSum]
    exact Nat.dvd_add (nibSum_dvd e j0 c) (Dvd.dvd.mul_left (pow_dvd_pow 16 (by omega)) _)

/-- **The rebuilt offset's nibbles are the digits.** -/
theorem nibSum_digit (e : ℕ → ℕ) (j0 : ℕ) : ∀ c, (∀ i < c, e i < 16) → ∀ i < c,
    nibOf (nibSum e j0 c) (j0 + i) = e i := by
  intro c
  induction c with
  | zero => intro _ i hi; omega
  | succ c ih =>
    intro he i hi
    have hlt := nibSum_lt e j0 c (fun i hi ↦ he i (by omega))
    unfold nibOf
    rw [Nat.shiftRight_eq_div_pow, show 2 ^ (4 * (j0 + i)) = 16 ^ (j0 + i) by rw [pow_mul]; rfl, nibSum]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · -- an earlier digit: the new one adds a multiple of `16` past it
      have := ih (fun i hi ↦ he i (by omega)) i h
      unfold nibOf at this
      rw [Nat.shiftRight_eq_div_pow, show 2 ^ (4 * (j0 + i)) = 16 ^ (j0 + i) by rw [pow_mul]; rfl] at this
      rw [show e c * 16 ^ (j0 + c) = 16 ^ (j0 + i) * (16 * (e c * 16 ^ (c - i - 1))) by
          rw [show j0 + c = (j0 + i) + 1 + (c - i - 1) by omega, pow_add, pow_add]; ring,
        Nat.add_mul_div_left _ _ (pow_pos (by decide) _), Nat.add_mul_mod_self_left]
      exact this
    · subst h
      rw [Nat.add_comm, mul_comm (e i), Nat.mul_add_div (pow_pos (by decide) _), Nat.div_eq_of_lt hlt,
        Nat.add_zero, Nat.mod_eq_of_lt (he _ (by omega))]

end
end LeanVM.Guest.B1.Stack
