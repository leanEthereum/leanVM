module

public import CompPoly.Fields.Binary.Common
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Words as polynomials, by classes of bit positions mod 4

The tools of the carry-less product by integer multiplication (`clmulLow`,
`NativeRustcVm.Field.ClmulLow`): a bit as an element of `GF(2)` (`zb`), a word's coefficients
(`coeff_toPoly`), the bits of a word at positions `≡ r (mod 4)` as a polynomial over `ℕ` in
`X = x^4` (`cls`), the masks `0x1111…`, `0x2222…`, `0x4444…`, `0x8888…` (`mask`), and the
digits of `F(16)` while `F`'s coefficients stay below `16` (`eval16_div`, `testBit_eval16`), so
that a masked word is `2^r · cls(16)` (`toNat_and_mask`).
-/

namespace NativeRustcVm.Field

open Polynomial BinaryField

@[expose] public section

/-- A bit as an element of `GF(2)`. -/
def zb (b : Bool) : ZMod 2 := if b then 1 else 0

theorem zb_bne (x y : Bool) : zb (x != y) = zb x + zb y := by
  cases x <;> cases y <;> decide

theorem zb_false : zb false = 0 := rfl

/-- The parity of a natural number as its lowest bit. -/
theorem natCast_eq_zb (c : ℕ) : (c : ZMod 2) = zb (c.testBit 0) := by
  rw [← ZMod.natCast_mod c 2, Nat.testBit_zero]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h, zb]

/-- The coefficients of a word's polynomial are its bits. -/
theorem coeff_toPoly {w : ℕ} (v : BitVec w) (n : ℕ) : (toPoly v).coeff n = zb (v.getLsbD n) := by
  rw [toPoly_coeff]
  split
  · rfl
  · rw [BitVec.getLsbD_of_ge v n (by omega)]; rfl

/-! ## Classes of bit positions -/

/-- The masks of the four classes of bit positions mod 4. -/
def mask : ℕ → BitVec 64
  | 0 => 0x1111111111111111#64
  | 1 => 0x2222222222222222#64
  | 2 => 0x4444444444444444#64
  | _ => 0x8888888888888888#64

theorem getLsbD_mask_lt : ∀ r < 4, ∀ i < 64, (mask r).getLsbD i = decide (i % 4 = r) := by
  decide +kernel

theorem getLsbD_mask {r : ℕ} (hr : r < 4) (i : ℕ) :
    (mask r).getLsbD i = (decide (i < 64) && decide (i % 4 = r)) := by
  by_cases hi : i < 64
  · rw [getLsbD_mask_lt r hr i hi]; simp [hi]
  · rw [BitVec.getLsbD_of_ge _ i (by omega)]; simp [hi]

/-- The bits of `a` at positions `4m + r`, the `m`-th as the coefficient of `X^m`. -/
noncomputable def cls (a : BitVec 64) (r : ℕ) : ℕ[X] :=
  ∑ m ∈ Finset.range 16, monomial m (if a.getLsbD (4 * m + r) then 1 else 0)

theorem coeff_cls (a : BitVec 64) (r n : ℕ) :
    (cls a r).coeff n = if n < 16 ∧ a.getLsbD (4 * n + r) then 1 else 0 := by
  simp only [cls, finsetSum_coeff, coeff_monomial, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_range]
  by_cases h : n < 16 <;> simp [h]

theorem coeff_cls_le (a : BitVec 64) (r n : ℕ) : (cls a r).coeff n ≤ 1 := by
  rw [coeff_cls]; split <;> omega

/-- A coefficient of a product of two classes counts at most `n + 1` pairs. -/
theorem coeff_cls_mul_le (a b : BitVec 64) (r s n : ℕ) : (cls a r * cls b s).coeff n ≤ n + 1 := by
  rw [coeff_mul]
  calc _ ≤ ∑ _x ∈ Finset.antidiagonal n, 1 :=
        Finset.sum_le_sum fun x _ ↦
          (Nat.mul_le_mul (coeff_cls_le a r x.1) (coeff_cls_le b s x.2)).trans (by norm_num)
    _ = n + 1 := by simp

/-! ## Base-16 digits -/

theorem sum_digits_lt (c : ℕ → ℕ) :
    ∀ m, (∀ n < m, c n < 16) → ∑ i ∈ Finset.range m, c i * 16 ^ i < 16 ^ m
  | 0, _ => by simp
  | m + 1, h => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := sum_digits_lt c m fun n hn ↦ h n (by omega)
    have h2 := h m (by omega)
    have h3 : c m * 16 ^ m ≤ 15 * 16 ^ m := Nat.mul_le_mul_right _ (by omega)
    omega

/-- **The `m`-th base-16 digit of `F(16)`** is `F`'s `m`-th coefficient mod 16, the lower ones
below 16. -/
theorem eval16_div (F : ℕ[X]) (m : ℕ) (h : ∀ n < m, F.coeff n < 16) :
    F.eval 16 / 16 ^ m % 16 = F.coeff m % 16 := by
  set N := max (F.natDegree + 1) (m + 1)
  rw [eval_eq_sum_range' (n := N) (by omega), ← Finset.sum_range_add_sum_Ico _ (show m ≤ N by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show m < N by omega)]
  have hT : ∑ i ∈ Finset.Ico (m + 1) N, F.coeff i * 16 ^ i =
      16 ^ m * (16 * ∑ i ∈ Finset.Ico (m + 1) N, F.coeff i * 16 ^ (i - (m + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    obtain ⟨j, rfl⟩ : ∃ j, i = m + 1 + j := ⟨i - (m + 1), by have := (Finset.mem_Ico.mp hi).1; omega⟩
    rw [Nat.add_sub_cancel_left, pow_add, pow_succ]
    ring
  rw [hT, show ∀ L c T : ℕ, L + (c * 16 ^ m + 16 ^ m * (16 * T)) = L + 16 ^ m * (c + 16 * T)
      from fun _ _ _ ↦ by ring, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt (sum_digits_lt _ m h), zero_add, Nat.add_mul_mod_self_left]

/-- A bit of `F(16)`, `F`'s coefficients below 16 under it. -/
theorem testBit_eval16 (F : ℕ[X]) (j : ℕ) (h : ∀ n < j / 4, F.coeff n < 16) :
    (F.eval 16).testBit j = (F.coeff (j / 4)).testBit (j % 4) := by
  have hu : j % 4 < 4 := Nat.mod_lt _ (by omega)
  calc (F.eval 16).testBit j = (F.eval 16 >>> (4 * (j / 4))).testBit (j % 4) := by
        rw [Nat.testBit_shiftRight]; congr 1; omega
    _ = (F.eval 16 / 16 ^ (j / 4) % 2 ^ 4).testBit (j % 4) := by
        rw [Nat.testBit_mod_two_pow, Nat.shiftRight_eq_div_pow, pow_mul]; simp [hu]
    _ = (F.coeff (j / 4) % 2 ^ 4).testBit (j % 4) := by
        rw [show (2 : ℕ) ^ 4 = 16 from rfl, eval16_div F _ h]
    _ = _ := by rw [Nat.testBit_mod_two_pow]; simp [hu]

/-- **A masked word** is its class at `16`, shifted by `r`. -/
theorem toNat_and_mask (a : BitVec 64) {r : ℕ} (hr : r < 4) :
    (a &&& mask r).toNat = 2 ^ r * (cls a r).eval 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.testBit_toNat, BitVec.getLsbD_and, getLsbD_mask hr, Nat.testBit_two_pow_mul,
    testBit_eval16 _ _ fun n _ ↦ lt_of_le_of_lt (coeff_cls_le a r n) (by omega), coeff_cls]
  by_cases h1 : r ≤ i
  · by_cases h2 : (i - r) % 4 = 0
    · have e : 4 * ((i - r) / 4) + r = i := by omega
      rw [e]
      by_cases h3 : i < 64
      · have : (i - r) / 4 < 16 := by omega
        have : i % 4 = r := by omega
        cases a.getLsbD i <;> simp [*]
      · simp [h3, BitVec.getLsbD_of_ge a i (by omega)]
    · have : i % 4 ≠ r := by omega
      rcases (show (i - r) % 4 = 1 ∨ (i - r) % 4 = 2 ∨ (i - r) % 4 = 3 by omega) with h | h | h <;>
        rw [h] <;> split <;> simp [this] <;> exact fun _ ↦ by decide
  · have : i % 4 ≠ r := by omega
    simp [this, h1]

end

end NativeRustcVm.Field
