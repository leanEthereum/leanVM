module

public import NativeRustcVm.Field.Rust
public import NativeRustcVm.Field.Poly

/-!
# The low word of the carry-less product

`clmulLow a b` is the low 64 bits of `a·b` in `GF(2)[x]` (`coeff_clmulLow`). A word is the sum
of its four classes of bit positions mod 4, `x^r · cls(x^4)` (`toPoly_eq_cls`), so the product is
the sum of the sixteen products of classes, `x^(r+s) · (cls_r · cls_s)(x^4)` (`term`). The integer
product of the masked words `2^r cls_r(16) · 2^s cls_s(16)` is `2^(r+s) (cls_r cls_s)(16)`, whose
coefficients count at most `n + 1 ≤ 15` pairs below the top, so its bit `k ≡ r + s (mod 4)` is
the parity of the coefficient (`getLsbD_mul_mask`): the term's coefficient. Bit `k` of
`clmulLow` keeps the four products of the class `k mod 4`; the other twelve terms vanish there.
-/

namespace NativeRustcVm.Field

open Polynomial BinaryField

public section

/-- A class in `GF(2)[X]`. -/
noncomputable abbrev clsZ (a : BitVec 64) (r : ℕ) : (ZMod 2)[X] :=
  (cls a r).map (Nat.castRingHom (ZMod 2))

/-- The product of the class `r` of `a` and the class `s` of `b`. -/
noncomputable def term (a b : BitVec 64) (r s : ℕ) : (ZMod 2)[X] :=
  X ^ (r + s) * expand (ZMod 2) 4 (clsZ a r * clsZ b s)

theorem coeff_term (a b : BitVec 64) (r s k : ℕ) :
    (term a b r s).coeff k = if r + s ≤ k ∧ (k - (r + s)) % 4 = 0 then
      (((cls a r * cls b s).coeff ((k - (r + s)) / 4) : ℕ) : ZMod 2) else 0 := by
  rw [term, coeff_X_pow_mul', ← Polynomial.map_mul, coeff_expand (by norm_num)]
  split_ifs <;> first | rfl | omega | (rw [coeff_map]; rfl)

/-- A word is the sum of its classes. -/
theorem toPoly_eq_cls (a : BitVec 64) :
    toPoly a = ∑ r ∈ Finset.range 4, X ^ r * expand (ZMod 2) 4 (clsZ a r) := by
  ext k
  rw [coeff_toPoly, finsetSum_coeff, Finset.sum_eq_single (k % 4)]
  · rw [coeff_X_pow_mul', ite_eq_left (Nat.mod_le k 4), coeff_expand (by norm_num),
      ite_eq_left (by omega), coeff_map, coeff_cls]
    have e : 4 * ((k - k % 4) / 4) + k % 4 = k := by omega
    rw [e]
    by_cases hk : k < 64
    · have : (k - k % 4) / 4 < 16 := by omega
      cases a.getLsbD k <;> simp [zb, this]
    · rw [BitVec.getLsbD_of_ge a k (by omega)]
      have : ¬ (k - k % 4) / 4 < 16 := by omega
      simp [zb, this]
  · intro r hr4 hr
    rw [Finset.mem_range] at hr4
    rw [coeff_X_pow_mul']
    split_ifs
    · rw [coeff_expand (by norm_num), ite_eq_right (by omega)]
    · rfl
  · intro h
    simp at h
    omega

/-- The product is the sum of the sixteen products of classes. -/
theorem toPoly_mul_eq (a b : BitVec 64) :
    toPoly a * toPoly b = ∑ r ∈ Finset.range 4, ∑ s ∈ Finset.range 4, term a b r s := by
  rw [toPoly_eq_cls a, toPoly_eq_cls b, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [term, pow_add, map_mul]
  ring

/-- **The integer product of two masked words**, at a bit of its class, is the term's
coefficient. -/
theorem getLsbD_mul_mask (a b : BitVec 64) {r s k : ℕ} (hr : r < 4) (hs : s < 4) (hk : k < 64)
    (hrs : (r + s) % 4 = k % 4) :
    zb (((a &&& mask r) * (b &&& mask s)).getLsbD k) = (term a b r s).coeff k := by
  have he : 2 ^ r * (cls a r).eval 16 * (2 ^ s * (cls b s).eval 16) =
      2 ^ (r + s) * (cls a r * cls b s).eval 16 := by
    rw [eval_mul, pow_add]; ring
  rw [coeff_term, ← BitVec.testBit_toNat, BitVec.toNat_mul, toNat_and_mask a hr,
    toNat_and_mask b hs, Nat.testBit_mod_two_pow, he, Nat.testBit_two_pow_mul]
  by_cases h : r + s ≤ k
  · have h4 : (k - (r + s)) % 4 = 0 := by omega
    rw [testBit_eval16 _ _ fun n hn ↦ lt_of_le_of_lt (coeff_cls_mul_le a b r s n) (by omega), h4,
      natCast_eq_zb]
    simp [h, hk]
  · simp [h, zb]

theorem clmulLow_eq_mask (a b : BitVec 64) : clmulLow a b =
    (((a &&& mask 0) * (b &&& mask 0)) ^^^ ((a &&& mask 1) * (b &&& mask 3)) ^^^
      ((a &&& mask 2) * (b &&& mask 2)) ^^^ ((a &&& mask 3) * (b &&& mask 1))) &&& mask 0 |||
    (((a &&& mask 0) * (b &&& mask 1)) ^^^ ((a &&& mask 1) * (b &&& mask 0)) ^^^
      ((a &&& mask 2) * (b &&& mask 3)) ^^^ ((a &&& mask 3) * (b &&& mask 2))) &&& mask 1 |||
    (((a &&& mask 0) * (b &&& mask 2)) ^^^ ((a &&& mask 1) * (b &&& mask 1)) ^^^
      ((a &&& mask 2) * (b &&& mask 0)) ^^^ ((a &&& mask 3) * (b &&& mask 3))) &&& mask 2 |||
    (((a &&& mask 0) * (b &&& mask 3)) ^^^ ((a &&& mask 1) * (b &&& mask 2)) ^^^
      ((a &&& mask 2) * (b &&& mask 1)) ^^^ ((a &&& mask 3) * (b &&& mask 0))) &&& mask 3 := rfl

/-- **`clmulLow` is the low word of the carry-less product.** -/
theorem coeff_clmulLow (a b : BitVec 64) {k : ℕ} (hk : k < 64) :
    zb ((clmulLow a b).getLsbD k) = (toPoly a * toPoly b).coeff k := by
  have hz : ∀ r s, (r + s) % 4 ≠ k % 4 → (term a b r s).coeff k = 0 := fun r s h ↦ by
    rw [coeff_term]
    split_ifs <;> first | rfl | omega
  have hw : ∀ r s, r < 4 → s < 4 → (r + s) % 4 = k % 4 →
      zb (((a &&& mask r) * (b &&& mask s)).getLsbD k) = (term a b r s).coeff k :=
    fun _ _ hr hs h ↦ getLsbD_mul_mask a b hr hs hk h
  have hm : ∀ r, r < 4 → (mask r).getLsbD k = decide (k % 4 = r) := fun r hr ↦ by
    rw [getLsbD_mask hr]; simp [hk]
  rw [toPoly_mul_eq, finsetSum_coeff, clmulLow_eq_mask]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h <;>
  · simp +decide only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor, hm 0 (by norm_num),
      hm 1 (by norm_num), hm 2 (by norm_num), hm 3 (by norm_num), h, decide_true, decide_false,
      Bool.and_true, Bool.and_false, Bool.or_false, Bool.false_or, zb_bne, coeff_add]
    simp (disch := omega) only [hw, hz, add_zero, zero_add]

end

end NativeRustcVm.Field
