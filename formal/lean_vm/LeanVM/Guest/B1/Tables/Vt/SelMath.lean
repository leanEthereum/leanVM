/-
  LeanVM.Guest.B1.Tables.Vt.SelMath

  A bus block's selector from its pinned bits: the `g`-power of the bits is the block's offset,
  and their eq weight is `Placement.eqAbove`.
-/

module

public import LeanVM.Guest.B1.Tables.Vt.Shared
public import LeanVM.Guest.B1.Selectors.ColumnSelector
public import LeanVM.Guest.B1.Selectors.BlockSelectorTab

/-!
# A block's selector (G:2326-2382)

Both selector paths of `verify_tables` (`block_selector`, `block_selector_tab`) return the eq
weight of `n = μ - κ` pinned bits against the bus point above `κ`, and the `g`-power
`Π g^(2^(κ+i)·b_i)` of the bits, which the guest asserts to be the block's `g^offset`. Then the
offset is `2^κ·V` for the bits' value `V` (`vt_offset_bits`), and the eq weight is the
specification's `eqAbove` of the placement `⟨κ, offset⟩` (`vt_eqAbove`).
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier

@[expose] public section

/-- The bits' value. -/
abbrev vtBitsV (bs : List Bool) (n : ℕ) : ℕ := bitsVal (bs.getD · false) n

theorem vt_foldl_mul_zipWith {f : E → E → E} : ∀ {n : ℕ} {l1 l2 : List E}, l1.length = n →
    l2.length = n → (List.zipWith f l1 l2).foldl (· * ·) 1 =
      ∏ i ∈ Finset.range n, f (l1.getD i 0) (l2.getD i 0)
  | 0, l1, l2, h1, h2 => by
    rw [List.length_eq_zero_iff] at h1 h2; subst h1 h2; rfl
  | n + 1, a :: l1, b :: l2, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    rw [List.zipWith_cons_cons, List.foldl_cons, Finset.prod_range_succ']
    have hf : ∀ (c : E) (l : List E), l.foldl (· * ·) c = c * l.foldl (· * ·) 1 := by
      intro c l
      induction l generalizing c with
      | nil => simp
      | cons x l ih => rw [List.foldl_cons, List.foldl_cons, ih, ih (1 * x)]; ring
    rw [hf, vt_foldl_mul_zipWith h1 h2, one_mul, mul_comm]
    rfl

/-- **The block's eq weight is `eqAbove`.** -/
theorem vt_eqAbove {κ n : ℕ} {bs : List Bool} (hbl : bs.length = n) {point : List E}
    (hpl : point.length = κ + n) :
    bitsEq bs (point.drop κ) ((point.map (1 + ·)).drop κ) =
      Placement.eqAbove ⟨κ, 2 ^ κ * vtBitsV bs n⟩ point := by
  simp only [Placement.eqAbove]
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (Nat.two_pow_pos κ),
    bitsEq_eq_prod hbl (by simp; omega) (by simp; omega), eqEval,
    vt_foldl_mul_zipWith (n := n) (by simp [selectorPoint]; omega) (by simp; omega)]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp only [selectorPoint, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show i < point.length - κ by omega), Option.map_some, Option.getD_some,
    List.getElem?_drop, List.getElem?_eq_getElem (show κ + i < point.length by omega)]
  have hb : (vtBitsV bs n >>> i) % 2 = (bs.getD i false).toNat := by
    have ht : (vtBitsV bs n).testBit i = decide (vtBitsV bs n / 2 ^ i % 2 = 1) :=
      Nat.testBit_eq_decide_div_mod_eq
    rw [testBit_bitsVal] at ht
    simp only [hi', decide_true, Bool.true_and] at ht
    rw [Nat.shiftRight_eq_div_pow]
    cases hbi : bs.getD i false <;> rw [hbi] at ht <;> simp at ht ⊢ <;> omega
  rw [hb]
  cases hbi : bs.getD i false
  · simp [List.getD_eq_getElem?_getD] at hbi ⊢
    rw [show (bs[i]?.getD false) = false from hbi]
    simp [eOfNat_zero]
  · simp [List.getD_eq_getElem?_getD] at hbi ⊢
    rw [show (bs[i]?.getD false) = true from hbi]
    simp only [↓reduceIte]
    rw [eOfNat_one, e_add_self, zero_add]

theorem vt_prod_zip {f : Bool → E → E} : ∀ {n : ℕ} {bs : List Bool} {cs : List E}, bs.length = n →
    cs.length = n → ((List.zip bs cs).map fun p ↦ f p.1 p.2).prod =
      ∏ i ∈ Finset.range n, f (bs.getD i false) (cs.getD i 0)
  | 0, bs, cs, h1, h2 => by rw [List.length_eq_zero_iff] at h1 h2; subst h1 h2; rfl
  | n + 1, b :: bs, c :: cs, h1, h2 => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    rw [List.zip_cons_cons, List.map_cons, List.prod_cons, vt_prod_zip h1 h2,
      Finset.prod_range_succ', mul_comm]
    rfl

theorem vt_pow_bit (κ i : ℕ) (b : Bool) :
    (if b then gen ^ 2 ^ (κ + i) else 1) = gen ^ (2 ^ (κ + i) * b.toNat) := by
  cases b <;> simp

/-- The tab path's `g`-power of the bits. -/
theorem vt_bitsPow_sq {κ n : ℕ} {bs : List Bool} (hbl : bs.length = n) (hkn : κ + n ≤ 34) :
    bitsPow bs ((gSquaresList.drop κ).take n) = gen ^ (2 ^ κ * vtBitsV bs n) := by
  rw [bitsPow_eq_prod hbl (by simp [gSquaresList]; omega), ← prod_gen_pow_bits]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [← vt_pow_bit]
  congr 1
  simp [gSquaresList, List.getD_eq_getElem?_getD, hi',
    List.getElem?_range (show κ + i < 34 by omega)]

/-- The index MLE's factors `1 + g^(2^t)`. -/
def vtIdxcList : List E := (List.range 34).map fun t ↦ 1 + gen ^ 2 ^ t

/-- The `block_selector` path's `g`-power of the bits. -/
theorem vt_idxcProd {κ n : ℕ} {bs : List Bool} (hbl : bs.length = n) (hkn : κ + n ≤ 34) :
    ((List.zip bs ((vtIdxcList.drop κ).take n)).map fun p ↦ 1 + bitE p.1 * p.2).prod =
      gen ^ (2 ^ κ * vtBitsV bs n) := by
  rw [vt_prod_zip (f := fun b c ↦ 1 + bitE b * c) hbl (by simp [vtIdxcList]; omega),
    ← prod_gen_pow_bits]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hc : ((vtIdxcList.drop κ).take n).getD i 0 = 1 + gen ^ 2 ^ (κ + i) := by
    simp [vtIdxcList, List.getD_eq_getElem?_getD, hi',
      List.getElem?_range (show κ + i < 34 by omega)]
  rw [hc, ← vt_pow_bit]
  cases bs.getD i false
  · simp [bitE]
  · simp only [bitE, ↓reduceIte, one_mul]
    rw [← add_assoc, e_add_self, zero_add]

/-- **The offset is the bits' value, shifted.** -/
theorem vt_offset_bits {κ n off : ℕ} {bs : List Bool} (hkn : κ + n ≤ 34) (hoff : off < 2 ^ 62)
    (h : gen ^ (2 ^ κ * vtBitsV bs n) = gen ^ off) : off = 2 ^ κ * vtBitsV bs n := by
  have hv := bitsVal_lt (bs.getD · false) n
  have : 2 ^ κ * vtBitsV bs n < 2 ^ 34 := by
    calc 2 ^ κ * vtBitsV bs n < 2 ^ κ * 2 ^ n := Nat.mul_lt_mul_of_pos_left hv (Nat.two_pow_pos κ)
      _ = 2 ^ (κ + n) := (pow_add 2 κ n).symm
      _ ≤ 2 ^ 34 := Nat.pow_le_pow_right (by norm_num) hkn
  exact (gen_pow_inj (by omega) (by omega) h).symm

end
end LeanVM.Guest.B1.Tables
