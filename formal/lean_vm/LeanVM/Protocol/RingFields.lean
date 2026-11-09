/-
  LeanVM.Protocol.RingFields

  The facts about leanVM's fields that ring switching rests on: a word of `K` is its bits packed
  by the powers of `x`, the Frobenius periods, and the injectivity of ring switching.
-/

module

public import Statement.LeanVmVerifier
public import LeanVM.Facts.Verifier
public import Statement.Fast.Keccak
public import Statement.Fast.CubicExt
public import Statement.Fast.FieldWords
public import LeanVM.Parameters.Field
public import LeanVM.Parameters.Generator
public import LeanVM.Protocol.Field
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Field facts for ring switching

Ring switching (`ringSwitch`, `crates/verifier/src/ring_switch.rs:36-54` at leanVM `40f877dc`;
`crates/pcs/src/ring_switch.rs`) packs the `64` bit
slices of `q_keccak` by the powers of `x = g` and draws a random `F_2`-linear map. Its soundness
rests on two facts about `K = GF(2^64)` and `E = K[y]/(y^3 + y + 1)` (`LeanVM.Parameters.Field`):

* `K.eq_sum_bits`: a word of `K` is its bits packed by the powers of `x`,
  `a = Σ_{i < 64} a_i · x^i` (through CompPoly's bridge to `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`).
* **Ring-switching injectivity**, `ringSwitch_injective`: a family `δ : Fin 64 → E` with
  `Σ_i x^i · δ_i^(2^k) = 0` for every `k < 64` is zero. Two steps: `limbs_eq_zero_of_frob`
  (`1, y^(2^k), y^(2^(k+1))` is a `K`-basis of `E`, so each limb family satisfies the same
  equations in `K`) and `eq_zero_of_frob_sums_K` (the polynomial `Σ_i d_i X^i`, of degree below
  64, vanishes at the 64 conjugates `x^(2^m)` of `x = g`, which are distinct by
  `g_conj_injective`, a kernel check on `K` words).

`ringSwitch_injective` needs all 64 twists `k < 64`: `δ ↦ (Σ_i x^i · δ_i^(2^k))_k` is
`F_2`-linear from `E^64`, so fewer than 64 twists cannot make it injective. The declarations live
in `LeanVM.Protocol.Ring`.
-/

namespace LeanVM.Protocol.Ring

open LeanVM.Parameters

@[expose] public section

/-! ## Packing bits into `K` -/

/-- A cell of `K` is its bits packed by the powers of `x`: `a = Σ_{i < 64} a_i · x^i`. -/
theorem K.eq_sum_bits (a : K) :
    a = ∑ i : Fin 64, if a.toBitVec.getLsbD i then g ^ (i : ℕ) else 0 := by
  apply BF64.toQuot_injective
  have hg : BF64.toQuot g = AdjoinRoot.root BF64.basePoly := by
    rw [BF64.toQuot, BF64.toPolyBF64, g, K.ofBits, BF64.toBitVec_ofBitVec,
      show BitVec.ofNat 64 2 = (1 <<< 1 : BitVec 64) by decide,
      BinaryField.toPoly_one_shiftLeft 1 (by norm_num), pow_one, AdjoinRoot.mk_X]
  have hsum : ∀ (s : Finset (Fin 64)) (f : Fin 64 → K),
      BF64.toQuot (∑ i ∈ s, f i) = ∑ i ∈ s, BF64.toQuot (f i) := fun s f ↦ by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, BF64.toQuot_add, ih]
  rw [hsum]
  conv_lhs => rw [BF64.toQuot, BF64.toPolyBF64, BinaryField.toPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [BitVec.getLsb, BitVec.getLsbD]
  split
  · rw [map_pow, AdjoinRoot.mk_X, BF64.toQuot_npow, hg]
  · rw [map_zero, BF64.toQuot_zero]

/-! ## `ofK` as a ring hom -/

private theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

private theorem ofK_sum {ι : Type*} (s : Finset ι) (f : ι → K) :
    ofK (∑ i ∈ s, f i) = ∑ i ∈ s, ofK (f i) :=
  map_sum (algebraMap K E) f s

/-! ## Frobenius periods -/

/-- Every `a : K` satisfies `a ^ 2 ^ 64 = a`. -/
theorem K.pow_two_pow_sixtyFour (a : K) : a ^ 2 ^ 64 = a := by
  have h := FiniteField.pow_card a
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
  exact h

/-- Every `a : E` satisfies `a ^ 2 ^ 192 = a`. -/
theorem E.pow_two_pow_oneNinetyTwo (a : E) : a ^ 2 ^ 192 = a := by
  have h := FiniteField.pow_card a
  simp only [card_E] at h
  exact h

/-- In characteristic two, `x^(2^a) = x^(2^b)` with `a ≤ b` gives `x^(2^(b-a)) = x`. -/
private theorem frob_cancel {R : Type*} [CommRing R] [IsReduced R] [ExpChar R 2] (x : R)
    {a b : ℕ} (hab : a ≤ b) (h : x ^ 2 ^ a = x ^ 2 ^ b) : x ^ 2 ^ (b - a) = x := by
  apply iterateFrobenius_inj R 2 a
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab]
  exact h.symm

/-- The Frobenius `x ↦ x^(2^m)` of a weighted sum of powers. -/
private theorem frob_sum {R : Type*} [CommRing R] [ExpChar R 2] {n : ℕ} (x : R) (v : Fin n → R)
    (m : ℕ) :
    (∑ i : Fin n, x ^ i.val * v i) ^ 2 ^ m = ∑ i : Fin n, (x ^ 2 ^ m) ^ i.val * v i ^ 2 ^ m := by
  rw [sum_pow_char_pow]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_pow, pow_right_comm x i.val (2 ^ m)]

/-! ## The conjugates of `x` -/

/-- Kernel check: `x^(2^d) ≠ x` for `0 < d < 64`. -/
private theorem g_frob_ne : ∀ d : Fin 64, d.val ≠ 0 → g ^ 2 ^ d.val ≠ g := by
  decide +kernel

/-- The 64 conjugates `x^(2^m)`, `m < 64`, of `x = g` are distinct. -/
theorem g_conj_injective : Function.Injective fun m : Fin 64 ↦ g ^ 2 ^ m.val := by
  intro a b hab
  simp only at hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with hlt | hlt
  · exact g_frob_ne ⟨b.val - a.val, by omega⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab)
  · exact g_frob_ne ⟨a.val - b.val, by omega⟩ (Nat.sub_ne_zero_of_lt hlt)
      (frob_cancel g hlt.le hab.symm)

/-- A family of `K` whose sums `Σ_i x^i · d_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem eq_zero_of_frob_sums_K (d : Fin 64 → K)
    (h : ∀ k < 64, ∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ k = 0) : ∀ i, d i = 0 := by
  have hroot : ∀ m : Fin 64, ∑ i : Fin 64, (g ^ 2 ^ m.val) ^ i.val * d i = 0 := by
    intro m
    by_cases hm : m.val = 0
    · simpa [hm] using h 0 (by norm_num)
    · have hk : (∑ i : Fin 64, g ^ i.val * d i ^ 2 ^ (64 - m.val)) ^ 2 ^ m.val = 0 := by
        rw [h _ (by omega), zero_pow (pow_ne_zero _ two_ne_zero)]
      rw [frob_sum] at hk
      rw [← hk]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← pow_mul (d i), ← pow_add, Nat.sub_add_cancel (by omega), K.pow_two_pow_sixtyFour]
  exact congrFun (Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero g_conj_injective hroot)

/-! ## Ring switching -/

/-- `1, y^(2^k), y^(2^(k+1))` are `K`-independent in `E`. -/
theorem limbs_eq_zero_of_frob (k : ℕ) (hk : k < 192) (a b c : K)
    (h : ofK a + ofK b * y ^ 2 ^ k + ofK c * (y ^ 2 ^ k) ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hy : (y ^ 2 ^ k) ^ 2 ^ (192 - k) = y := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hk.le, E.pow_two_pow_oneNinetyTwo]
  have h' : (ofK a + ofK b * y ^ 2 ^ k + ofK c * (y ^ 2 ^ k) ^ 2) ^ 2 ^ (192 - k) = 0 := by
    rw [h, zero_pow (pow_ne_zero _ two_ne_zero)]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow,
    pow_right_comm (y ^ 2 ^ k) 2 (2 ^ (192 - k)), hy, ← ofK_pow, ← ofK_pow, ← ofK_pow,
    ← ofLimbs_eq] at h'
  have h0 := congrArg (fun z : E ↦ z.limb 0) h'
  have h1 := congrArg (fun z : E ↦ z.limb 1) h'
  have h2 := congrArg (fun z : E ↦ z.limb 2) h'
  simp only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hn : 2 ^ (192 - k) ≠ 0 := pow_ne_zero _ two_ne_zero
  exact ⟨(pow_eq_zero_iff hn).mp h0, (pow_eq_zero_iff hn).mp h1, (pow_eq_zero_iff hn).mp h2⟩

/-- The Frobenius `x ↦ x^(2^k)` on limbs. -/
private theorem frob_limbs (x : E) (k : ℕ) :
    x ^ 2 ^ k = ofK (x.limb 0 ^ 2 ^ k) + ofK (x.limb 1 ^ 2 ^ k) * y ^ 2 ^ k +
      ofK (x.limb 2 ^ 2 ^ k) * (y ^ 2 ^ k) ^ 2 := by
  conv_lhs => rw [E.eq_sum_limbs x]
  rw [add_pow_char_pow, add_pow_char_pow, mul_pow, mul_pow, pow_right_comm y 2 (2 ^ k),
    ofK_pow, ofK_pow, ofK_pow]

/-- **Ring-switching injectivity** (Annex A, §A.3): a family of `E` whose sums
`Σ_i x^i · δ_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem ringSwitch_injective (δ : Fin 64 → E)
    (h : ∀ k < 64, ∑ i : Fin 64, algebraMap K E (g ^ i.val) * δ i ^ 2 ^ k = 0) :
    ∀ i, δ i = 0 := by
  have hsplit : ∀ k < 64, (∑ i : Fin 64, g ^ i.val * (δ i).limb 0 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 1 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 2 ^ 2 ^ k) = 0 := by
    intro k hk
    apply limbs_eq_zero_of_frob k (by omega)
    have e : ∀ i : Fin 64, algebraMap K E (g ^ i.val) * δ i ^ 2 ^ k =
        ofK (g ^ i.val * (δ i).limb 0 ^ 2 ^ k) +
          ofK (g ^ i.val * (δ i).limb 1 ^ 2 ^ k) * y ^ 2 ^ k +
          ofK (g ^ i.val * (δ i).limb 2 ^ 2 ^ k) * (y ^ 2 ^ k) ^ 2 := by
      intro i
      rw [frob_limbs (δ i) k, ofK_mul, ofK_mul, ofK_mul]
      change ofK (g ^ i.val) * _ = _
      ring
    rw [← h k hk, Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ofK_sum, ofK_sum, ofK_sum]
  have ha := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 0) fun k hk ↦ (hsplit k hk).1
  have hb := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 1) fun k hk ↦ (hsplit k hk).2.1
  have hc := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 2) fun k hk ↦ (hsplit k hk).2.2
  intro i
  refine E.ext fun j ↦ ?_
  rw [limb_zero]
  fin_cases j
  exacts [ha i, hb i, hc i]

end
end LeanVM.Protocol.Ring
