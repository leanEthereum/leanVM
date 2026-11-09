/-
  LeanVM.Protocol.RingFields

  The facts about leanVM's fields that ring switching rests on: a word of `K` is its bits packed
  by the powers of `x`, the Frobenius periods, the injectivity of ring switching over
  `E = K[y]/(y^2 + x·y + 1)`, and the count of the challenges at which the drawn map misses a
  wrong claim.
-/

module

public import LeanVM.Parameters.Field
public import LeanVM.Protocol.ToArkLib.FrobeniusMap
import Mathlib.Algebra.CharP.Reduced
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Field facts for ring switching

Ring switching (`doc/leanvm/body/a-ring-switching.tex`, §A.3 and §A.4;
`crates/verifier/src/ring_switch.rs` at leanVM `f128`) packs the `64` bit slices of `q_keccak` by
the powers of `x = g` and draws a random `F_2`-linear map `Φ` of support `{0, …, 63}`. Its
soundness rests on facts about `K = GF(2^64)` and `E = K[y]/(y^2 + x·y + 1)`
(`LeanVM.Parameters.Field`):

* `K.eq_sum_bits`: a word of `K` is its bits packed by the powers of `x`,
  `a = Σ_{i < 64} a_i · x^i` (through CompPoly's bridge to `GF(2)[X] / (X^64 + X^4 + X^3 + X + 1)`).
* **Ring-switching injectivity**, `ringSwitch_injective` (§A.3): a family `δ : Fin 64 → E` with
  `Σ_i x^i · δ_i^(2^k) = 0` for every `k < 64` is zero. Two steps: `limbs_eq_zero_of_frob`
  (`1, y^(2^k)` is a `K`-basis of `E`: `y^(2^k) ∉ K`, since the Frobenius maps `K` onto itself and
  is injective, and `y ∉ K`; so `a + b·y^(2^k) = 0` forces `b = 0`, then `a = 0`), and
  `eq_zero_of_frob_sums_K` (the polynomial `Σ_i d_i X^i`, of degree below 64, vanishes at the 64
  conjugates `x^(2^m)` of `x = g`, distinct by `g_conj_injective`, a kernel check on `K` words).
* **Soundness of the drawn map** (§A.4), `card_ringSwitch_zero_le`: for a nonzero error family
  `δ`, `Σ_i x^i Φ(δ_i) = 0` holds at no more than `2·|E|^15` of the `|E|^16` challenges
  `(f, g) ∈ E^8 × E^8`, `Φ = frobPhi 8 f g` (`ToArkLib/FrobeniusMap.lean`); as a fraction,
  `2/|E|` (`ringSwitch_zero_ratio_le`). Injectivity gives a nonzero `π_k`, `k = 8p + b < 64`,
  and each stage is linear in its own challenges.

The declarations live in `LeanVM.Protocol.Ring`.
-/

namespace LeanVM.Protocol.Ring

open LeanVM.Parameters CompPoly.Extension Finset
open scoped ENNReal

@[expose] public section

/-- `|E| = 2^128`, counted with `Nat.card`. -/
theorem natCard_E : Nat.card E = 2 ^ 128 := by
  rw [Ext.nat_card_ext]
  rfl

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
  let := Fintype.ofFinite K
  have h := FiniteField.pow_card a
  -- `simp only`, not `rw`: a goal mentioning `Fintype.card K` makes the elaborator enumerate `K`.
  simp only [BF64.card_bf64] at h
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

/-! ## The limbs of `E` -/

/-- `y ∉ K`. -/
theorem y_ne_ofK (a : K) : y ≠ ofK a := by
  intro h
  have h1 : Ext.coeff (Ext.gen : E) ⟨1, eParams.two_le⟩ =
      Ext.coeff (ofK a) ⟨1, eParams.two_le⟩ := congrArg (fun z : E ↦ Ext.coeff z _) h
  rw [Ext.coeff_gen, Ext.coeff_ofBase] at h1
  simp at h1

/-- `y^(2^k) ∉ K`: the Frobenius maps `K` onto itself and is injective on `E`. -/
theorem y_frob_ne_ofK (k : ℕ) (a : K) : y ^ 2 ^ k ≠ ofK a := by
  intro h
  obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp (iterateFrobenius_inj K 2 k)) a
  rw [iterateFrobenius_def] at hc
  rw [← hc, ofK_pow] at h
  exact y_ne_ofK c (iterateFrobenius_inj E 2 k (by simpa only [iterateFrobenius_def] using h))

/-- `1, y^(2^k)` are `K`-independent in `E`. -/
theorem limbs_eq_zero_of_frob (k : ℕ) (a b : K) (h : ofK a + ofK b * y ^ 2 ^ k = 0) :
    a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    refine ⟨ofK_injective ?_, rfl⟩
    simpa using h
  · refine absurd ?_ (y_frob_ne_ofK k (-a * b⁻¹))
    have hb' : ofK b ≠ 0 := fun h0 ↦ hb (ofK_injective (h0.trans (map_zero (algebraMap K E)).symm))
    change _ = algebraMap K E (-a * b⁻¹)
    rw [map_mul, map_neg, map_inv₀]
    change _ = -ofK a * (ofK b)⁻¹
    field_simp
    linear_combination h

/-- The Frobenius `x ↦ x^(2^k)` on limbs. -/
theorem frob_limbs (x : E) (k : ℕ) :
    x ^ 2 ^ k = ofK (x.limb 0 ^ 2 ^ k) + ofK (x.limb 1 ^ 2 ^ k) * y ^ 2 ^ k := by
  conv_lhs => rw [E.eq_sum_limbs x]
  rw [add_pow_char_pow, mul_pow, ofK_pow, ofK_pow]

/-! ## Ring switching -/

/-- The packing weights `x^i`, `i < 64`, in `E`. -/
def ringW (i : Fin 64) : E := algebraMap K E (g ^ i.val)

/-- **Ring-switching injectivity** (Annex A, §A.3): a family of `E` whose sums
`Σ_i x^i · δ_i^(2^k)` vanish for every `k < 64` is zero. -/
theorem ringSwitch_injective (δ : Fin 64 → E)
    (h : ∀ k < 64, ∑ i : Fin 64, ringW i * δ i ^ 2 ^ k = 0) : ∀ i, δ i = 0 := by
  have hsplit : ∀ k < 64, (∑ i : Fin 64, g ^ i.val * (δ i).limb 0 ^ 2 ^ k) = 0 ∧
      (∑ i : Fin 64, g ^ i.val * (δ i).limb 1 ^ 2 ^ k) = 0 := by
    intro k hk
    apply limbs_eq_zero_of_frob k
    have e : ∀ i : Fin 64, ringW i * δ i ^ 2 ^ k =
        ofK (g ^ i.val * (δ i).limb 0 ^ 2 ^ k) +
          ofK (g ^ i.val * (δ i).limb 1 ^ 2 ^ k) * y ^ 2 ^ k := by
      intro i
      rw [frob_limbs (δ i) k, ofK_mul, ofK_mul]
      change ofK (g ^ i.val) * _ = _
      ring
    rw [← h k hk, Finset.sum_congr rfl fun i _ ↦ e i, Finset.sum_add_distrib,
      ← Finset.sum_mul, ofK_sum, ofK_sum]
  have ha := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 0) fun k hk ↦ (hsplit k hk).1
  have hb := eq_zero_of_frob_sums_K (fun i ↦ (δ i).limb 1) fun k hk ↦ (hsplit k hk).2
  intro i
  refine Ext.ext fun j ↦ ?_
  rw [show Ext.coeff (0 : E) j = 0 from Ext.coeff_zero (P := eParams) j]
  fin_cases j
  exacts [ha i, hb i]

/-- A nonzero error family leaves a nonzero pairing `π_{8p + b}`, `p, b < 8`. -/
theorem exists_frobPair_ne {δ : Fin 64 → E} (hδ : δ ≠ 0) :
    ∃ p : Fin 8, ∃ b : Fin 8, frobPair univ ringW δ (8 * p + b) ≠ 0 := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  refine hδ (funext (ringSwitch_injective δ fun k hk ↦ ?_))
  have h := hall ⟨k / 8, by omega⟩ ⟨k % 8, by omega⟩
  rwa [frobPair, show 8 * (k / 8) + k % 8 = k from Nat.div_add_mod k 8] at h

/-- **Ring switching's soundness, counting form** (Annex A, §A.4): for a nonzero error family
`δ`, the drawn map `Φ = frobPhi 8 f g` cancels `Σ_i x^i Φ(δ_i)` at no more than `2·|E|^15` of
the challenges `(f, g)`. -/
theorem card_ringSwitch_zero_le {δ : Fin 64 → E} (hδ : δ ≠ 0) :
    Nat.card {fg : (Fin 8 → E) × (Fin 8 → E) //
      ∑ i, ringW i * frobPhi 8 fg.1 fg.2 (δ i) = 0} ≤ 2 * Nat.card E ^ 15 := by
  classical
  let := Fintype.ofFinite E
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card]
  exact card_frobPhi_zero_le univ ringW δ 8 (exists_frobPair_ne hδ)

/-- **Ring switching's soundness**: for a nonzero error family, the fraction of the challenges
`(f, g) ∈ E^8 × E^8` at which `Σ_i x^i Φ(δ_i) = 0` is at most `2/|E|`. -/
theorem ringSwitch_zero_ratio_le {δ : Fin 64 → E} (hδ : δ ≠ 0) :
    (Nat.card {fg : (Fin 8 → E) × (Fin 8 → E) //
        ∑ i, ringW i * frobPhi 8 fg.1 fg.2 (δ i) = 0} : ℝ≥0∞) /
      (Nat.card ((Fin 8 → E) × (Fin 8 → E)) : ℝ≥0∞) ≤ 2 / (Nat.card E : ℝ≥0∞) := by
  have hc : Nat.card ((Fin 8 → E) × (Fin 8 → E)) = Nat.card E * Nat.card E ^ 15 := by
    simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin]
    rw [← pow_add, ← pow_succ']
  have hE : (Nat.card E : ℝ≥0∞) ≠ 0 := by rw [natCard_E]; positivity
  have hE' : (Nat.card E : ℝ≥0∞) ^ 15 ≠ 0 := pow_ne_zero _ hE
  have hT : (Nat.card E : ℝ≥0∞) ^ 15 ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  rw [hc, Nat.cast_mul, Nat.cast_pow]
  calc _ ≤ ((2 * Nat.card E ^ 15 : ℕ) : ℝ≥0∞) / ((Nat.card E : ℝ≥0∞) * (Nat.card E : ℝ≥0∞) ^ 15) := by
        gcongr
        exact_mod_cast card_ringSwitch_zero_le hδ
    _ = 2 / (Nat.card E : ℝ≥0∞) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_div_mul_right _ _ hE' hT]

end
end LeanVM.Protocol.Ring
