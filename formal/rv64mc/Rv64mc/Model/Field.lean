module

public import Rv64mc.Model.Clmul
public import Statement.LeanVmVerifier
import Mathlib.Tactic.LinearCombination

/-!
# `field.rs` as the Rust computes it

Mirrors of `crates/verifier/src/field.rs` on machine words: a `u64` is a `BitVec 64`, a `u128` a
`BitVec 128`, and an `E` the pair of its limbs `(c0, c1)` (`Limbs`), each mirror following the
Rust's steps and loops. Each is proved equal to the statement's operation on `K` (CompPoly's
`BF64`) or `E` (`Ext eParams`), through `limbs`:

* `clmul` is the carry-less product (`clmul_eq`), `reduce` is `BF64.reduce` (`reduce_eq`), so
  `baseMul` and `K * K` are `K` multiplication (`baseMul_eq`), `kSquare` the square, `kInv` the
  inverse (`kInv_eq`), `timesX` the product by `x` (`timesX_eq`);
* `eAdd`, `eMul` (Karatsuba), `eMulK`, `eSquare`, `ePow`, `eInv` and `eSum` are `E`'s sum,
  product, product by `K`, square, power, inverse and `sumE` (`eMul_eq`, ...); `frobenius` is the
  conjugation the inverse uses (`frobenius_eq`);
* `scaledNew` and `scaledMul` are `Scaled::new` and `Scaled::mul`, the product by a fixed `r`
  through tables (`scaledMul_eq`), and `powersM` is `powers` (`powersM_eq`).

A limb identity is proved in the quotient `GF(2)[X]/(x^64 + x^4 + x^3 + x + 1)`: a reduced
carry-less expression is the `K` word with the same class (`reduce_eq_of_mk`), and the `K`
algebra after that is a ring identity in characteristic two.
-/

namespace Rv64mc.Model

open CompPoly.Extension LeanVM.Parameters BinaryField

@[expose] public section

/-! ## The limbs of `E` -/

/-- An `E` as the Rust holds it: `c0`, `c1`. -/
abbrev Limbs : Type := BitVec 64 × BitVec 64

/-- The limbs of a word. -/
def limbs (x : E) : Limbs := ((x.limb 0).toBitVec, (x.limb 1).toBitVec)

/-- `E::new(c0, c1)`: the word of two limbs. -/
def ofLimbsW (w : Limbs) : E := E.ofLimbs (BF64.ofBitVec w.1) (BF64.ofBitVec w.2)

/-- `y`, the adjoined root. -/
abbrev ey : E := Ext.gen

/-- `x`, the generator `g` of `K`, in `E`. -/
abbrev ex : E := ofK g

/-- `E` has characteristic two, as its base field does. -/
instance instCharPE : CharP E 2 := charP_of_injective_algebraMap' (R := K) (A := E) 2

theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

theorem E.ext {x z : E} (h : ∀ i, x.limb i = z.limb i) : x = z := Ext.ext h

@[simp] theorem limb_ofLimbs (c0 c1 : K) (i : Fin 2) :
    (E.ofLimbs c0 c1).limb i = ![c0, c1] i := by
  fin_cases i <;> rfl

@[simp] private theorem limb_ofK (a : K) (i : Fin 2) :
    (ofK a).limb i = if (i : ℕ) = 0 then a else 0 :=
  Ext.coeff_ofBase (P := eParams) a i

private theorem ofK_injective : Function.Injective ofK := fun a b h ↦ by
  simpa using congrArg (·.limb 0) h

private theorem limb_add (x z : E) (i : Fin 2) : (x + z).limb i = x.limb i + z.limb i :=
  Ext.coeff_add x z i

private theorem ey_sq : ey ^ 2 = ex * ey + 1 := by
  have h : Polynomial.aeval ey ePoly = 0 := by rw [← eParams_poly]; exact Ext.aeval_gen_poly
  simp only [ePoly, map_add, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_one,
    Ext.algebraMap_eq_ofBase] at h
  rw [← sub_eq_zero, CharTwo.sub_eq_add, ← add_assoc]
  exact h

private theorem eq_sum_limbs (x : E) : x = ofK (x.limb 0) + ofK (x.limb 1) * ey := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot x = ∑ i : Fin 2,
      algebraMap K (AdjoinRoot eParams.poly) (x.limb i) * Ext.rt eParams ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_two]
  simp

private theorem ofLimbs_eq (c0 c1 : K) : E.ofLimbs c0 c1 = ofK c0 + ofK c1 * ey := by
  conv_lhs => rw [eq_sum_limbs (E.ofLimbs c0 c1)]
  simp

private theorem ofLimbs_limb (x : E) : E.ofLimbs (x.limb 0) (x.limb 1) = x :=
  E.ext fun i ↦ by fin_cases i <;> simp

private theorem mul_limbs (a0 a1 b0 b1 : K) :
    E.ofLimbs a0 a1 * E.ofLimbs b0 b1 =
      E.ofLimbs (a0 * b0 + a1 * b1) (a0 * b1 + a1 * b0 + g * (a1 * b1)) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  linear_combination (ofK a1 * ofK b1) * ey_sq

theorem limbs_ofLimbs (a b : K) : limbs (E.ofLimbs a b) = (a.toBitVec, b.toBitVec) := by
  simp [limbs]

theorem ofLimbsW_limbs (x : E) : ofLimbsW (limbs x) = x := ofLimbs_limb x

theorem limbs_ofK (a : K) : limbs (ofK a) = (a.toBitVec, 0#64) := by
  simp [limbs]

theorem toBitVec_add (a b : K) : (a + b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl

/-! ## The reduction, through the quotient -/

private theorem toQuot_eq (a : K) :
    BF64.toQuot a = AdjoinRoot.mk BF64.basePoly (toPoly a.toBitVec) := rfl

private theorem toQuot_g : BF64.toQuot g = AdjoinRoot.mk BF64.basePoly Polynomial.X := by
  rw [toQuot_eq,
    show toPoly g.toBitVec = Polynomial.X ^ 1 from toPoly_one_shiftLeft (w := 64) 1 (by norm_num),
    pow_one]

/-- The `K` word `BF64.reduce x` is the class of `x`. -/
private theorem toQuot_reduce (x : BitVec 128) :
    BF64.toQuot (BF64.ofBitVec (BF64.reduce x)) = AdjoinRoot.mk BF64.basePoly (toPoly x) := by
  rw [toQuot_eq, BF64.toBitVec_ofBitVec, BF64.toPoly_reduce, AdjoinRoot.mk_eq_mk]
  exact ⟨-(toPoly x / BF64.basePoly), by rw [EuclideanDomain.mod_eq_sub_mul_div]; ring⟩

/-- **A reduced 128-bit word is the `K` word of its class.** -/
private theorem reduce_eq_of_mk (x : BitVec 128) (k : K)
    (h : AdjoinRoot.mk BF64.basePoly (toPoly x) = BF64.toQuot k) :
    BF64.reduce x = k.toBitVec := by
  have : BF64.ofBitVec (BF64.reduce x) = k := BF64.toQuot_injective (by rw [toQuot_reduce, h])
  rw [← this]
  rfl

/-- The carry-less product as one 128-bit word. -/
def cl (a b : BitVec 64) : BitVec 128 := carryLessMul (w := 128) a b

private theorem toPoly_cl (a b : BitVec 64) : toPoly (cl a b) = toPoly a * toPoly b :=
  toPoly_carryLessMul a b (by norm_num)

/-- A carry-less product of 64-bit words has degree at most `126`. -/
private theorem cl_lt (a b : BitVec 64) : (cl a b).toNat < 2 ^ 127 := by
  apply BitVec_lt_two_pow_of_toPoly_degree_lt
  rw [toPoly_cl]
  have ha := toPoly_degree_of_lt_two_pow a (d := 64) a.isLt
  have hb := toPoly_degree_of_lt_two_pow b (d := 64) b.isLt
  rcases eq_or_ne (toPoly a) 0 with h0 | h0
  · rw [h0, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  rcases eq_or_ne (toPoly b) 0 with h1 | h1
  · rw [h1, mul_zero, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
  rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree h0,
    Polynomial.degree_eq_natDegree h1]
  rw [Polynomial.degree_eq_natDegree h0] at ha
  rw [Polynomial.degree_eq_natDegree h1] at hb
  have ha' : (toPoly a).natDegree < 64 := by exact_mod_cast ha
  have hb' : (toPoly b).natDegree < 64 := by exact_mod_cast hb
  rw [← Nat.cast_add]
  exact_mod_cast (show (toPoly a).natDegree + (toPoly b).natDegree < 127 by omega)

private theorem toPoly_cl_shl (a b : BitVec 64) :
    toPoly (cl a b <<< 1) = toPoly a * toPoly b * Polynomial.X := by
  rw [toPoly_shiftLeft_no_overflow _ (cl_lt a b) (by norm_num), toPoly_cl, pow_one]

/-- Rewrite a reduced carry-less expression into the quotient, then compare by `ring`. -/
macro "limb_quot" : tactic => `(tactic| (
  apply reduce_eq_of_mk
  simp only [BF64.toQuot_add, BF64.toQuot_mul, toQuot_g]
  simp only [toPoly_xor, toPoly_cl, toPoly_cl_shl, map_add, map_mul, toQuot_eq]
  all_goals ring))

/-! ## `K`: `clmul`, `reduce`, `base_mul` -/

/-- `clmul(a, b)`: the high half is the low half of the bit-reversed operands' product,
reversed back and shifted; `(high as u128) << 64 | low as u128`. -/
def clmul (a b : BitVec 64) : BitVec 128 :=
  let low := clmulLow a b
  let high := (clmulLow a.reverse b.reverse).reverse >>> 1
  high.setWidth 128 <<< 64 ||| low.setWidth 128

private theorem u128_eq_append (hi lo : BitVec 64) :
    hi.setWidth 128 <<< 64 ||| lo.setWidth 128 = hi ++ lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp [h, hi']
  · simp [h, BitVec.getLsbD_of_ge lo i (by omega), hi', show i - 64 < 128 by omega]

/-- `reduce(p)`: fold the high word by `x^64 = x^4 + x^3 + x + 1` twice, the second fold's
spill being the high word's top bits. -/
def reduce (p : BitVec 128) : BitVec 64 :=
  let lo := p.setWidth 64
  let hi := (p >>> 64).setWidth 64
  let spill := (hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60)
  let v := hi ^^^ spill
  lo ^^^ v ^^^ (v <<< 1) ^^^ (v <<< 3) ^^^ (v <<< 4)

/-- `base_mul(a, b)`. -/
def baseMul (a b : BitVec 64) : BitVec 64 := reduce (clmul a b)

private theorem card_pairs_reverse (a b : BitVec 64) (k : ℕ) (hk : k ≤ 126) :
    (pairs a.reverse b.reverse k).card = (pairs a b (126 - k)).card := by
  apply Finset.card_nbij' (fun uv ↦ (63 - uv.1, 63 - uv.2)) (fun uv ↦ (63 - uv.1, 63 - uv.2))
  · intro uv huv
    have huv := Finset.mem_coe.1 huv
    simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, Bool.and_eq_true, decide_eq_true_eq] at huv
    rw [Finset.mem_coe]
    simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet]
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · rw [show 63 - uv.1 = 64 - 1 - uv.1 by omega]; exact huv.1.1.2
    · rw [show 63 - uv.2 = 64 - 1 - uv.2 by omega]; exact huv.1.2.2
  · intro uv huv
    have huv := Finset.mem_coe.1 huv
    simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet] at huv
    have := BitVec.lt_of_getLsbD huv.1.1
    have := BitVec.lt_of_getLsbD huv.1.2
    rw [Finset.mem_coe]
    simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, by omega⟩
    · rw [show 64 - 1 - (63 - uv.1) = uv.1 by omega]; exact huv.1.1
    · rw [show 64 - 1 - (63 - uv.2) = uv.2 by omega]; exact huv.1.2
  · intro uv huv
    have huv := Finset.mem_coe.1 huv
    simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD, Bool.and_eq_true, decide_eq_true_eq] at huv
    ext <;> simp <;> omega
  · intro uv huv
    have huv := Finset.mem_coe.1 huv
    simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet] at huv
    have := BitVec.lt_of_getLsbD huv.1.1
    have := BitVec.lt_of_getLsbD huv.1.2
    ext <;> simp <;> omega

private theorem pairs_eq_empty (a b : BitVec 64) (k : ℕ) (hk : 126 < k) : pairs a b k = ∅ := by
  ext uv
  simp only [pairs, Finset.mem_filter, Finset.mem_product, mem_bitSet, Finset.notMem_empty,
    iff_false, not_and]
  intro h1 h2
  have := BitVec.lt_of_getLsbD h1.1
  have := BitVec.lt_of_getLsbD h1.2
  omega

/-- **`clmul` is the carry-less product.** -/
theorem clmul_eq (a b : BitVec 64) : clmul a b = cl a b := by
  rw [clmul, u128_eq_append]
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_append, cl, getLsbD_carryLessMul]
  by_cases hp64 : p < 64
  · simp only [hp64, ↓reduceIte]
    exact getLsbD_clmulLow a b p hp64
  · simp only [hp64, ↓reduceIte, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse,
      BitVec.getMsbD_eq_getLsbD]
    by_cases hp127 : p = 127
    · subst hp127
      simp [pairs_eq_empty a b 127 (by norm_num)]
    · rw [show 1 + (p - 64) = p - 63 by omega, decide_eq_true (show p - 63 < 64 by omega),
        Bool.true_and, getLsbD_clmulLow _ _ _ (by omega), card_pairs_reverse _ _ _ (by omega),
        show 126 - (64 - 1 - (p - 63)) = p by omega]

private theorem setWidth_ushiftRight_append (p : BitVec 128) :
    (p >>> 64).setWidth 64 ++ p.setWidth 64 = p := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp [h]
  · simp [h, show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega]

/-- **`reduce` is `BF64.reduce`.** -/
theorem reduce_eq (p : BitVec 128) : reduce p = BF64.reduce p := by
  have h := BF64.reduceWords_eq ⟨(p >>> 64).setWidth 64⟩ ⟨p.setWidth 64⟩
  simp only [BF64.wordsToBitVec] at h
  rw [setWidth_ushiftRight_append] at h
  rw [← h]
  simp only [reduce, BF64.reduceWords, BF64.tailLow, BF64.tailHigh, UInt64.toBitVec_xor,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight]
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.toNat_umod,
    UInt64.toNat_toBitVec, UInt64.reduceToNat, BitVec.shiftLeft_xor_distrib]
  ac_rfl

/-- **`base_mul` is `K` multiplication.** -/
theorem baseMul_eq (a b : K) : baseMul a.toBitVec b.toBitVec = (a * b).toBitVec := by
  rw [baseMul, clmul_eq, reduce_eq]
  exact (BF64.toBitVec_mul a b).symm

/-! ## `spread` and `K::square` -/

/-- `spread(a)`: the bits of `a` to the even positions of a 128-bit word. -/
def spread (a : BitVec 64) : BitVec 128 :=
  let x := a.setWidth 128
  let x := (x ||| x <<< 32) &&& 0x00000000FFFFFFFF00000000FFFFFFFF#128
  let x := (x ||| x <<< 16) &&& 0x0000FFFF0000FFFF0000FFFF0000FFFF#128
  let x := (x ||| x <<< 8) &&& 0x00FF00FF00FF00FF00FF00FF00FF00FF#128
  let x := (x ||| x <<< 4) &&& 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128
  let x := (x ||| x <<< 2) &&& 0x33333333333333333333333333333333#128
  (x ||| x <<< 1) &&& 0x55555555555555555555555555555555#128

/-- After the step of shift `s`, bit `k` (with `k % 2s < s`) holds bit `(k / 2s) s + k % 2s` of
`a`, and the other bits are clear. -/
private def Spread (a : BitVec 64) (s : ℕ) (x : BitVec 128) : Prop :=
  ∀ k, x.getLsbD k =
    (decide (k < 128) && decide (k % (2 * s) < s) && a.getLsbD (k / (2 * s) * s + k % (2 * s)))

private theorem spread_start (a : BitVec 64) : Spread a 64 (a.setWidth 128) := by
  intro k
  rw [BitVec.getLsbD_setWidth]
  by_cases hk : k < 128
  · rw [show k % (2 * 64) = k by omega, show k / (2 * 64) = 0 by omega]
    by_cases h : k < 64
    · simp [hk, h]
    · simp [hk, h, BitVec.getLsbD_of_ge a k (by omega)]
  · simp [hk, BitVec.getLsbD_of_ge a k (by omega)]

private theorem spread_step (a : BitVec 64) (s : ℕ) (x m : BitVec 128)
    (hs : s = 32 ∨ s = 16 ∨ s = 8 ∨ s = 4 ∨ s = 2 ∨ s = 1)
    (hm : ∀ k : Fin 128, m.getLsbD k = decide (k.val % (2 * s) < s)) (hx : Spread a (2 * s) x) :
    Spread a s ((x ||| x <<< s) &&& m) := by
  intro k
  by_cases hk : k < 128
  · have hmk := hm ⟨k, hk⟩
    simp only at hmk
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, hx, hx, hmk]
    by_cases h1 : k % (2 * s) < s <;> by_cases h2 : k % (2 * (2 * s)) < 2 * s <;>
      by_cases h3 : k < s <;> simp [h1, h2, h3, hk]
    · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
    · have h4 : ¬ (k - s) % (2 * (2 * s)) < 2 * s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [h4, decide_false, Bool.and_false, Bool.false_and, Bool.or_false]
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
    · exfalso; rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have h4 : (k - s) % (2 * (2 * s)) < 2 * s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      simp only [h4, decide_true, show k - s < 128 by omega, Bool.true_and]
      rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> (congr 1; omega)
  · rw [BitVec.getLsbD_of_ge _ k (by omega)]; simp [hk]

private theorem mask32 : ∀ k : Fin 128, (0x00000000FFFFFFFF00000000FFFFFFFF#128).getLsbD k =
    decide (k.val % (2 * 32) < 32) := by decide +kernel

private theorem mask16 : ∀ k : Fin 128, (0x0000FFFF0000FFFF0000FFFF0000FFFF#128).getLsbD k =
    decide (k.val % (2 * 16) < 16) := by decide +kernel

private theorem mask8 : ∀ k : Fin 128, (0x00FF00FF00FF00FF00FF00FF00FF00FF#128).getLsbD k =
    decide (k.val % (2 * 8) < 8) := by decide +kernel

private theorem mask4 : ∀ k : Fin 128, (0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128).getLsbD k =
    decide (k.val % (2 * 4) < 4) := by decide +kernel

private theorem mask2 : ∀ k : Fin 128, (0x33333333333333333333333333333333#128).getLsbD k =
    decide (k.val % (2 * 2) < 2) := by decide +kernel

private theorem mask1 : ∀ k : Fin 128, (0x55555555555555555555555555555555#128).getLsbD k =
    decide (k.val % (2 * 1) < 1) := by decide +kernel

private theorem spread_spread (a : BitVec 64) : Spread a 1 (spread a) :=
  spread_step a 1 _ _ (by simp) mask1 <| spread_step a 2 _ _ (by simp) mask2 <|
    spread_step a 4 _ _ (by simp) mask4 <| spread_step a 8 _ _ (by simp) mask8 <|
    spread_step a 16 _ _ (by simp) mask16 <| spread_step a 32 _ _ (by simp) mask32 <|
    spread_start a

/-- **`spread` is the carry-less square.** -/
theorem spread_eq (a : BitVec 64) : spread a = cl a a := by
  have h := spread_spread a
  have hbit : ∀ k, (spread a).getLsbD k =
      (decide (k < 128) && decide (k % 2 = 0) && a.getLsbD (k / 2)) := by
    intro k
    rw [h k]
    by_cases hk : k % 2 = 0
    · simp [hk]
    · simp [hk, show ¬ k % (2 * 1) < 1 by omega]
  apply BF64.bitVec_toPoly_injective
  rw [cl, toPoly_carryLessMul _ _ (by norm_num), ← sq, ← ZMod.expand_card]
  ext n
  rw [toPoly_coeff, coeff_bit, Polynomial.coeff_expand (by norm_num), toPoly_coeff, coeff_bit,
    hbit n]
  by_cases hn : n % 2 = 0
  · have h2 : 2 ∣ n := Nat.dvd_of_mod_eq_zero hn
    by_cases hk : n < 128
    · simp [hn, hk, h2]
    · simp [hk, h2, BitVec.getLsbD_of_ge a (n / 2) (by omega)]
  · have h2 : ¬ 2 ∣ n := fun h ↦ hn (Nat.mod_eq_zero_of_dvd h)
    simp [hn, h2]

/-- `K::square`: `reduce(spread(self))`. -/
def kSquare (a : BitVec 64) : BitVec 64 := reduce (spread a)

/-- **`K::square` is the square.** -/
theorem kSquare_eq (a : K) : kSquare a.toBitVec = (a * a).toBitVec := by
  rw [kSquare, reduce_eq, spread_eq]
  exact (BF64.toBitVec_mul a a).symm

/-! ## `K::inv` -/

/-- The closure `sq(v, n)`: `for _ in 0..n { v = v.square() }`. -/
def kSq (v : BitVec 64) (n : ℕ) : BitVec 64 := (List.range n).foldl (fun v _ ↦ kSquare v) v

/-- `K::inv`: `self^(2^64 - 2)` by Itoh-Tsujii, each `t_k = self^(2^k - 1)`. -/
def kInv (a : BitVec 64) : BitVec 64 :=
  let t1 := a
  let t2 := baseMul (kSq t1 1) t1
  let t3 := baseMul (kSq t2 1) t1
  let t6 := baseMul (kSq t3 3) t3
  let t12 := baseMul (kSq t6 6) t6
  let t24 := baseMul (kSq t12 12) t12
  let t48 := baseMul (kSq t24 24) t24
  let t60 := baseMul (kSq t48 12) t12
  let t63 := baseMul (kSq t60 3) t3
  kSq t63 1

private theorem kSq_succ (v : BitVec 64) (n : ℕ) : kSq v (n + 1) = kSquare (kSq v n) := by
  rw [kSq, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ← kSq]

theorem kSq_eq (a : K) (n : ℕ) : kSq a.toBitVec n = (a ^ 2 ^ n).toBitVec := by
  induction n with
  | zero => simp [kSq]
  | succ n ih => rw [kSq_succ, ih, kSquare_eq, ← sq, ← pow_mul, pow_succ]

private theorem chain_step {a x y : K} {n m k : ℕ} (hx : x = a ^ (2 ^ n - 1))
    (hy : y = a ^ (2 ^ m - 1))
    (hk : n + m = k) : x ^ 2 ^ m * y = a ^ (2 ^ k - 1) := by
  subst hx hy hk
  rw [← pow_mul, ← pow_add]
  congr 1
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [pow_add]
  generalize 2 ^ n = A at *
  generalize 2 ^ m = B at *
  obtain ⟨A, rfl⟩ := Nat.exists_eq_add_of_le' h1
  obtain ⟨B, rfl⟩ := Nat.exists_eq_add_of_le' h2
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-- **`K::inv` is the inverse**, zero to zero. -/
theorem kInv_eq (a : K) : kInv a.toBitVec = a⁻¹.toBitVec := by
  simp only [kInv, kSq_eq, baseMul_eq]
  congr 1
  have e1 : a = a ^ (2 ^ 1 - 1) := by norm_num
  have e2 := chain_step e1 e1 (k := 2) rfl
  have e3 := chain_step e2 e1 (k := 3) rfl
  have e6 := chain_step e3 e3 (k := 6) rfl
  have e12 := chain_step e6 e6 (k := 12) rfl
  have e24 := chain_step e12 e12 (k := 24) rfl
  have e48 := chain_step e24 e24 (k := 48) rfl
  have e60 := chain_step e48 e12 (k := 60) rfl
  have e63 := chain_step e60 e3 (k := 63) rfl
  rw [e63, ← pow_mul]
  by_cases ha : a = 0
  · subst ha
    rw [inv_zero, zero_pow (by norm_num)]
  · apply eq_inv_of_mul_eq_one_right
    have : Fintype K := Fintype.ofFinite K
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [BF64.card_bf64] at h
    rw [← pow_succ', ← h]
    norm_num

/-! ## `times_x` -/

/-- `times_x(value)`: `value << 1 ^ (0u64.wrapping_sub(value >> 63) & 0x1B)`. -/
def timesX (v : BitVec 64) : BitVec 64 := v <<< 1 ^^^ ((0#64 - (v >>> 63)) &&& 0x1B#64)

private theorem cl_two (a : BitVec 64) : cl a 2#64 = (a >>> 63) ++ (a <<< 1) := by
  have h : (a >>> 63) ++ (a <<< 1) = zeroExtendTo (w := 128) a <<< 1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_append, zeroExtendTo, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    rcases (show k < 64 ∨ k = 64 ∨ 64 < k by omega) with h1 | h1 | h1
    · simp [h1, hk, show k - 1 < 128 by omega]
    · subst h1; simp
    · simp [show ¬ k < 64 by omega, hk, show ¬ k < 1 by omega,
        BitVec.getLsbD_of_ge a (63 + (k - 64)) (by omega),
        BitVec.getLsbD_of_ge a (k - 1) (by omega)]
  rw [h]
  apply BF64.bitVec_toPoly_injective
  have hlt : (zeroExtendTo (w := 128) a).toNat < 2 ^ 64 := by
    rw [toNat_zeroExtendTo _ (by omega)]; exact a.isLt
  rw [cl, toPoly_carryLessMul _ _ (by norm_num), toPoly_shiftLeft_no_overflow _ hlt (by norm_num),
    toPoly_zeroExtendTo _ (by norm_num),
    show toPoly 2#64 = Polynomial.X ^ 1 from toPoly_one_shiftLeft (w := 64) 1 (by norm_num)]

private theorem reduce_append (hi lo : BitVec 64) :
    reduce (hi ++ lo) = lo ^^^ (hi ^^^ ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60))) ^^^
      ((hi ^^^ ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60))) <<< 1) ^^^
      ((hi ^^^ ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60))) <<< 3) ^^^
      ((hi ^^^ ((hi >>> 63) ^^^ (hi >>> 61) ^^^ (hi >>> 60))) <<< 4) := by
  have h1 : (hi ++ lo).setWidth 64 = lo := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_append]
    simp [hi']
  have h2 : ((hi ++ lo) >>> 64).setWidth 64 = hi := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
    simp [hi']
  simp only [reduce, h1, h2]

/-- **`times_x` is the product by `x`.** -/
theorem timesX_eq (a : K) : timesX a.toBitVec = (a * g).toBitVec := by
  rw [← baseMul_eq, baseMul, clmul_eq, show g.toBitVec = 2#64 from rfl, cl_two, reduce_append]
  generalize a.toBitVec = v
  have hlt : (v >>> 63).toNat < 2 := by
    have := v.isLt
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    omega
  have hh : v >>> 63 = 0#64 ∨ v >>> 63 = 1#64 := by
    rcases (show (v >>> 63).toNat = 0 ∨ (v >>> 63).toNat = 1 by omega) with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp [h]))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp [h]))
  unfold timesX
  rcases hh with h | h <;> rw [h] <;> simp only [BitVec.xor_assoc] <;> rfl

/-! ## `E`: the constants, `+`, `*`, `From<K>`, `Mul<K>` -/

/-- `ZERO`. -/
def eZero : Limbs := (0#64, 0#64)

/-- `ONE`. -/
def eOne : Limbs := (1#64, 0#64)

/-- `GEN = E::new(2, 0)`. -/
def eGen : Limbs := (2#64, 0#64)

@[simp] private theorem limb_zero (i : Fin 2) : (0 : E).limb i = 0 :=
  Ext.coeff_zero (P := eParams) i

theorem limbs_zero : limbs (0 : E) = eZero := by
  simp [limbs, eZero]

theorem limbs_one : limbs (1 : E) = eOne := by
  rw [show (1 : E) = ofK 1 from rfl, limbs_ofK]
  rfl

theorem limbs_gen : limbs LeanVM.Protocol.Verifier.gen = eGen := by
  rw [LeanVM.Protocol.Verifier.gen, LeanVM.Protocol.Verifier.eOfNat, limbs_ofK]
  rfl

/-- `E + E`. -/
def eAdd (a b : Limbs) : Limbs := (a.1 ^^^ b.1, a.2 ^^^ b.2)

theorem eAdd_eq (x z : E) : eAdd (limbs x) (limbs z) = limbs (x + z) := by
  simp only [eAdd, limbs, limb_add, toBitVec_add]

/-- `From<K> for E`: `E::new(value.0, 0)`. -/
def eOfK (a : BitVec 64) : Limbs := (a, 0#64)

theorem eOfK_eq (a : K) : eOfK a.toBitVec = limbs (ofK a) := (limbs_ofK a).symm

/-- `E * E`: Karatsuba, three base products, then `y^2 = x y + 1` folds `a1 b1 y^2` back, the
`x` a one-bit shift of the 128-bit product. -/
def eMul (a b : Limbs) : Limbs :=
  let p0 := clmul a.1 b.1
  let p1 := clmul a.2 b.2
  let middle := clmul (a.1 ^^^ a.2) (b.1 ^^^ b.2) ^^^ p0 ^^^ p1
  (reduce (p0 ^^^ p1), reduce (middle ^^^ p1 <<< 1))

/-- Every word is `E.ofLimbs` of its limbs. -/
theorem exists_ofLimbs (x : E) : ∃ a b : K, x = E.ofLimbs a b := ⟨_, _, (ofLimbs_limb x).symm⟩

theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 := by
  rw [ofLimbs_eq, show ofK (0 : K) = 0 from map_zero (algebraMap K E), zero_mul, add_zero]

/-- **The Rust's `E` product is `E` multiplication.** -/
theorem eMul_eq (x z : E) : eMul (limbs x) (limbs z) = limbs (x * z) := by
  obtain ⟨a0, a1, rfl⟩ := exists_ofLimbs x
  obtain ⟨b0, b1, rfl⟩ := exists_ofLimbs z
  rw [mul_limbs, limbs_ofLimbs, limbs_ofLimbs, limbs_ofLimbs,
    show a0 * b1 + a1 * b0 + g * (a1 * b1) =
      (a0 + a1) * (b0 + b1) + a0 * b0 + a1 * b1 + a1 * b1 * g by
      linear_combination (-(a0 * b0 + a1 * b1)) * (CharTwo.two_eq_zero : (2 : K) = 0)]
  simp only [eMul, clmul_eq, reduce_eq, Prod.mk.injEq]
  constructor <;> limb_quot

/-- `Mul<K> for E`: each limb times `rhs`. -/
def eMulK (a : Limbs) (k : BitVec 64) : Limbs := (baseMul a.1 k, baseMul a.2 k)

theorem eMulK_eq (x : E) (k : K) : eMulK (limbs x) k.toBitVec = limbs (x * ofK k) := by
  obtain ⟨a0, a1, rfl⟩ := exists_ofLimbs x
  rw [ofK_eq_ofLimbs, mul_limbs, limbs_ofLimbs, limbs_ofLimbs]
  simp only [eMulK, baseMul_eq, mul_zero, add_zero, zero_add]

/-! ## `E::square`, `frobenius`, `pow`, `inv`, `sum` -/

/-- `E::square`: the two limbs' carry-less squares, `y^2 = x y + 1`. -/
def eSquare (a : Limbs) : Limbs :=
  let s0 := spread a.1
  let s1 := spread a.2
  (reduce (s0 ^^^ s1), reduce (s1 <<< 1))

/-- **`E::square` is the square.** -/
theorem eSquare_eq (x : E) : eSquare (limbs x) = limbs (x * x) := by
  obtain ⟨a0, a1, rfl⟩ := exists_ofLimbs x
  rw [mul_limbs, limbs_ofLimbs, limbs_ofLimbs,
    show a0 * a1 + a1 * a0 + g * (a1 * a1) = a1 * a1 * g by
      linear_combination (a0 * a1) * (CharTwo.two_eq_zero : (2 : K) = 0)]
  simp only [eSquare, spread_eq, reduce_eq, Prod.mk.injEq]
  constructor <;> limb_quot

/-- `E::frobenius`: `self^(2^64)`, `K` fixed and `y` to its conjugate `y + x`. -/
def frobenius (a : Limbs) : Limbs := (a.1 ^^^ timesX a.2, a.2)

theorem frobenius_eq (a b : K) :
    frobenius (limbs (E.ofLimbs a b)) = limbs (E.ofLimbs (a + b * g) b) := by
  rw [limbs_ofLimbs, limbs_ofLimbs, frobenius, timesX_eq]
  rfl

/-- `E::pow`'s loop: `out *= base` on a set low bit, then `base` squared and `n >>= 1`. -/
def ePowLoop (base out : Limbs) (n : BitVec 64) : Limbs :=
  if n = 0 then out
  else
    let out := if n &&& 1 = 1 then eMul out base else out
    ePowLoop (eSquare base) out (n >>> 1)
termination_by n.toNat
decreasing_by
  rename_i h
  have : n.toNat ≠ 0 := fun h0 ↦ h (BitVec.eq_of_toNat_eq (by simpa using h0))
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- `E::pow(exponent)`, from `(self, ONE, exponent)`. -/
def ePow (x : Limbs) (exponent : BitVec 64) : Limbs := ePowLoop x eOne exponent

theorem ePowLoop_eq (b o : E) (n : BitVec 64) :
    ePowLoop (limbs b) (limbs o) n = limbs (o * b ^ n.toNat) := by
  induction h : n.toNat using Nat.strong_induction_on generalizing n b o with
  | _ N ih =>
  subst h
  rw [ePowLoop]
  by_cases h0 : n = 0
  · subst h0
    simp
  · rw [ite_eq_right h0]
    have hbit : (if n &&& 1 = 1 then eMul (limbs o) (limbs b) else limbs o) =
        limbs (o * b ^ (n.toNat % 2)) := by
      have hand : (n &&& 1).toNat = n.toNat % 2 := by
        rw [BitVec.toNat_and]; simp [Nat.and_one_is_mod]
      by_cases h1 : n.toNat % 2 = 1
      · rw [ite_eq_left (BitVec.eq_of_toNat_eq (by rw [hand, h1]; rfl)), eMul_eq, h1, pow_one]
      · have h1' : n.toNat % 2 = 0 := by omega
        rw [ite_eq_right (fun h ↦ h1 (by rw [← hand, h]; rfl)), h1', pow_zero, mul_one]
    have hlt : (n >>> 1).toNat < n.toNat := by
      have : n.toNat ≠ 0 := fun h ↦ h0 (BitVec.eq_of_toNat_eq (by simpa using h))
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      omega
    simp only
    have hdiv : (n >>> 1).toNat = n.toNat / 2 := by
      simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hbit, eSquare_eq, ih _ hlt _ _ _ rfl, hdiv, mul_assoc, ← sq, ← pow_mul, ← pow_add,
      show n.toNat % 2 + 2 * (n.toNat / 2) = n.toNat by omega]

/-- **`E::pow` is the power.** -/
theorem ePow_eq (x : E) (exponent : BitVec 64) :
    ePow (limbs x) exponent = limbs (x ^ exponent.toNat) := by
  rw [ePow, ← limbs_one, ePowLoop_eq, one_mul]

/-- `E::inv`: `m` the conjugate, `self * m` in `K` (its limb `0`), and `m` times that norm's
inverse. -/
def eInv (x : Limbs) : Limbs :=
  let m := frobenius x
  let norm := eMul x m
  eMul m (eOfK (kInv norm.1))

/-- The norm: a word times its conjugate lies in `K`. -/
private theorem norm_ofLimbs (a b : K) :
    E.ofLimbs a b * E.ofLimbs (a + b * g) b = ofK (a * (a + b * g) + b * b) := by
  rw [mul_limbs, ofK_eq_ofLimbs]
  congr 1
  linear_combination (a * b + b * b * g) * (CharTwo.two_eq_zero : (2 : K) = 0)

private theorem ofLimbs_eq_zero {a b : K} (h : E.ofLimbs a b = 0) : a = 0 ∧ b = 0 := by
  have h0 := congrArg (·.limb 0) h
  have h1 := congrArg (·.limb 1) h
  simp only [limb_ofLimbs, limb_zero] at h0 h1
  exact ⟨h0, h1⟩

/-- **`E::inv` is the inverse**, zero to zero. -/
theorem eInv_eq (x : E) : eInv (limbs x) = limbs x⁻¹ := by
  obtain ⟨a, b, rfl⟩ := exists_ofLimbs x
  simp only [eInv]
  rw [frobenius_eq, eMul_eq, norm_ofLimbs, limbs_ofK, kInv_eq, eOfK_eq, eMul_eq]
  refine congrArg limbs ?_
  have hN := norm_ofLimbs a b
  generalize a * (a + b * g) + b * b = n at hN
  have hof0 : ofK (0 : K) = 0 := map_zero (algebraMap K E)
  by_cases hx : E.ofLimbs a b = 0
  · have hn : n = 0 := by
      rw [hx, zero_mul, ← hof0] at hN
      exact ofK_injective hN.symm
    rw [hx, inv_zero, hn, inv_zero, hof0, mul_zero]
  · have hn0 : n ≠ 0 := by
      rintro rfl
      rw [hof0] at hN
      rcases mul_eq_zero.1 hN with h | h
      · exact hx h
      · obtain ⟨h0, rfl⟩ := ofLimbs_eq_zero h
        rw [zero_mul, add_zero] at h0
        subst h0
        exact hx (by rw [← ofK_eq_ofLimbs, hof0])
    apply eq_inv_of_mul_eq_one_right
    rw [← mul_assoc, hN, ← ofK_mul, mul_inv_cancel₀ hn0]
    exact map_one (algebraMap K E)

/-- `E::sum(values)`: the fold from `ZERO`. -/
def eSum (values : List Limbs) : Limbs := values.foldl eAdd eZero

private theorem foldl_eAdd (l : List E) (acc : E) :
    (l.map limbs).foldl eAdd (limbs acc) = limbs (l.foldl (· + ·) acc) := by
  induction l generalizing acc with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.foldl_cons, eAdd_eq, ih]

/-- **`E::sum` is `sumE`.** -/
theorem eSum_eq (values : List E) :
    eSum (values.map limbs) = limbs (LeanVM.Protocol.Verifier.sumE values) := by
  rw [eSum, ← limbs_zero, foldl_eAdd]
  rfl

/-! ## `powers` -/

/-- `powers(base, count)`: `for _ in 0..count { out.push(power); power *= base }` from `ONE`. -/
def powersM (base : Limbs) (count : ℕ) : List Limbs :=
  ((List.range count).foldl (fun (st : List Limbs × Limbs) _ ↦ (st.1 ++ [st.2], eMul st.2 base))
    ([], eOne)).1

private theorem powersFrom_succ (acc base : E) (n : ℕ) :
    LeanVM.Protocol.Verifier.powersFrom acc base (n + 1) =
      LeanVM.Protocol.Verifier.powersFrom acc base n ++ [acc * base ^ n] := by
  induction n generalizing acc with
  | zero => simp [LeanVM.Protocol.Verifier.powersFrom]
  | succ n ih =>
    rw [LeanVM.Protocol.Verifier.powersFrom, ih, LeanVM.Protocol.Verifier.powersFrom, pow_succ',
      mul_assoc]
    rfl

/-- **`powers` is the statement's `powers`.** -/
theorem powersM_eq (base : E) (count : ℕ) :
    powersM (limbs base) count = (LeanVM.Protocol.Verifier.powers base count).map limbs := by
  have key : ∀ n, (List.range n).foldl (fun (st : List Limbs × Limbs) _ ↦
      (st.1 ++ [st.2], eMul st.2 (limbs base))) ([], eOne) =
      ((LeanVM.Protocol.Verifier.powers base n).map limbs, limbs (base ^ n)) := by
    intro n
    induction n with
    | zero => simp [LeanVM.Protocol.Verifier.powers, LeanVM.Protocol.Verifier.powersFrom,
        limbs_one]
    | succ n ih =>
      rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, eMul_eq,
        show LeanVM.Protocol.Verifier.powers base (n + 1) =
          LeanVM.Protocol.Verifier.powers base n ++ [1 * base ^ n] from powersFrom_succ 1 base n,
        one_mul, ← pow_succ]
      simp
  rw [powersM, key]

/-! ## `Scaled` -/

/-- `times_x` on both limbs: `E::new(times_x(power.c0), times_x(power.c1))`. -/
def ltimesX (p : Limbs) : Limbs := (timesX p.1, timesX p.2)

/-- `monomial` times `y`, with `y^2 = x y + 1`: `E::new(m.c1, m.c0 ^ times_x(m.c1))`. -/
def ltimesY (m : Limbs) : Limbs := (m.2, m.1 ^^^ timesX m.2)

private theorem ltimesX_eq (z : E) : ltimesX (limbs z) = limbs (z * ex) := by
  obtain ⟨a, b, rfl⟩ := exists_ofLimbs z
  rw [show ex = E.ofLimbs g 0 from ofK_eq_ofLimbs g, mul_limbs, limbs_ofLimbs, limbs_ofLimbs]
  simp only [ltimesX, timesX_eq, mul_zero, add_zero, zero_add]

private theorem ey_eq : ey = E.ofLimbs 0 1 := by
  rw [ofLimbs_eq, show ofK (0 : K) = 0 from map_zero (algebraMap K E),
    show ofK (1 : K) = 1 from map_one (algebraMap K E), zero_add, one_mul]

private theorem ltimesY_eq (z : E) : ltimesY (limbs z) = limbs (z * ey) := by
  obtain ⟨a, b, rfl⟩ := exists_ofLimbs z
  rw [ey_eq, mul_limbs, limbs_ofLimbs, limbs_ofLimbs]
  simp only [ltimesY, timesX_eq, mul_zero, mul_one, zero_add, add_zero, toBitVec_add, mul_comm g]

/-- A word of `K` is the sum of the powers of `x` at its set bits. -/
private theorem sum_bits (c : BitVec 64) :
    ∑ k ∈ Finset.range 64, (if c.getLsbD k then g ^ k else 0) = BF64.ofBitVec c := by
  apply BF64.toQuot_injective
  let φ : K →+ BF64.BF64Quot := AddMonoidHom.mk' BF64.toQuot BF64.toQuot_add
  have hsum : ∀ f : ℕ → K, BF64.toQuot (∑ k ∈ Finset.range 64, f k) =
      ∑ k ∈ Finset.range 64, BF64.toQuot (f k) := fun f ↦ map_sum φ f _
  rw [hsum, BF64.toQuot, BF64.toPolyBF64, BF64.toBitVec_ofBitVec, toPoly, map_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [apply_ite BF64.toQuot, BF64.toQuot_npow, BF64.toQuot_zero, toQuot_g,
    apply_ite (AdjoinRoot.mk _), map_pow, map_zero]
  rfl

private theorem ofK_sum_bits (c : BitVec 64) :
    ∑ k ∈ Finset.range 64, (if c.getLsbD k then ex ^ k else 0) = ofK (BF64.ofBitVec c) := by
  rw [← sum_bits c]
  change _ = algebraMap K E _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split <;> simp [map_pow]

/-! ### The tables

`WINDOW = 6` and `WINDOWS_PER_LIMB = 64.div_ceil(6) = 11`, so a limb has `11` tables of `64`
entries, `704` in all, and the run `1408`. -/

/-- `table[1 << bit | low] = table[low] + power`, the table at `base` of the flat run. -/
def fillStep (base bit : ℕ) (power : Limbs) (tables : List Limbs) (low : ℕ) : List Limbs :=
  tables.set (base + (1 <<< bit ||| low)) (eAdd (tables.getD (base + low) eZero) power)

/-- `for low in 0..1 << bit`. -/
def fillBit (base bit : ℕ) (power : Limbs) (tables : List Limbs) : List Limbs :=
  (List.range (1 <<< bit)).foldl (fillStep base bit power) tables

/-- One table: `for bit in 0..WINDOW`, `power` times `x` after each bit. -/
def fillTable (base : ℕ) (state : List Limbs × Limbs) : List Limbs × Limbs :=
  (List.range 6).foldl (fun state bit ↦ (fillBit base bit state.2 state.1, ltimesX state.2)) state

/-- One limb's `WINDOWS_PER_LIMB` tables, `power` starting at `monomial`. -/
def fillLimb (t : ℕ) (state : List Limbs × Limbs) : List Limbs × Limbs :=
  (List.range 11).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state) state

/-- `Scaled::new(r)`: the flat run of `2 * WINDOWS_PER_LIMB` tables of `1 << WINDOW` entries,
`monomial` times `y` after each limb. -/
def scaledNew (r : Limbs) : List Limbs :=
  ((List.range 2).foldl
    (fun state t ↦ ((fillLimb t (state.1, state.2)).1, ltimesY state.2))
    (List.replicate ((2 * 11) <<< 6) eZero, r)).1

/-- Entry `i` of the tables: table `i / 64` is window `j = i % 704 / 64` of limb `t = i / 704`,
and its entry `n = i % 64` is the sum of `r y^t x^(6j + b)` over the set bits `b` of `n`. -/
private def entry (r : E) (i : ℕ) : E :=
  ∑ b ∈ Finset.range 6,
    if (i % 64).testBit b then r * ey ^ (i / 704) * ex ^ (6 * (i % 704 / 64) + b) else 0

/-- The tables hold `entry` below `p`, and zero from `p` on. -/
private def Filled (r : E) (p : ℕ) (tables : List Limbs) : Prop :=
  tables.length = 1408 ∧ ∀ i, tables.getD i eZero = if i < p then limbs (entry r i) else eZero

theorem getD_set {α : Type} (l : List α) (i j : ℕ) (a d : α) :
    (l.set i a).getD j d = if i = j ∧ i < l.length then a else l.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h1 : i = j
  · subst h1
    by_cases h2 : i < l.length <;> simp [h2]
  · simp [h1]

private theorem testBit_two_pow_add (k m b : ℕ) (hm : m < 2 ^ k) :
    (2 ^ k + m).testBit b = (m.testBit b || decide (b = k)) := by
  rcases (show b < k ∨ b = k ∨ k < b by omega) with h | h | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [show b ≠ k by omega]
  · subst h; rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]; simp
  · have hb : 2 ^ (k + 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h
    rw [Nat.testBit_lt_two_pow (by rw [pow_succ] at hb; omega),
      Nat.testBit_lt_two_pow (by rw [pow_succ] at hb; omega)]
    simp [show b ≠ k by omega]

private theorem sum_bits_add (f : ℕ → E) (k m : ℕ) (hk : k < 6) (hm : m < 2 ^ k) :
    ∑ b ∈ Finset.range 6, (if (2 ^ k + m).testBit b then f b else 0) =
      ∑ b ∈ Finset.range 6, (if m.testBit b then f b else 0) + f k := by
  have hk' : m.testBit k = false := Nat.testBit_lt_two_pow hm
  have hf : ∑ b ∈ Finset.range 6, (if b = k then f b else 0) = f k := by simp [hk]
  rw [← hf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [testBit_two_pow_add k m b hm]
  by_cases hb : b = k
  · subst hb; simp [hk']
  · simp [hb]

private theorem entry_add (r : E) (t j k m : ℕ) (hj : j < 11) (hk : k < 6) (hm : m < 2 ^ k) :
    entry r ((t * 11 + j) * 64 + 2 ^ k + m) =
      entry r ((t * 11 + j) * 64 + m) + r * ey ^ t * ex ^ (6 * j + k) := by
  have hP : 2 ^ k ≤ 32 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k ≤ 5 by omega); simpa using this
  unfold entry
  generalize hP' : 2 ^ k = P at hm hP
  have e1 : ((t * 11 + j) * 64 + P + m) % 64 = P + m := by omega
  have e2 : ((t * 11 + j) * 64 + P + m) / 704 = t := by omega
  have e3 : ((t * 11 + j) * 64 + P + m) % 704 / 64 = j := by omega
  have e4 : ((t * 11 + j) * 64 + m) % 64 = m := by omega
  have e5 : ((t * 11 + j) * 64 + m) / 704 = t := by omega
  have e6 : ((t * 11 + j) * 64 + m) % 704 / 64 = j := by omega
  rw [e1, e2, e3, e4, e5, e6, ← hP']
  exact sum_bits_add (fun b ↦ r * ey ^ t * ex ^ (6 * j + b)) k m hk (hP' ▸ hm)

private theorem fillBit_prefix (base bit : ℕ) (power : Limbs) (l : List Limbs)
    (hlen : base + 2 ^ (bit + 1) ≤ l.length) (m : ℕ) (hm : m ≤ 2 ^ bit) :
    ((List.range m).foldl (fillStep base bit power) l).length = l.length ∧
      ∀ i, ((List.range m).foldl (fillStep base bit power) l).getD i eZero =
        if base + 2 ^ bit ≤ i ∧ i < base + 2 ^ bit + m then eAdd (l.getD (i - 2 ^ bit) eZero) power
        else l.getD i eZero := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ihl, ihg⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, fillStep]
    have hor : 1 <<< bit ||| m = 2 ^ bit + m := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.one_shiftLeft]
    rw [hor]
    rw [pow_succ] at hlen
    refine ⟨by rw [List.length_set, ihl], fun i ↦ ?_⟩
    rw [getD_set, ihl, ihg (base + m)]
    have hbm : ¬ (base + 2 ^ bit ≤ base + m ∧ base + m < base + 2 ^ bit + m) := by omega
    rw [ite_eq_right hbm, ihg i]
    by_cases hi : base + (2 ^ bit + m) = i
    · subst hi
      rw [ite_eq_left ⟨rfl, by omega⟩, ite_eq_left ⟨by omega, by omega⟩,
        show base + (2 ^ bit + m) - 2 ^ bit = base + m by omega]
    · rw [ite_eq_right (fun h ↦ hi h.1)]
      by_cases hr : base + 2 ^ bit ≤ i ∧ i < base + 2 ^ bit + m
      · rw [ite_eq_left hr, ite_eq_left ⟨hr.1, by omega⟩]
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

private theorem fillBit_filled (r : E) (t j k : ℕ) (ht : t < 2) (hj : j < 11) (hk : k < 6)
    (l : List Limbs) (hl : Filled r ((t * 11 + j) * 64 + 2 ^ k) l) :
    Filled r ((t * 11 + j) * 64 + 2 ^ (k + 1))
      (fillBit ((t * 11 + j) * 64) k (limbs (r * ey ^ t * ex ^ (6 * j + k))) l) := by
  have hP : 2 ^ k ≤ 32 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show k ≤ 5 by omega); simpa using this
  have hP1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  obtain ⟨hlen, hget⟩ := hl
  obtain ⟨hl', hg'⟩ := fillBit_prefix ((t * 11 + j) * 64) k
    (limbs (r * ey ^ t * ex ^ (6 * j + k))) l (by omega) (2 ^ k) le_rfl
  rw [fillBit, Nat.one_shiftLeft]
  refine ⟨by rw [hl', hlen], fun i ↦ ?_⟩
  rw [hg' i]
  by_cases hr : (t * 11 + j) * 64 + 2 ^ k ≤ i ∧ i < (t * 11 + j) * 64 + 2 ^ k + 2 ^ k
  · rw [ite_eq_left hr, ite_eq_left (by omega), hget, ite_eq_left (by omega), eAdd_eq]
    obtain ⟨m, rfl⟩ : ∃ m, i = (t * 11 + j) * 64 + 2 ^ k + m :=
      ⟨i - ((t * 11 + j) * 64 + 2 ^ k), by omega⟩
    rw [entry_add r t j k m hj hk (by omega), show (t * 11 + j) * 64 + 2 ^ k + m - 2 ^ k =
      (t * 11 + j) * 64 + m by omega]
  · rw [ite_eq_right hr, hget]
    by_cases h1 : i < (t * 11 + j) * 64 + 2 ^ k
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1, ite_eq_right (by omega)]

private theorem entry_base (r : E) (t j : ℕ) : entry r ((t * 11 + j) * 64) = 0 := by
  unfold entry
  rw [show (t * 11 + j) * 64 % 64 = 0 by omega]
  simp

private theorem fillTable_filled (r : E) (t j : ℕ) (ht : t < 2) (hj : j < 11) (l : List Limbs)
    (hl : Filled r ((t * 11 + j) * 64) l) :
    Filled r ((t * 11 + j) * 64 + 64)
        (fillTable ((t * 11 + j) * 64) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).1 ∧
      (fillTable ((t * 11 + j) * 64) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).2 =
        limbs (r * ey ^ t * ex ^ (6 * (j + 1))) := by
  have key : ∀ k ≤ 6,
      Filled r ((t * 11 + j) * 64 + 2 ^ k)
          ((List.range k).foldl (fun state bit ↦ (fillBit ((t * 11 + j) * 64) bit state.2 state.1,
            ltimesX state.2)) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).1 ∧
        ((List.range k).foldl (fun state bit ↦ (fillBit ((t * 11 + j) * 64) bit state.2 state.1,
            ltimesX state.2)) (l, limbs (r * ey ^ t * ex ^ (6 * j)))).2 =
          limbs (r * ey ^ t * ex ^ (6 * j + k)) := by
    intro k hk
    induction k with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨⟨hl.1, fun i ↦ ?_⟩, by rw [Nat.add_zero]⟩
      rw [hl.2 i]
      by_cases h1 : i < (t * 11 + j) * 64
      · rw [ite_eq_left h1, ite_eq_left (by simp; omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : i = (t * 11 + j) * 64
        · subst h2; rw [ite_eq_left (by simp), entry_base, limbs_zero]
        · rw [ite_eq_right (by simp; omega)]
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only
      rw [h2]
      refine ⟨fillBit_filled r t j k ht hj (by omega) _ h1, ?_⟩
      rw [ltimesX_eq, mul_assoc, ← pow_succ, Nat.add_assoc]
  obtain ⟨h1, h2⟩ := key 6 le_rfl
  exact ⟨h1, by rw [fillTable, h2]; ring_nf⟩

private theorem fillLimb_filled (r : E) (t : ℕ) (ht : t < 2) (l : List Limbs)
    (hl : Filled r (t * 11 * 64) l) :
    Filled r ((t + 1) * 704) (fillLimb t (l, limbs (r * ey ^ t))).1 := by
  have key : ∀ w ≤ 11,
      Filled r ((t * 11 + w) * 64)
          ((List.range w).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state)
            (l, limbs (r * ey ^ t))).1 ∧
        ((List.range w).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state)
            (l, limbs (r * ey ^ t))).2 = limbs (r * ey ^ t * ex ^ (6 * w)) := by
    intro w hw
    induction w with
    | zero => exact ⟨by simpa using hl, by simp⟩
    | succ w ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize hs : (List.range w).foldl (fun state j ↦ fillTable ((t * 11 + j) * 64) state)
        (l, limbs (r * ey ^ t)) = s at h1 h2
      obtain ⟨s1, s2⟩ := s
      simp only at h1 h2
      subst h2
      obtain ⟨h3, h4⟩ := fillTable_filled r t w ht (by omega) s1 h1
      exact ⟨by rw [show (t * 11 + (w + 1)) * 64 = (t * 11 + w) * 64 + 64 by ring]; exact h3, h4⟩
  have := (key 11 le_rfl).1
  rw [show (t * 11 + 11) * 64 = (t + 1) * 704 by ring] at this
  exact this

private theorem scaledNew_filled (r : E) : Filled r 1408 (scaledNew (limbs r)) := by
  have key : ∀ u ≤ 2,
      Filled r (u * 704)
          ((List.range u).foldl
            (fun state t ↦ ((fillLimb t (state.1, state.2)).1, ltimesY state.2))
            (List.replicate ((2 * 11) <<< 6) eZero, limbs r)).1 ∧
        ((List.range u).foldl
            (fun state t ↦ ((fillLimb t (state.1, state.2)).1, ltimesY state.2))
            (List.replicate ((2 * 11) <<< 6) eZero, limbs r)).2 = limbs (r * ey ^ u) := by
    intro u hu
    induction u with
    | zero =>
      simp only [List.range_zero, List.foldl_nil]
      refine ⟨⟨List.length_replicate, fun i ↦ ?_⟩, by rw [pow_zero, mul_one]⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> simp
    | succ u ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only
      rw [h2, ltimesY_eq, mul_assoc, ← pow_succ]
      refine ⟨?_, rfl⟩
      exact fillLimb_filled r u (by omega) _ (by rw [show u * 11 * 64 = u * 704 by ring]; exact h1)
  exact (key 2 le_rfl).1

/-! ### The product -/

/-- One lookup: `product += self.0[(table << WINDOW) | (limb >> (WINDOW * window)) as usize %
(1 << WINDOW)]`, then `table += 1`. -/
def mulStep (tables : List Limbs) (limb : BitVec 64) (state : Limbs × ℕ) (window : ℕ) :
    Limbs × ℕ :=
  (eAdd state.1 (tables.getD (state.2 <<< 6 ||| (limb >>> (6 * window)).toNat % (1 <<< 6)) eZero),
    state.2 + 1)

/-- `Scaled::mul(a)`: for each limb of `[a.c0, a.c1]`, `WINDOWS_PER_LIMB` lookups. -/
def scaledMul (tables : List Limbs) (a : Limbs) : Limbs :=
  ([a.1, a.2].foldl
    (fun state limb ↦ (List.range 11).foldl (mulStep tables limb) state) (eZero, 0)).1

private theorem sum_range_six_mul (f : ℕ → E) (n : ℕ) :
    ∑ k ∈ Finset.range (6 * n), f k =
      ∑ j ∈ Finset.range n, ∑ b ∈ Finset.range 6, f (6 * j + b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 6 * (n + 1) = 6 * n + 6 by ring, Finset.sum_range_add, ih,
      Finset.sum_range_succ (fun j ↦ ∑ b ∈ Finset.range 6, f (6 * j + b)) n]

private theorem windows_sum (r : E) (t : ℕ) (c : BitVec 64) :
    ∑ j ∈ Finset.range 11, entry r ((t * 11 + j) * 64 + (c >>> (6 * j)).toNat % 64) =
      r * ey ^ t * ofK (BF64.ofBitVec c) := by
  rw [← ofK_sum_bits, Finset.mul_sum]
  have h66 : ∑ k ∈ Finset.range 64, r * ey ^ t * (if c.getLsbD k then ex ^ k else 0) =
      ∑ k ∈ Finset.range (6 * 11), (if c.getLsbD k then r * ey ^ t * ex ^ k else 0) := by
    rw [show 6 * 11 = 64 + 2 by rfl, Finset.sum_range_add]
    simp [mul_ite]
  rw [h66, sum_range_six_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj := Finset.mem_range.1 hj
  unfold entry
  have hn : (c >>> (6 * j)).toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
  generalize hN : (c >>> (6 * j)).toNat % 64 = n at hn
  rw [show ((t * 11 + j) * 64 + n) % 64 = n by omega,
    show ((t * 11 + j) * 64 + n) / 704 = t by omega,
    show ((t * 11 + j) * 64 + n) % 704 / 64 = j by omega]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  have hb := Finset.mem_range.1 hb
  have : n.testBit b = c.getLsbD (6 * j + b) := by
    rw [← hN, show (c >>> (6 * j)).toNat % 64 = (c >>> (6 * j)).toNat % 2 ^ 6 by norm_num,
      Nat.testBit_mod_two_pow, BitVec.toNat_ushiftRight,
      Nat.testBit_shiftRight, BitVec.testBit_toNat]
    simp [hb]
  rw [this]

private theorem mulStep_fold (r : E) (tables : List Limbs) (htab : Filled r 1408 tables) (t : ℕ)
    (ht : t < 2) (c : BitVec 64) (p : E) :
    (List.range 11).foldl (mulStep tables c) (limbs p, t * 11) =
      (limbs (p + r * ey ^ t * ofK (BF64.ofBitVec c)), (t + 1) * 11) := by
  have key : ∀ w ≤ 11, (List.range w).foldl (mulStep tables c) (limbs p, t * 11) =
      (limbs (p + ∑ j ∈ Finset.range w, entry r ((t * 11 + j) * 64 + (c >>> (6 * j)).toNat % 64)),
        t * 11 + w) := by
    intro w hw
    induction w with
    | zero => simp
    | succ w ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega),
        mulStep]
      have hn : (c >>> (6 * w)).toNat % 64 < 64 := Nat.mod_lt _ (by norm_num)
      rw [show (1 <<< 6 : ℕ) = 64 by rfl, ← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hn),
        Nat.shiftLeft_eq, htab.2, ite_eq_left (by omega), eAdd_eq, Finset.sum_range_succ,
        add_assoc, show (t * 11 + w) * 2 ^ 6 = (t * 11 + w) * 64 by rfl]
      rfl
  rw [key 11 le_rfl, windows_sum r t c, show t * 11 + 11 = (t + 1) * 11 by ring]

/-- **`Scaled::mul` of `Scaled::new(r)` is the product by `r`.** -/
theorem scaledMul_eq (r a : E) : scaledMul (scaledNew (limbs r)) (limbs a) = limbs (a * r) := by
  have htab := scaledNew_filled r
  unfold scaledMul
  rw [List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show (eZero, 0) = (limbs 0, 0 * 11) by rw [limbs_zero],
    mulStep_fold r _ htab 0 (by norm_num), mulStep_fold r _ htab 1 (by norm_num)]
  conv_rhs => rw [eq_sum_limbs a]
  exact congrArg limbs (by simp only [limbs, BF64.ofBitVec_toBitVec]; ring)

/-! ## `E`-valued forms, for the other modules' mirrors -/

/-- `E::square` of a word. -/
def squareE (x : E) : E := ofLimbsW (eSquare (limbs x))

theorem squareE_eq (x : E) : squareE x = x ^ 2 := by
  rw [squareE, eSquare_eq, ofLimbsW_limbs, sq]

/-- `Scaled::new(r)` of a word. -/
def scaledNewE (r : E) : List Limbs := scaledNew (limbs r)

/-- `Scaled::mul(a)` of a word. -/
def scaledMulE (tables : List Limbs) (a : E) : E := ofLimbsW (scaledMul tables (limbs a))

theorem scaledMulE_eq (r a : E) : scaledMulE (scaledNewE r) a = a * r := by
  rw [scaledMulE, scaledNewE, scaledMul_eq, ofLimbsW_limbs]

end

end Rv64mc.Model
