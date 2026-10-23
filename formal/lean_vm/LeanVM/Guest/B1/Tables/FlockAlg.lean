/-
  LeanVM.Guest.B1.Tables.FlockAlg

  The algebra `verify_flock` relies on: the skip interpolation over 128 nodes from the
  numerators of the upper half, the slices' Lagrange combination, the pin column's weight, and
  the compile-time constants (the fixed challenges, the cursor's steps).
-/

module

public import LeanVM.Guest.B1.Tables.FlockSpec

/-!
# `verify_flock`'s algebra

* `interp_eq`: `lagrangeInterpolate 128 (0^64 ++ p) z` (V:758) is the sum of the upper half's
  numerators times `p`, scaled by the lower half's product and `windowDenominator 128`, whose
  word is `LAGRANGE_INV_COMBINED` (`lagInvComb_eq`).
* `cslice_eq`: `dot (lagrangeWeights 64 z) s` from the numerators and `LAGRANGE_INV_S`.
* `colWeight_pin`: the column weight at `BLAKE2S_CONSTANT_COLUMN = 512` is `s[0]` times the
  equality weight at index 8.
* `fixed_words`: the seven words the prelude stores are `fixedChallenges` (V:1812).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Sums and products -/

theorem dot_eq_sum : ∀ (l m : List E) (n : ℕ), l.length = n → m.length = n →
    dot l m = ∑ i ∈ Finset.range n, l.getD i 0 * m.getD i 0 := by
  intro l m n hl hm
  have key : ∀ (l m : List E) (a : E), l.length = m.length →
      (List.zipWith (· * ·) l m).foldl (· + ·) a =
        a + ∑ i ∈ Finset.range l.length, l.getD i 0 * m.getD i 0 := by
    intro l
    induction l with
    | nil => intro m a _; simp
    | cons x l ih =>
      intro m a h
      match m, h with
      | y :: m, h =>
        simp only [List.zipWith_cons_cons, List.foldl_cons, List.length_cons]
        rw [ih m _ (by simpa using h), Finset.sum_range_succ']
        simp only [List.getD_cons_succ, List.getD_cons_zero]
        ring
  rw [dot, key l m 0 (by rw [hl, hm]), zero_add, hl]

theorem prod_erase_eq (f : ℕ → E) {n i : ℕ} (hi : i < n) :
    ∏ j ∈ (Finset.range n).erase i, f j =
      (∏ j ∈ Finset.range i, f j) * ∏ j ∈ Finset.Ico (i + 1) n, f j := by
  have hset : (Finset.range n).erase i = Finset.range i ∪ Finset.Ico (i + 1) n := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hset, Finset.prod_union (Finset.disjoint_left.mpr fun j h1 h2 => by
    simp only [Finset.mem_range] at h1
    simp only [Finset.mem_Ico] at h2
    omega)]

/-! ## The Lagrange weights -/

/-- `lagrangeWeights n z` at `i` (V:750): the products of `z + φ(j)` below and above `i`, times
the window's denominator. -/
theorem lagrange_getD' (n : ℕ) (z : E) (i : ℕ) (hi : i < n) :
    (lagrangeWeights n z).getD i 0 = (∏ j ∈ Finset.range i, (z + phi j)) *
      (∏ j ∈ Finset.Ico (i + 1) n, (z + phi j)) * windowDenominator n := by
  have hd : ((List.range n).map fun k ↦ z + phi k).length = n := by simp
  simp only [lagrangeWeights]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_zipWith, List.getElem_take,
    List.getElem_scanl, List.getElem_drop, List.getElem_reverse, List.getElem_scanl,
    Main.take_map_range _ _ _ (by omega), Main.foldl_mul_eq_prod]
  congr 2
  simp only [List.length_scanl, List.length_reverse, hd]
  rw [show n + 1 - 1 - (1 + i) = n - 1 - i by omega, List.take_reverse, hd,
    show n - (n - 1 - i) = i + 1 by omega, Main.foldl_mul_reverse,
    Main.drop_map_range _ _ _ (by omega), Main.foldl_mul_eq_prod, Finset.prod_Ico_eq_prod_range]

theorem lagInvComb_mul : K.ofBits 233317187178767959 *
    ((List.range 127).map fun k => Flock.phi8 (k + 1)).foldl (· * ·) 1 = 1 := by decide +kernel

/-- `LAGRANGE_INV_COMBINED` is `windowDenominator 128` (V:745). -/
theorem lagInvComb_eq : word 233317187178767959 0 0 = windowDenominator 128 := by
  rw [windowDenominator]
  apply eq_inv_of_mul_eq_one_left
  have h := congrArg ofK lagInvComb_mul
  have hp : ofK (∏ j ∈ Finset.range 127, Flock.phi8 (j + 1)) =
      ∏ j ∈ Finset.range 127, phi (j + 1) :=
    map_prod (algebraMap K E) _ _
  rw [ofK_mul, ofK_one, Main.foldl_mul_eq_prod (fun k => Flock.phi8 (k + 1)), hp] at h
  rw [word_eOfNat, eOfNat, show 128 - 1 = 127 from rfl, Main.foldl_mul_eq_prod]
  exact h

/-- **The skip interpolation** (V:1835): over the 128 nodes, the lower 64 values zero, it is the
upper half's numerators against `p`, times the lower half's product and the denominator. -/
theorem interp_eq (z : E) (p : List E) (hp : p.length = 64) :
    lagrangeInterpolate 128 (List.replicate 64 0 ++ p) z =
      (∑ i ∈ Finset.range 64, (∏ j ∈ (Finset.range 64).erase i, (z + phi (64 + j))) * p.getD i 0) *
        ((∏ i ∈ Finset.range 64, (z + phi i)) * word 233317187178767959 0 0) := by
  rw [lagrangeInterpolate, dot_eq_sum _ _ 128 (by simp [lagrangeWeights]) (by simp [hp]),
    show 128 = 64 + 64 from rfl, Finset.sum_range_add, Finset.sum_mul, lagInvComb_eq]
  have h0 : ∀ i ∈ Finset.range 64,
      (lagrangeWeights (64 + 64) z).getD i 0 * (List.replicate 64 0 ++ p).getD i 0 = 0 := by
    intro i hi
    have hi' : i < 64 := Finset.mem_range.mp hi
    have : (List.replicate 64 (0 : E) ++ p).getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega),
        List.getElem?_replicate]
      simp [hi']
    rw [this, mul_zero]
  rw [Finset.sum_eq_zero h0, zero_add]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 64 := Finset.mem_range.mp hi
  have hv : (List.replicate 64 (0 : E) ++ p).getD (64 + i) 0 = p.getD i 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp), List.length_replicate, Nat.add_sub_cancel_left]
  rw [hv, lagrange_getD' _ z _ (by omega), Finset.prod_range_add, prod_erase_eq _ hi',
    Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range,
    show 64 + 64 - (64 + i + 1) = 64 - (i + 1) by omega]
  have e : ∀ k, 64 + i + 1 + k = 64 + (i + 1 + k) := fun k => by omega
  simp only [e]
  ring

/-- **The slices' Lagrange combination** (V:1990): the numerators over the 64 skip nodes against
`s`, scaled by `LAGRANGE_INV_S`. -/
theorem cslice_eq (z : E) (s : List E) (hs : s.length = 64) :
    (∑ i ∈ Finset.range 64, (∏ j ∈ (Finset.range 64).erase i, (z + phi j)) * s.getD i 0) *
        word 11666641484232641359 0 0 = dot (lagrangeWeights 64 z) s := by
  rw [dot_eq_sum _ _ 64 (by simp [lagrangeWeights]) hs, Main.lagInv_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [lagrange_getD' _ z _ (Finset.mem_range.mp hi), prod_erase_eq _ (Finset.mem_range.mp hi)]
  ring

/-! ## The pin column -/

theorem flatMap_getD (s : List E) (hs : s.length = 64) :
    ∀ (l : List E) (q r : ℕ), r < 64 → q < l.length →
      (l.flatMap fun w => s.map (· * w)).getD (64 * q + r) 0 = s.getD r 0 * l.getD q 0
  | [], _, _, _, hq => absurd hq (by simp)
  | w :: l, q, r, hr, hq => by
    rw [List.flatMap_cons]
    rcases q with _ | q
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hs]; omega)]
      simp [List.getD_eq_getElem?_getD, hr, hs]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hs]; omega)]
      simp only [List.length_map, hs, show 64 * (q + 1) + r - 64 = 64 * q + r by omega]
      rw [← List.getD_eq_getElem?_getD, flatMap_getD s hs l q r hr (by simpa using hq)]
      rfl

/-- **The column weight at `BLAKE2S_CONSTANT_COLUMN`** (V:1993): `s[0]` times the equality
weight of the column point at index 8, bit 3 set, the others clear. -/
theorem colWeight_pin (rc s : List E) (hrc : rc.length = 8) (hs : s.length = 64) :
    (lincheckColumnWeights rc.reverse s).getD 512 0 = s.getD 0 0 *
      ((1 + rc.getD 0 0) * (1 + rc.getD 1 0) * (1 + rc.getD 2 0) * (1 + rc.getD 3 0) *
        rc.getD 4 0 * (1 + rc.getD 5 0) * (1 + rc.getD 6 0) * (1 + rc.getD 7 0)) := by
  rw [lincheckColumnWeights, show 512 = 64 * 8 + 0 from rfl,
    flatMap_getD s hs _ 8 0 (by omega) (by rw [length_eqKernel, List.length_reverse, hrc]; decide),
    eqKernel_getD _ 8 (by rw [List.length_reverse, hrc]; decide), List.length_reverse, hrc]
  have hr : ∀ c < 8, rc.reverse.getD c 0 = rc.getD (7 - c) 0 := fun c hc => by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega),
      hrc]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, hr _ (by decide : (0 : ℕ) < 8),
    hr _ (by decide : (1 : ℕ) < 8), hr _ (by decide : (2 : ℕ) < 8), hr _ (by decide : (3 : ℕ) < 8),
    hr _ (by decide : (4 : ℕ) < 8), hr _ (by decide : (5 : ℕ) < 8), hr _ (by decide : (6 : ℕ) < 8),
    hr _ (by decide : (7 : ℕ) < 8)]
  simp only [ewFac, show Nat.testBit 8 0 = false from rfl, show Nat.testBit 8 1 = false from rfl,
    show Nat.testBit 8 2 = false from rfl, show Nat.testBit 8 3 = true from rfl,
    show Nat.testBit 8 4 = false from rfl, show Nat.testBit 8 5 = false from rfl,
    show Nat.testBit 8 6 = false from rfl, show Nat.testBit 8 7 = false from rfl,
    Bool.false_eq_true, ↓reduceIte, Nat.reduceSub]
  ring

/-! ## The constants -/

theorem word_g78 : word 442368 0 0 = gen ^ 78 := by
  rw [word_eOfNat, gen_pow_eq_ofK]
  show ofK (K.ofBits 442368) = ofK (Parameters.gpow 78)
  rw [show K.ofBits 442368 = Parameters.gpow 78 by decide +kernel]

theorem word_g82 : word 7077888 0 0 = gen ^ 82 := by
  rw [word_eOfNat, gen_pow_eq_ofK]
  show ofK (K.ofBits 7077888) = ofK (Parameters.gpow 82)
  rw [show K.ofBits 7077888 = Parameters.gpow 82 by decide +kernel]

/-- The words the prelude stores at `zerocheck_r[g^(6+i)]`. -/
def fixedWords : List E :=
  [word 5772811086190238293 0 0, word 18376177690117868746 0 0, word 1537792354547671042 0 0,
    word 3877548338577296374 1367482035892397521 13373126565067795492,
    word 7200243516802924451 16251485319816311889 13522021764491415548,
    word 14498505783250251438 16564499533431716054 16770611540025040673,
    word 3934799921294095118 853327055063395975 1309330797735322834]

theorem mediumCoord_of {w a : E} (h : w * (1 + a) = a) : w = a / (1 + a) := by
  have hne : 1 + a ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    rw [← h, add_zero] at h0
    exact one_ne_zero h0
  rw [eq_div_iff hne, h]

theorem fixed_low : ∀ i < 3, K.ofBits ([5772811086190238293, 18376177690117868746,
    1537792354547671042].getD i 0) = Flock.phi8 (Flock.fixedBytes.toList.getD i 0) := by
  decide +kernel

/-- Products in `E` limb by limb (`mul_limbs`), as a computable function on triples. -/
def mul3 (a b : K × K × K) : K × K × K :=
  (a.1 * b.1 + a.2.1 * b.2.2 + a.2.2 * b.2.1,
    a.1 * b.2.1 + a.2.1 * b.1 + a.2.1 * b.2.2 + a.2.2 * b.2.1 + a.2.2 * b.2.2,
    a.1 * b.2.2 + a.2.1 * b.2.1 + a.2.2 * b.1 + a.2.2 * b.2.2)

/-- A triple's word. -/
def of3 (a : K × K × K) : E := E.ofLimbs a.1 a.2.1 a.2.2

theorem of3_mul (a b : K × K × K) : of3 a * of3 b = of3 (mul3 a b) := mul_limbs _ _ _ _ _ _

/-- `g_0^(2^j)`'s limbs. -/
def g0Pow : ℕ → K × K × K
  | 0 => (K.ofBits 0x243F6A8885A308D3, K.ofBits 0x13198A2E03707344, K.ofBits 0xA4093822299F31D0)
  | j + 1 => mul3 (g0Pow j) (g0Pow j)

theorem g0_pow (j : ℕ) : Flock.g0 ^ 2 ^ j = of3 (g0Pow j) := by
  induction j with
  | zero => rw [pow_zero, pow_one]; rfl
  | succ j ih => rw [pow_succ, pow_mul, sq, ih, of3_mul]; rfl

/-- The last four words' limbs. -/
def fixedTriples : List (K × K × K) :=
  [(K.ofBits 3877548338577296374, K.ofBits 1367482035892397521, K.ofBits 13373126565067795492),
    (K.ofBits 7200243516802924451, K.ofBits 16251485319816311889, K.ofBits 13522021764491415548),
    (K.ofBits 14498505783250251438, K.ofBits 16564499533431716054, K.ofBits 16770611540025040673),
    (K.ofBits 3934799921294095118, K.ofBits 853327055063395975, K.ofBits 1309330797735322834)]

theorem fixed_med3 : ∀ j < 4, mul3 (fixedTriples.getD j (0, 0, 0))
    ((1, 0, 0) + g0Pow j) = g0Pow j := by
  decide +kernel

theorem fixed_med (j : ℕ) (hj : j < 4) :
    fixedWords.getD (3 + j) 0 * (1 + Flock.g0 ^ 2 ^ j) = Flock.g0 ^ 2 ^ j := by
  have hw : fixedWords.getD (3 + j) 0 = of3 (fixedTriples.getD j (0, 0, 0)) := by
    interval_cases j <;> rfl
  have h1 : (1 : E) + of3 (g0Pow j) = of3 ((1, 0, 0) + g0Pow j) := by
    rw [one_eq_ofLimbs, of3, ofLimbs_add]; rfl
  rw [hw, g0_pow, h1, of3_mul, fixed_med3 j hj]

/-- **The prelude's words are the fixed challenges** (V:1812). -/
theorem fixed_words : fixedWords = fixedChallenges := by
  apply List.ext_getElem (by rfl)
  intro i h1 h2
  have hi : i < 7 := h1
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
  rcases Nat.lt_or_ge i 3 with h | h
  · have := fixed_low i h
    interval_cases i <;>
      simp only [fixedWords, fixedChallenges, Flock.fixedPoint, List.getD_cons_zero,
        List.getD_cons_succ, Vector.toList_mk, word_eOfNat, eOfNat] at this ⊢ <;>
      rw [this] <;> rfl
  · obtain ⟨j, rfl⟩ : ∃ j, i = 3 + j := ⟨i - 3, by omega⟩
    have hj : j < 4 := by omega
    rw [mediumCoord_of (fixed_med j hj)]
    interval_cases j <;> rfl

end
end LeanVM.Guest.B1
