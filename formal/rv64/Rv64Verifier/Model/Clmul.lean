import Mathlib
import CompPoly.Fields.Binary.Common

/-!
# The low half of a carry-less product, by integer multiplication

`crates/verifier/src/field.rs`'s `clmul_low` splits each operand into the four classes of its bit
positions mod 4 and multiplies classes as integers. A product of classes `i` and `j` has its bits
in class `i + j`: below bit 60 a coefficient of the integer product counts at most 15 pairs of
bits, so it never carries into the next bit of its class, and its low bit is the parity of that
count. Masking each class's XOR of products to its own bits leaves the carry-less product.
-/

namespace Rv64Verifier.Model

open Finset

/-- The class masks: bit `u` set when `u % 4 = i`. -/
def classMask (i : ℕ) : BitVec 64 := 0x1111111111111111#64 <<< i

/-- `clmul_low`, as the Rust writes it. -/
def clmulLow (a b : BitVec 64) : BitVec 64 :=
  let m0 := classMask 0
  let m1 := classMask 1
  let m2 := classMask 2
  let m3 := classMask 3
  let x0 := a &&& m0
  let x1 := a &&& m1
  let x2 := a &&& m2
  let x3 := a &&& m3
  let y0 := b &&& m0
  let y1 := b &&& m1
  let y2 := b &&& m2
  let y3 := b &&& m3
  let z0 := x0 * y0 ^^^ x1 * y3 ^^^ x2 * y2 ^^^ x3 * y1
  let z1 := x0 * y1 ^^^ x1 * y0 ^^^ x2 * y3 ^^^ x3 * y2
  let z2 := x0 * y2 ^^^ x1 * y1 ^^^ x2 * y0 ^^^ x3 * y3
  let z3 := x0 * y3 ^^^ x1 * y2 ^^^ x2 * y1 ^^^ x3 * y0
  z0 &&& m0 ||| z1 &&& m1 ||| z2 &&& m2 ||| z3 &&& m3

theorem getLsbD_classMask {i : ℕ} (hi : i < 4) (u : ℕ) :
    (classMask i).getLsbD u = decide (u < 64 ∧ u % 4 = i) := by
  by_cases hu : u < 64
  · interval_cases i <;> revert u <;> decide
  · simp [BitVec.getLsbD_of_ge (classMask i) u (by omega), hu]

/-! ## Words as sums of powers of two -/

/-- The set bits of a word. -/
def bitSet (v : BitVec 64) : Finset ℕ := (range 64).filter fun u ↦ v.getLsbD u

theorem mem_bitSet {v : BitVec 64} {u : ℕ} : u ∈ bitSet v ↔ v.getLsbD u := by
  simp only [bitSet, mem_filter, mem_range, and_iff_right_iff_imp]
  exact fun h ↦ BitVec.lt_of_getLsbD h

theorem toNat_eq_sum (v : BitVec 64) : v.toNat = ∑ u ∈ bitSet v, 2 ^ u := by
  conv_lhs => rw [← Finset.sum_toFinset_bitIndices_two_pow v.toNat]
  congr 1
  ext u
  simp [mem_bitSet, Nat.mem_bitIndices, BitVec.testBit_toNat]

/-- The pairs of set bits, one from each word, at positions summing to `q`. -/
def pairs (x y : BitVec 64) (q : ℕ) : Finset (ℕ × ℕ) :=
  (bitSet x ×ˢ bitSet y).filter fun uv ↦ uv.1 + uv.2 = q

theorem toNat_mul_toNat (x y : BitVec 64) :
    x.toNat * y.toNat = ∑ q ∈ range 128, (pairs x y q).card * 2 ^ q := by
  rw [toNat_eq_sum x, toNat_eq_sum y, sum_mul_sum, ← sum_product']
  simp_rw [← pow_add]
  rw [← sum_fiberwise_of_maps_to (g := fun uv : ℕ × ℕ ↦ uv.1 + uv.2) (t := range 128)]
  · refine sum_congr rfl fun q _ ↦ ?_
    rw [pairs, sum_congr rfl fun uv huv ↦ by rw [(mem_filter.1 huv).2], sum_const, smul_eq_mul]
  · intro uv huv
    obtain ⟨h1, h2⟩ := mem_product.1 huv
    have := BitVec.lt_of_getLsbD (mem_bitSet.1 h1)
    have := BitVec.lt_of_getLsbD (mem_bitSet.1 h2)
    simp only [mem_range]
    omega

/-! ## Reading a bit of a sum of digits -/

/-- A sum of `c q · 2^q` whose nonzero digits sit in one class mod 4, each below 16 under bit
`p`: below `p` it stays below `2^p`. -/
theorem sum_lt_of_digits (c : ℕ → ℕ) (r : ℕ) (hr : r < 4) (hsupp : ∀ q, c q ≠ 0 → q % 4 = r)
    (m : ℕ) (hsmall : ∀ q < r + 4 * m, c q ≤ 15) :
    ∑ q ∈ range (r + 4 * m), c q * 2 ^ q < 2 ^ (r + 4 * m) := by
  induction m with
  | zero =>
    rw [sum_eq_zero]
    · positivity
    · intro q hq
      have : c q = 0 := by
        by_contra h
        have := hsupp q h
        simp only [mem_range] at hq
        omega
      simp [this]
  | succ m ih =>
    have hzero : ∀ k, 0 < k → k < 4 → c (r + 4 * m + k) = 0 := by
      intro k hk0 hk4
      by_contra h
      have := hsupp _ h
      omega
    rw [show r + 4 * (m + 1) = r + 4 * m + 1 + 1 + 1 + 1 by ring]
    simp only [sum_range_succ]
    rw [hzero 1 (by omega) (by omega), show r + 4 * m + 1 + 1 = r + 4 * m + 2 by ring,
      hzero 2 (by omega) (by omega), show r + 4 * m + 2 + 1 = r + 4 * m + 3 by ring,
      hzero 3 (by omega) (by omega)]
    have h1 := ih fun q hq ↦ hsmall q (by omega)
    have h2 := hsmall (r + 4 * m) (by omega)
    have h3 : c (r + 4 * m) * 2 ^ (r + 4 * m) ≤ 15 * 2 ^ (r + 4 * m) := Nat.mul_le_mul_right _ h2
    rw [show 2 ^ (r + 4 * m + 3 + 1) = 16 * 2 ^ (r + 4 * m) by ring]
    simp only [zero_mul, add_zero]
    omega

theorem testBit_sum_digits (c : ℕ → ℕ) (K p : ℕ) (hp : p < K)
    (hsupp : ∀ q, c q ≠ 0 → q % 4 = p % 4) (hsmall : ∀ q < p, c q ≤ 15) :
    (∑ q ∈ range K, c q * 2 ^ q).testBit p = decide (c p % 2 = 1) := by
  set r := p % 4
  obtain ⟨m, hm⟩ : ∃ m, p = r + 4 * m := ⟨p / 4, by omega⟩
  have hlow : ∑ q ∈ range p, c q * 2 ^ q < 2 ^ p := by
    rw [hm]
    exact sum_lt_of_digits c r (Nat.mod_lt _ (by norm_num)) hsupp m (fun q hq ↦ hsmall q (by omega))
  have hhigh : ∀ q ∈ Ico (p + 1) K, c q * 2 ^ q = 2 ^ p * (16 * (c q * 2 ^ (q - p - 4))) := by
    intro q hq
    simp only [mem_Ico] at hq
    by_cases h : c q = 0
    · simp [h]
    · have := hsupp q h
      have hq4 : p + 4 ≤ q := by omega
      rw [show q = p + 4 + (q - p - 4) by omega, pow_add, pow_add]
      rw [show p + 4 + (q - p - 4) - p - 4 = q - p - 4 by omega]
      ring
  have hsplit : ∑ q ∈ range K, c q * 2 ^ q =
      2 ^ p * (c p + 16 * ∑ q ∈ Ico (p + 1) K, c q * 2 ^ (q - p - 4)) +
        ∑ q ∈ range p, c q * 2 ^ q := by
    rw [← sum_range_add_sum_Ico _ (show p ≤ K by omega), sum_eq_sum_Ico_succ_bot hp,
      sum_congr rfl hhigh, ← mul_sum, ← mul_sum]
    ring
  rw [hsplit, Nat.testBit_two_pow_mul_add _ hlow]
  simp only [lt_irrefl, ↓reduceIte, Nat.sub_self, Nat.testBit_zero]
  congr 1
  apply propext
  omega

/-! ## A product of two classes -/

/-- Each set bit of a class-`i` word is in class `i`. -/
def InClass (x : BitVec 64) (i : ℕ) : Prop := ∀ u, x.getLsbD u → u % 4 = i

theorem card_pairs_le (x y : BitVec 64) (i : ℕ) (hi : i < 4) (hx : InClass x i) (q : ℕ)
    (hq : q < 60) : (pairs x y q).card ≤ 15 := by
  calc (pairs x y q).card ≤ ((range 60).filter fun u ↦ u % 4 = i).card := by
        apply card_le_card_of_injOn Prod.fst
        · intro uv huv
          have huv := mem_coe.1 huv
          simp only [pairs, mem_filter, mem_product, mem_bitSet] at huv
          rw [mem_coe, mem_filter, mem_range]
          exact ⟨by omega, hx _ huv.1.1⟩
        · intro uv huv uv' huv' h
          have huv := (mem_filter.1 (mem_coe.1 huv)).2
          have huv' := (mem_filter.1 (mem_coe.1 huv')).2
          ext
          · exact h
          · omega
    _ = 15 := by interval_cases i <;> decide

theorem getLsbD_mul_class (x y : BitVec 64) (i j : ℕ) (hi : i < 4)
    (hx : InClass x i) (hy : InClass y j) (p : ℕ) (hp : p < 64) (hpij : p % 4 = (i + j) % 4) :
    (x * y).getLsbD p = decide ((pairs x y p).card % 2 = 1) := by
  rw [← BitVec.testBit_toNat, BitVec.toNat_mul, Nat.testBit_mod_two_pow, decide_eq_true hp,
    Bool.true_and, toNat_mul_toNat]
  apply testBit_sum_digits _ _ _ (by omega)
  · intro q hq
    obtain ⟨uv, huv⟩ := card_ne_zero.1 hq
    simp only [pairs, mem_filter, mem_product, mem_bitSet] at huv
    have := hx _ huv.1.1
    have := hy _ huv.1.2
    omega
  · intro q hq
    by_cases h : (pairs x y q).card = 0
    · omega
    · obtain ⟨uv, huv⟩ := card_ne_zero.1 h
      simp only [pairs, mem_filter, mem_product, mem_bitSet] at huv
      have := hx _ huv.1.1
      have := hy _ huv.1.2
      exact card_pairs_le x y i hi hx q (by omega)

/-! ## The four classes together -/

theorem inClass_and (a : BitVec 64) {i : ℕ} (hi : i < 4) : InClass (a &&& classMask i) i := by
  intro u hu
  simp only [BitVec.getLsbD_and, getLsbD_classMask hi, Bool.and_eq_true, decide_eq_true_eq] at hu
  exact hu.2.2

/-- The pairs at `q`, by the class of their first position. -/
theorem card_pairs_split (a b : BitVec 64) (q : ℕ) :
    (pairs a b q).card = ∑ i ∈ range 4,
      (pairs (a &&& classMask i) (b &&& classMask ((q + 4 - i) % 4)) q).card := by
  rw [card_eq_sum_card_fiberwise (f := fun uv : ℕ × ℕ ↦ uv.1 % 4) (t := range 4)]
  · refine sum_congr rfl fun i hi ↦ ?_
    simp only [mem_range] at hi
    congr 1
    ext ⟨u, v⟩
    simp only [pairs, mem_filter, mem_product, mem_bitSet, BitVec.getLsbD_and,
      getLsbD_classMask hi, getLsbD_classMask (Nat.mod_lt _ (by norm_num) : (q + 4 - i) % 4 < 4),
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨hu, hv⟩, huv⟩, hi'⟩
      have := BitVec.lt_of_getLsbD hu
      have := BitVec.lt_of_getLsbD hv
      exact ⟨⟨⟨hu, by omega, by omega⟩, hv, by omega, by omega⟩, huv⟩
    · rintro ⟨⟨⟨hu, _, hi'⟩, hv, _⟩, huv⟩
      exact ⟨⟨⟨hu, hv⟩, huv⟩, hi'⟩
  · intro uv _
    simpa using Nat.mod_lt uv.1 (by norm_num : 0 < 4)

theorem xor_parity (a b c d : ℕ) :
    (decide (a % 2 = 1) != (decide (b % 2 = 1) != (decide (c % 2 = 1) != decide (d % 2 = 1)))) =
      decide ((a + b + c + d) % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
  rcases Nat.mod_two_eq_zero_or_one d with hd | hd <;>
  simp only [ha, hb, hc, hd] <;> (simp; omega)

theorem getLsbD_clmulLow (a b : BitVec 64) (p : ℕ) (hp : p < 64) :
    (clmulLow a b).getLsbD p = decide ((pairs a b p).card % 2 = 1) := by
  have key : ∀ i j, i < 4 → j < 4 → p % 4 = (i + j) % 4 →
      ((a &&& classMask i) * (b &&& classMask j)).getLsbD p =
        decide ((pairs (a &&& classMask i) (b &&& classMask j) p).card % 2 = 1) :=
    fun i j hi hj hij ↦ getLsbD_mul_class _ _ i j hi (inClass_and a hi) (inClass_and b hj) p hp hij
  rw [card_pairs_split]
  simp only [sum_range_succ, sum_range_zero, zero_add]
  unfold clmulLow
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    getLsbD_classMask (show 0 < 4 by norm_num), getLsbD_classMask (show 1 < 4 by norm_num),
    getLsbD_classMask (show 2 < 4 by norm_num), getLsbD_classMask (show 3 < 4 by norm_num), hp,
    true_and]
  have h4 : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rcases (show p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 by omega) with h | h | h | h <;>
  · simp only [h, show (p + 4 - 0) % 4 = (p % 4 + 4 - 0) % 4 by omega,
      show (p + 4 - 1) % 4 = (p % 4 + 4 - 1) % 4 by omega,
      show (p + 4 - 2) % 4 = (p % 4 + 4 - 2) % 4 by omega,
      show (p + 4 - 3) % 4 = (p % 4 + 4 - 3) % 4 by omega]
    norm_num
    rw [key 0 _ (by norm_num) (by norm_num) (by omega), key 1 _ (by norm_num) (by norm_num) (by omega),
      key 2 _ (by norm_num) (by norm_num) (by omega), key 3 _ (by norm_num) (by norm_num) (by omega),
      xor_parity]

/-! ## The carry-less product -/

theorem coeff_bit {w : ℕ} (v : BitVec w) (i : ℕ) :
    (if h : i < w then (if v.getLsb ⟨i, h⟩ = true then (1 : ZMod 2) else 0) else 0) =
      if v.getLsbD i then 1 else 0 := by
  by_cases h : i < w
  · simp only [h, ↓reduceDIte]
    rfl
  · simp [h, BitVec.getLsbD_of_ge v i (by omega)]

open BinaryField in
theorem getLsbD_carryLessMul (a b : BitVec 64) (p : ℕ) :
    (carryLessMul (w := 128) a b).getLsbD p = decide ((pairs a b p).card % 2 = 1) := by
  have h := congrArg (fun P ↦ P.coeff p) (toPoly_carryLessMul (w := 128) a b (by norm_num))
  simp only [toPoly_coeff, Polynomial.coeff_mul, coeff_bit, ite_mul, one_mul, zero_mul,
    ← ite_and, sum_boole] at h
  have hfilter : (HasAntidiagonal.antidiagonal p).filter (fun x ↦ a.getLsbD x.1 = true ∧
      b.getLsbD x.2 = true) = pairs a b p := by
    ext ⟨u, v⟩
    simp only [mem_filter, HasAntidiagonal.mem_antidiagonal, pairs, mem_product, mem_bitSet]
    tauto
  rw [hfilter, ← ZMod.natCast_mod] at h
  rcases Nat.mod_two_eq_zero_or_one (pairs a b p).card with hc | hc <;> rw [hc] at h <;>
    cases hb : (carryLessMul (w := 128) a b).getLsbD p <;> simp_all

/-- **`clmul_low` is the low half of the carry-less product.** -/
theorem clmulLow_eq (a b : BitVec 64) :
    clmulLow a b = (BinaryField.carryLessMul (w := 128) a b).truncate 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and,
    getLsbD_carryLessMul, getLsbD_clmulLow a b p hp]

end Rv64Verifier.Model
