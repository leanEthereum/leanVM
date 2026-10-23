/-
  LeanVM.Spec.Fast.FieldWords

  Multiplication in CompPoly's `GF(2^64)` on machine words: the carry-less product on `UInt64`
  words and the reduction by `x^64 = x^4 + x^3 + x + 1` as shifts, proved equal to `BF64.mul` and
  swapped in for compilation, with CompPoly's instances restated to be compiled with it.
  Candidate for CompPoly.
-/

module

public import CompPoly.Fields.Binary.BF64
import Mathlib.Tactic.Ring

/-!
# `GF(2^64)` arithmetic on machine words

`BF64.mul a b` reduces `carryLessMul (w := 128) a b`, a fold over the 64 bits of `a` on
`BitVec 128`; compiled, every step is arbitrary-precision arithmetic on `Nat`. This module
computes the same product on `UInt64` words:

* `tailHigh h`, `tailLow h` are the two words of the carry-less product of `h` by the reduction
  constant `0x1B`, as shifts (`carryLessMul_reductionConstant`), and `reduceWords hi lo` is
  `BF64.reduce` on the words `(hi, lo)` of a 128-bit value (`reduceWords_eq`);
* `mulShift a bhi blo hi lo` is the fold of `carryLessMul`, the remaining bits of the first factor
  in `a`, the shifted second factor in the words `(bhi, blo)` and the 128-bit accumulator in the
  words `(hi, lo)`, then reduced (`mulShift_eq`);
* `mulWords` is the product, and `mul_eq_mulWords` is the `@[csimp]` lemma that compiles
  `BF64.mul` as `mulWords`.

A `@[csimp]` lemma acts on code compiled where it is visible. CompPoly's instances, its inverse,
and the extension field's operations specialised to them were compiled without it, so the
instances are restated here, each by a `@[csimp]` lemma proved by `rfl`.

This is a candidate for CompPoly. It lives in `Parameters` rather than `Protocol/ToCompPoly`
because `LeanVM.Spec.Field` imports it: every module of the repository then compiles `K`
and `E` arithmetic on words, including the closed constants of `Parameters.Flock`, which are
evaluated when a program starts. Nothing here transcribes a source.
-/

namespace BF64

open BinaryField Polynomial

@[expose] public section

/-! ## Pairs of words -/

/-- The 128-bit value of a pair of words, high word first. -/
def wordsToBitVec (w : UInt64 × UInt64) : BitVec 128 := w.1.toBitVec ++ w.2.toBitVec

/-- The `xor` of two pairs of words is the `xor` of their values. -/
theorem wordsToBitVec_xor (hi lo hi' lo' : UInt64) :
    wordsToBitVec (hi ^^^ hi', lo ^^^ lo') =
      wordsToBitVec (hi, lo) ^^^ wordsToBitVec (hi', lo') := by
  simp only [wordsToBitVec, UInt64.toBitVec_xor]
  rw [BitVec.xor_append]

/-- A word, widened, is the pair `(0, b)`. -/
theorem wordsToBitVec_zero_left (b : UInt64) :
    wordsToBitVec (0, b) = zeroExtendTo (w := 128) b.toBitVec := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [wordsToBitVec, zeroExtendTo, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
  split_ifs with h1
  · simp [hk]
  · simp [BitVec.getLsbD_of_ge b.toBitVec k (by omega)]

/-- Shifting a pair of words left by one bit. -/
theorem wordsToBitVec_shiftLeft_one (hi lo : UInt64) :
    wordsToBitVec ((hi <<< 1) ||| (lo >>> 63), lo <<< 1) = wordsToBitVec (hi, lo) <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [wordsToBitVec, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight, BitVec.getLsbD_or]
  simp
  rcases (show k < 64 ∨ k = 64 ∨ 64 < k by omega) with h1 | h1 | h1
  · simp [h1, hk, show k - 1 < 64 by omega]
  · subst h1
    simp
  · rw [BitVec.getLsbD_of_ge lo.toBitVec (63 + (k - 64)) (by omega)]
    simp [show ¬ k < 64 by omega, show ¬ k - 1 < 64 by omega, show k - 64 < 64 by omega,
      show k - 64 ≠ 0 by omega, show k ≠ 0 by omega, show k - 64 - 1 = k - 1 - 64 by omega, hk]

/-- The mask of `mulShift`: all ones if the low bit of `a` is set, zero otherwise. -/
theorem and_mask (x a : UInt64) :
    x &&& (0 - (a &&& 1)) = if a.toBitVec.getLsbD 0 then x else 0 := by
  have hbit : a &&& 1 = if a.toBitVec.getLsbD 0 then 1 else 0 := by
    rw [← UInt64.toBitVec_inj]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0
      cases h : a.toBitVec.getLsbD 0 <;> simpa [BitVec.getLsbD_eq_getElem] using h
    · cases h : a.toBitVec.getLsbD 0 <;> simp [hk0]
  rw [hbit]
  split
  · rw [← UInt64.toBitVec_inj]
    simp only [UInt64.toBitVec_and]
    rw [show (0 - 1 : UInt64).toBitVec = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
  · simp

/-! ## The reduction -/

/-- The low word of `h · (x^4 + x^3 + x + 1)`. -/
def tailLow (h : UInt64) : UInt64 := h ^^^ (h <<< 1) ^^^ (h <<< 3) ^^^ (h <<< 4)

/-- The high word of `h · (x^4 + x^3 + x + 1)`. -/
def tailHigh (h : UInt64) : UInt64 := (h >>> 63) ^^^ (h >>> 61) ^^^ (h >>> 60)

/-- Polynomials of bit vectors determine them. -/
theorem bitVec_toPoly_injective {w : ℕ} : Function.Injective (toPoly (w := w)) := by
  intro x y hxy
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have := congrArg (fun p ↦ p.coeff k) hxy
  simp only [toPoly_coeff, hk, ↓reduceDIte] at this
  have hx : x.getLsb ⟨k, hk⟩ = x.getLsbD k := rfl
  have hy : y.getLsb ⟨k, hk⟩ = y.getLsbD k := rfl
  rw [hx, hy] at this
  cases hxk : x.getLsbD k <;> cases hyk : y.getLsbD k <;> simp_all

/-- A shifted word, widened, as a pair of words (`0 < j < 64`), the shifts given as words. -/
theorem zeroExtendTo_shiftLeft' (b s t : UInt64) {j : ℕ} (hs : s.toNat = 64 - j)
    (ht : t.toNat = j) (h0 : 0 < j) (h : j < 64) :
    zeroExtendTo (w := 128) b.toBitVec <<< j = wordsToBitVec (b >>> s, b <<< t) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hs' : (s.toBitVec % 64).toNat = 64 - j := by
    rw [BitVec.toNat_umod, UInt64.toNat_toBitVec, hs]; simp; omega
  have ht' : (t.toBitVec % 64).toNat = j := by
    rw [BitVec.toNat_umod, UInt64.toNat_toBitVec, ht]; simp; omega
  simp only [wordsToBitVec, zeroExtendTo, BitVec.getLsbD_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_append,
    BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, hs', ht']
  split_ifs with h1
  · by_cases h2 : k < j
    · simp [h2]
    · simp [h2, hk, show k - j < 128 by omega, h1]
  · by_cases h2 : k - j < 64
    · rw [show 64 - j + (k - 64) = k - j by omega]
      simp [show ¬ k < j by omega, show k - j < 128 by omega, hk]
    · rw [BitVec.getLsbD_of_ge b.toBitVec (64 - j + (k - 64)) (by omega)]
      simp [BitVec.getLsbD_of_ge b.toBitVec (k - j) (by omega)]

/-- **The product by the reduction constant, as shifts.** -/
theorem carryLessMul_reductionConstant (h : UInt64) :
    carryLessMul (w := 128) h.toBitVec reductionConstant =
      wordsToBitVec (tailHigh h, tailLow h) := by
  have hsplit : wordsToBitVec (tailHigh h, tailLow h) =
      wordsToBitVec (0, h) ^^^ wordsToBitVec (h >>> 63, h <<< 1) ^^^
        wordsToBitVec (h >>> 61, h <<< 3) ^^^ wordsToBitVec (h >>> 60, h <<< 4) := by
    simp only [← wordsToBitVec_xor, tailHigh, tailLow, UInt64.zero_xor]
  rw [hsplit, wordsToBitVec_zero_left,
    ← zeroExtendTo_shiftLeft' h 63 1 (j := 1) rfl rfl (by omega) (by omega),
    ← zeroExtendTo_shiftLeft' h 61 3 (j := 3) rfl rfl (by omega) (by omega),
    ← zeroExtendTo_shiftLeft' h 60 4 (j := 4) rfl rfl (by omega) (by omega)]
  apply bitVec_toPoly_injective
  have hlt : (zeroExtendTo (w := 128) h.toBitVec).toNat < 2 ^ 64 := by
    rw [toNat_zeroExtendTo _ (by omega)]; exact h.toBitVec.isLt
  simp only [toPoly_xor, toPoly_carryLessMul _ _ (show 64 + 64 ≤ 128 by omega),
    toPoly_reductionConstant, baseTail_eq,
    toPoly_shiftLeft_no_overflow _ hlt (show 64 + 1 ≤ 128 by omega),
    toPoly_shiftLeft_no_overflow _ hlt (show 64 + 3 ≤ 128 by omega),
    toPoly_shiftLeft_no_overflow _ hlt (show 64 + 4 ≤ 128 by omega),
    toPoly_zeroExtendTo _ (show 64 ≤ 128 by omega)]
  ring

/-- `BF64.reduce` on the words `(hi, lo)` of a 128-bit value: two folds of the high part by
`x^64 = x^4 + x^3 + x + 1`; the first leaves at most four high bits, `tailHigh hi`, and the
second none. -/
def reduceWords (hi lo : UInt64) : UInt64 := lo ^^^ tailLow hi ^^^ tailLow (tailHigh hi)

/-- **`reduceWords` is `BF64.reduce`.** -/
theorem reduceWords_eq (hi lo : UInt64) :
    (reduceWords hi lo).toBitVec = reduce (wordsToBitVec (hi, lo)) := by
  have hhigh : ∀ p : UInt64 × UInt64, highHalf (wordsToBitVec p) = p.1.toBitVec := by
    intro p
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [highHalf, wordsToBitVec, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, hk,
      decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_right (by omega), Nat.add_sub_cancel_left]
  have hlow : ∀ p : UInt64 × UInt64, lowHalf (wordsToBitVec p) = p.2.toBitVec := by
    intro p
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [lowHalf, wordsToBitVec, BitVec.getLsbD_setWidth, hk, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append, ite_eq_left hk]
  have hfold : ∀ p : UInt64 × UInt64,
      foldStep (wordsToBitVec p) = wordsToBitVec (tailHigh p.1, tailLow p.1 ^^^ p.2) := by
    intro p
    rw [foldStep, hhigh, hlow, carryLessMul_reductionConstant, ← wordsToBitVec_zero_left,
      ← wordsToBitVec_xor,
      UInt64.xor_zero]
  rw [reduce, hfold, hfold, hlow]
  simp only [reduceWords, UInt64.toBitVec_xor]
  ac_rfl

/-! ## The product -/

/-- Step `j` of the fold `carryLessMul (w := 128) a b`: add `b·x^j` if bit `j` of `a` is set. -/
def clmulStep (a b : BitVec 64) (acc : BitVec 128) (j : Fin 64) : BitVec 128 :=
  if a.getLsbD j then acc ^^^ (zeroExtendTo (w := 128) b <<< (j : ℕ)) else acc

/-- The fold changes nothing from a bit of `a` on which every higher bit is clear. -/
theorem loop_clmulStep_of_clear (a b : BitVec 64) (acc : BitVec 128) (i : ℕ)
    (h : ∀ j, i ≤ j → j < 64 → a.getLsbD j = false) :
    Fin.foldl.loop 64 (clmulStep a b) acc i = acc := by
  rw [Fin.foldl.loop.eq_1]
  by_cases hi : i < 64
  · rw [dite_eq_left hi, clmulStep, h i le_rfl hi]
    exact loop_clmulStep_of_clear a b acc (i + 1) fun j hj ↦ h j (by omega)
  · rw [dite_eq_right hi]
termination_by 64 - i

/-- If `a >>> i` is zero, the bits of `a` from `i` on are clear. -/
theorem getLsbD_of_ushiftRight_eq_zero (a : BitVec 64) {i : ℕ} (h : a >>> i = 0) :
    ∀ j, i ≤ j → j < 64 → a.getLsbD j = false := by
  intro j hij _
  have := congrArg (fun v : BitVec 64 ↦ v.getLsbD (j - i)) h
  simpa [BitVec.getLsbD_ushiftRight, show i + (j - i) = j by omega] using this

/-- The product from the bits `a` of the first factor not yet added, the second factor shifted
alongside as the words `(bhi, blo)`, into the accumulator `(hi, lo)`, then reduced: the low bit
of `a` adds `(bhi, blo)`, masked rather than branched on, and the loop stops when `a` is
exhausted. -/
def mulShift (a bhi blo hi lo : UInt64) : UInt64 :=
  if a = 0 then reduceWords hi lo
  else
    let mask := 0 - (a &&& 1)
    mulShift (a >>> 1) ((bhi <<< 1) ||| (blo >>> 63)) (blo <<< 1) (hi ^^^ (bhi &&& mask))
      (lo ^^^ (blo &&& mask))
termination_by a.toNat
decreasing_by
  rename_i h
  have : a.toNat ≠ 0 := fun h0 ↦ h (UInt64.toNat_inj.mp (by simpa using h0))
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- **`mulShift` is the fold of `carryLessMul` from bit `i`, reduced**, when `a'` holds the bits
of `a` from `i` on and `(bhi, blo)` is `b·x^i`. -/
theorem mulShift_eq (a b a' bhi blo hi lo : UInt64) (i : ℕ)
    (ha : a'.toBitVec = a.toBitVec >>> i)
    (hb : wordsToBitVec (bhi, blo) = zeroExtendTo (w := 128) b.toBitVec <<< i) :
    (mulShift a' bhi blo hi lo).toBitVec =
      reduce (Fin.foldl.loop 64 (clmulStep a.toBitVec b.toBitVec) (wordsToBitVec (hi, lo)) i) := by
  rw [mulShift]
  by_cases h0 : a' = 0
  · rw [ite_eq_left h0, reduceWords_eq,
      loop_clmulStep_of_clear _ _ _ _ (getLsbD_of_ushiftRight_eq_zero _ (by rw [← ha, h0]; rfl))]
  · rw [ite_eq_right h0]
    have hlt : i < 64 := by
      by_contra hge
      apply h0
      apply UInt64.toBitVec_inj.mp
      rw [ha]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge a.toBitVec (i + k) (by omega)]
    have hbit : a'.toBitVec.getLsbD 0 = a.toBitVec.getLsbD i := by
      rw [ha, BitVec.getLsbD_ushiftRight, Nat.add_zero]
    have hacc :
        wordsToBitVec (hi ^^^ (bhi &&& (0 - (a' &&& 1))), lo ^^^ (blo &&& (0 - (a' &&& 1)))) =
          clmulStep a.toBitVec b.toBitVec (wordsToBitVec (hi, lo)) ⟨i, hlt⟩ := by
      rw [and_mask, and_mask, hbit, clmulStep]
      cases a.toBitVec.getLsbD i
      · simp
      · simp [wordsToBitVec_xor, hb]
    have ha' : (a' >>> 1).toBitVec = a.toBitVec >>> (i + 1) := by
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp [UInt64.toBitVec_shiftRight, ha, BitVec.getLsbD_ushiftRight, Nat.add_assoc,
        Nat.add_comm 1 k]
    have hb' : wordsToBitVec ((bhi <<< 1) ||| (blo >>> 63), blo <<< 1) =
        zeroExtendTo (w := 128) b.toBitVec <<< (i + 1) := by
      rw [wordsToBitVec_shiftLeft_one, hb, BitVec.shiftLeft_add]
    rw [mulShift_eq a b _ _ _ _ _ (i + 1) ha' hb', hacc, Fin.foldl.loop.eq_1 64 _ _ i,
      dite_eq_left hlt]
termination_by a'.toNat
decreasing_by
  have : a'.toNat ≠ 0 := fun h ↦ h0 (UInt64.toNat_inj.mp (by simpa using h))
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- The product of two field elements on words, the loop running over the bits of the smaller
word. -/
def mulWords (a b : BF64) : BF64 :=
  let x := UInt64.ofBitVec a.toBitVec
  let y := UInt64.ofBitVec b.toBitVec
  ofBitVec (if x ≤ y then mulShift x 0 y 0 0 else mulShift y 0 x 0 0).toBitVec

/-- `BF64.mul` is the reduced loop. -/
theorem mul_eq_mulShift (a b : BF64) :
    mul a b = ofBitVec
      (mulShift (UInt64.ofBitVec a.toBitVec) 0 (UInt64.ofBitVec b.toBitVec) 0 0).toBitVec := by
  have h := mulShift_eq (UInt64.ofBitVec a.toBitVec) (UInt64.ofBitVec b.toBitVec)
    (UInt64.ofBitVec a.toBitVec) 0 (UInt64.ofBitVec b.toBitVec) 0 0 0 (by simp)
    (by rw [wordsToBitVec_zero_left]; simp)
  rw [h, mul]
  rfl

/-- **The word-level product is `BF64.mul`**, and compiles in its place. -/
@[csimp] theorem mul_eq_mulWords : @mul = @mulWords := by
  funext a b
  rw [mulWords]
  split
  · exact mul_eq_mulShift a b
  · rw [← mul_eq_mulShift, ← mul_def, ← mul_def, mul_comm]

/-! ## The instances, compiled with the word-level product

CompPoly's instances and its inverse were compiled before `mul_eq_mulWords` existed and call the
bit-vector product. Each declaration below is the CompPoly one restated, so that it is compiled
here, and the lemma equating them, by `rfl` (an induction for the recursive `powTwoPow`),
compiles the CompPoly one as the restatement wherever it is visible. -/

/-- `BF64.instMul`, restated. -/
@[instance_reducible] def instMulWords : Mul BF64 := ⟨mul⟩

/-- `BF64.instMul` compiles as its restatement. -/
@[csimp] theorem instMul_eq_instMulWords : @instMul = @instMulWords := rfl

/-- `BF64.powTwoPow`, restated. -/
def powTwoPowWords (a : BF64) : ℕ → BF64
  | 0 => a
  | n + 1 => powTwoPowWords (a * a) n

/-- `BF64.powTwoPow` compiles as its restatement. -/
@[csimp] theorem powTwoPow_eq_powTwoPowWords : @powTwoPow = @powTwoPowWords := by
  funext a k
  induction k generalizing a with
  | zero => rfl
  | succ n ih => exact ih (a * a)

/-- `BF64.invItohTsujii`, restated. -/
def invWords (a : BF64) : BF64 :=
  if a = 0 then 0 else
    let u1 := a
    let u2 := powTwoPow u1 1 * u1
    let u3 := powTwoPow u2 1 * u1
    let u6 := powTwoPow u3 3 * u3
    let u7 := powTwoPow u6 1 * u1
    let u14 := powTwoPow u7 7 * u7
    let u15 := powTwoPow u14 1 * u1
    let u30 := powTwoPow u15 15 * u15
    let u31 := powTwoPow u30 1 * u1
    let u62 := powTwoPow u31 31 * u31
    let u63 := powTwoPow u62 1 * u1
    u63 * u63

/-- `BF64.invItohTsujii` compiles as its restatement. -/
@[csimp] theorem invItohTsujii_eq_invWords : @invItohTsujii = @invWords := rfl

/-- `BF64.instInv`, restated. -/
@[instance_reducible] def instInvWords : Inv BF64 := ⟨invItohTsujii⟩

/-- `BF64.instInv` compiles as its restatement. -/
@[csimp] theorem instInv_eq_instInvWords : @instInv = @instInvWords := rfl

/-- `BF64.instCommRing`, restated: its product is `BF64.instMul`. -/
@[instance_reducible] def instCommRingWords : CommRing BF64 :=
  { instCommRing with toMul := instMul }

/-- `BF64.instCommRing` compiles as its restatement. -/
@[csimp] theorem instCommRing_eq_instCommRingWords : @instCommRing = @instCommRingWords := rfl

/-- `BF64.instField`, restated: its ring is `BF64.instCommRing` and its inverse
`BF64.invItohTsujii`. -/
@[instance_reducible] def instFieldWords : Field BF64 :=
  { instField with
    toCommRing := instCommRing
    inv := invItohTsujii
    div := fun a b ↦ a * invItohTsujii b }

/-- `BF64.instField` compiles as its restatement. -/
@[csimp] theorem instField_eq_instFieldWords : @instField = @instFieldWords := rfl

end

end BF64
