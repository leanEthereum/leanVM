/-
  LeanVM.Guest.PowWords

  Products and powers of `K` on its words as natural numbers, for the kernel.
-/

module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.Word

/-!
# Products on words in `ℕ`

The kernel evaluates a product of `K` bit by bit, through `BitVec` and a well-founded fold.
`mulN` is the product on the words of `K` as `ℕ`, by the loop of `BF64.mulShift`
(`FastFields.FieldWords`) on `ℕ` operations the kernel evaluates natively (`ofBits_mulN`), and
`powN e` is `g^e` by square-and-multiply on them, for `e < 2^64` (`ofBits_powN`).
-/

namespace LeanVM.Guest.Pow

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- `2^64`. -/
def w64 : ℕ := 18446744073709551616

/-- `BF64.tailLow` on a word in `ℕ`. -/
def tailLowN (h : ℕ) : ℕ := h ^^^ (h <<< 1) % w64 ^^^ (h <<< 3) % w64 ^^^ (h <<< 4) % w64

/-- `BF64.tailHigh` on a word in `ℕ`. -/
def tailHighN (h : ℕ) : ℕ := (h >>> 63) ^^^ (h >>> 61) ^^^ (h >>> 60)

/-- `BF64.reduceWords` on words in `ℕ`. -/
def reduceN (hi lo : ℕ) : ℕ := lo ^^^ tailLowN hi ^^^ tailLowN (tailHighN hi)

/-- `BF64.mulShift` on words in `ℕ`, at most `n` steps. -/
def mulShiftN : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, _, hi, lo => reduceN hi lo
  | n + 1, a, bhi, blo, hi, lo =>
    bif Nat.beq a 0 then reduceN hi lo
    else mulShiftN n (a >>> 1) ((bhi <<< 1) % w64 ||| blo >>> 63) ((blo <<< 1) % w64)
      (bif Nat.beq (a % 2) 1 then hi ^^^ bhi else hi) (bif Nat.beq (a % 2) 1 then lo ^^^ blo else lo)

/-- The product of `K.ofBits a` and `K.ofBits b`, on words in `ℕ`. -/
def mulN (a b : ℕ) : ℕ := mulShiftN 64 (a % w64) 0 (b % w64) 0 0

theorem reduceWords_toNat (hi lo : UInt64) :
    (BF64.reduceWords hi lo).toNat = reduceN hi.toNat lo.toNat := by
  simp [BF64.reduceWords, BF64.tailLow, BF64.tailHigh, reduceN, tailLowN, tailHighN, w64]

theorem mulShift_toNat : ∀ (n : ℕ) (a bhi blo hi lo : UInt64), a.toNat < 2 ^ n →
    (BF64.mulShift a bhi blo hi lo).toNat = mulShiftN n a.toNat bhi.toNat blo.toNat hi.toNat lo.toNat
  | n, a, bhi, blo, hi, lo, ha => by
    rw [BF64.mulShift]
    by_cases h0 : a = 0
    · subst h0
      cases n <;> simp [mulShiftN, reduceWords_toNat]
    · rw [ite_eq_right h0]
      have ha0 : a.toNat ≠ 0 := fun h ↦ h0 (UInt64.toNat_inj.mp (by simpa using h))
      obtain _ | n := n
      · simp at ha; omega
      have hbit : a.toBitVec.getLsbD 0 = decide (a.toNat % 2 = 1) := by
        simp [BitVec.getLsbD, Nat.testBit_zero]
      rw [mulShiftN, show Nat.beq a.toNat 0 = false from
          Bool.eq_false_iff.mpr fun h ↦ ha0 (Nat.eq_of_beq_eq_true h),
        Bool.cond_false]
      dsimp only
      rw [BF64.and_mask, BF64.and_mask, hbit,
        mulShift_toNat n _ _ _ _ _ (by simp [Nat.shiftRight_eq_div_pow]; rw [pow_succ] at ha; omega)]
      by_cases hb : a.toNat % 2 = 1
      · simp [hb, w64]
      · simp [hb, w64, show Nat.beq (a.toNat % 2) 1 = false from
          Bool.eq_false_iff.mpr fun h ↦ hb (Nat.eq_of_beq_eq_true h)]

/-- **`mulN` is the product of `K`.** -/
theorem ofBits_mulN (a b : ℕ) : K.ofBits (mulN a b) = K.ofBits a * K.ofBits b := by
  have h := mulShift_toNat 64 (UInt64.ofBitVec (BitVec.ofNat 64 a)) 0
    (UInt64.ofBitVec (BitVec.ofNat 64 b)) 0 0 (UInt64.toNat_lt _)
  have ha : (UInt64.ofBitVec (BitVec.ofNat 64 a)).toNat = a % w64 := by
    show (BitVec.ofNat 64 a).toNat = _
    rw [BitVec.toNat_ofNat]
    rfl
  have hb : (UInt64.ofBitVec (BitVec.ofNat 64 b)).toNat = b % w64 := by
    show (BitVec.ofNat 64 b).toNat = _
    rw [BitVec.toNat_ofNat]
    rfl
  rw [ha, hb, UInt64.toNat_zero] at h
  rw [BF64.mul_def, BF64.mul_eq_mulShift]
  unfold K.ofBits mulN
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, ← h, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]
  rfl

/-- `acc · b^e` on words, by square-and-multiply over at most `f` bits of `e`. -/
def powBinN : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, acc, _ => acc
  | f + 1, b, acc, e =>
      bif Nat.beq e 0 then acc
      else powBinN f (mulN b b) (bif Nat.beq (e % 2) 1 then mulN acc b else acc) (e / 2)

theorem ofBits_powBinN : ∀ (f b acc e : ℕ),
    K.ofBits (powBinN f b acc e) = powBin f (K.ofBits b) (K.ofBits acc) e
  | 0, _, _, _ => rfl
  | f + 1, b, acc, e => by
    simp only [powBinN, powBin]
    by_cases he : e = 0
    · simp [he]
    · have hb : Nat.beq e 0 = false := Bool.eq_false_iff.mpr fun h ↦ he (Nat.eq_of_beq_eq_true h)
      rw [hb, Bool.cond_false]
      simp only [he, ↓reduceIte]
      rw [ofBits_powBinN, ofBits_mulN]
      by_cases h2 : e % 2 = 1
      · rw [show Nat.beq (e % 2) 1 = true from Nat.beq_eq_true_eq _ _ ▸ h2, Bool.cond_true]
        simp only [h2, ↓reduceIte]
        rw [ofBits_mulN]
      · rw [show Nat.beq (e % 2) 1 = false from Bool.eq_false_iff.mpr fun h ↦ h2 (Nat.eq_of_beq_eq_true h),
          Bool.cond_false]
        simp only [h2, ↓reduceIte]

/-- `g^e` on words, `e < 2^64`. -/
def powN (e : ℕ) : ℕ := powBinN 64 2 1 e

/-- **`powN` is the power of `g`.** -/
theorem ofBits_powN {e : ℕ} (h : e < 2 ^ 64) : K.ofBits (powN e) = addressOfIndex e := by
  rw [powN, ofBits_powBinN, powBin_eq 64 _ _ e h, K.ofBits_one, one_mul]
  rfl

end
end LeanVM.Guest.Pow
