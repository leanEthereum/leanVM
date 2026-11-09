/-
  LeanVM.Guest.Pow

  Powers of `g` for the kernel: `g^e` as the product of five table entries, one per hexadecimal
  digit of `e`, and the check of a search tree of powers by it.
-/

module

public import LeanVM.Guest.ExecCore
public import LeanVM.Guest.Data.Pows

/-!
# Powers of `g` by digits

The kernel evaluates `gpow e` by square-and-multiply, some thirty products of `K` for an
exponent of the guest's code size. `gpowW e` takes five, one per hexadecimal digit of `e < 2^20`,
from the table `Data.gtab` of the words `g^(d·16^w)` (`gw_eq`, decided once), so that
`PowTree.OkW`, the check of every pair of a search tree by `gpowW`, costs a fraction of
`PowTree.Ok`, which it implies (`PowTree.ok_of_okW`).
-/

namespace LeanVM.Guest.Pow

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Exec

@[expose] public section

/-- `g^(d·16^w)`, from the table. -/
def gw (w d : ℕ) : K := K.ofBits (listElementOrDefault (listElementOrDefault Data.gtab w []) d 0)

/-- `g^e` for `e < 2^20`, by the hexadecimal digits of `e`. -/
def gpowW (e : ℕ) : K :=
  gw 0 (e % 16) * gw 1 (e / 16 % 16) * gw 2 (e / 256 % 16) * gw 3 (e / 4096 % 16) *
    gw 4 (e / 65536 % 16)

theorem gw_eq : ∀ w < 5, ∀ d < 16, gw w d = addressOfIndex (d * 16 ^ w) := by decide +kernel

theorem gpowW_eq {e : ℕ} (h : e < 2 ^ 20) : gpowW e = addressOfIndex e := by
  unfold gpowW
  rw [gw_eq 0 (by decide) _ (Nat.mod_lt _ (by decide)), gw_eq 1 (by decide) _ (Nat.mod_lt _ (by decide)),
    gw_eq 2 (by decide) _ (Nat.mod_lt _ (by decide)), gw_eq 3 (by decide) _ (Nat.mod_lt _ (by decide)),
    gw_eq 4 (by decide) _ (Nat.mod_lt _ (by decide)), addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex, addressOfIndex,
    ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-! ## Products on words in `ℕ`, for the kernel

The kernel evaluates a product of `K` bit by bit, through `BitVec` and a well-founded fold.
`mulN` is the product on the words of `K` as `ℕ`, by the loop of `BF64.mulShift`
(`Statement.Fast.FieldWords`) on `ℕ` operations the kernel evaluates natively (`ofBits_mulN`), and
`gpowN` is `gpowW` by it (`ofBits_gpowN`). -/

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

/-- `gw` as a word in `ℕ`. -/
def gwN (w d : ℕ) : ℕ := listElementOrDefault (listElementOrDefault Data.gtab w []) d 0

/-- `gpowW` on words in `ℕ`. -/
def gpowN (e : ℕ) : ℕ :=
  mulN (mulN (mulN (mulN (gwN 0 (e % 16)) (gwN 1 (e / 16 % 16))) (gwN 2 (e / 256 % 16)))
    (gwN 3 (e / 4096 % 16))) (gwN 4 (e / 65536 % 16))

/-- **`gpowN` is `gpowW`.** -/
theorem ofBits_gpowN (e : ℕ) : K.ofBits (gpowN e) = gpowW e := by
  simp only [gpowN, ofBits_mulN]
  rfl

end
end LeanVM.Guest.Pow

namespace LeanVM.Guest.Exec

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Pow

@[expose] public section

/-- Every pair of the tree is a power of `g` below `2^20`, by digits. -/
def PowTree.OkW : PowTree → Prop
  | .leaf => True
  | .node k e l r => e < 2 ^ 20 ∧ K.ofBits k = gpowW e ∧ l.OkW ∧ r.OkW

/-- `PowTree.OkW` is decided pair by pair. -/
def PowTree.decOkW : (t : PowTree) → Decidable t.OkW
  | .leaf => isTrue trivial
  | .node k e l r =>
    haveI := PowTree.decOkW l
    haveI := PowTree.decOkW r
    inferInstanceAs (Decidable (e < 2 ^ 20 ∧ K.ofBits k = gpowW e ∧ l.OkW ∧ r.OkW))

instance (t : PowTree) : Decidable t.OkW := PowTree.decOkW t

/-- `PowTree.OkW` as a `Bool`, on words in `ℕ` (`gpowN`). -/
def PowTree.okWB : PowTree → Bool
  | .leaf => true
  | .node k e l r => Nat.blt e 1048576 && Nat.beq k (gpowN e) && l.okWB && r.okWB

/-- A pair checked on words is a power of `g` by digits. -/
theorem gpowW_of_beq {k e : ℕ} (h : Nat.beq k (gpowN e) = true) : K.ofBits k = gpowW e := by
  rw [Nat.eq_of_beq_eq_true h, ofBits_gpowN]

/-- **`PowTree.OkW`, decided on words.** -/
theorem PowTree.okW_of_okWB : ∀ {t : PowTree}, t.okWB = true → t.OkW
  | .leaf, _ => trivial
  | .node _ _ _ _, h => by
    simp only [okWB, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨⟨⟨he, hk⟩, hl⟩, hr⟩ := h
    exact ⟨he, gpowW_of_beq hk, okW_of_okWB hl, okW_of_okWB hr⟩

theorem PowTree.ok_of_okW : ∀ {t : PowTree}, t.OkW → t.Ok
  | .leaf, _ => trivial
  | .node _ _ _ _, ⟨he, hk, hl, hr⟩ => ⟨hk.trans (gpowW_eq he), ok_of_okW hl, ok_of_okW hr⟩

end
end LeanVM.Guest.Exec
