/-
  LeanVM.Guest.Backend.Pow

  Powers of `g` for the kernel: the back end's `g^e` (a pooled constant, a pc immediate) as the
  product of five table entries on words in `ℕ`, which the kernel evaluates natively.
-/

module

public import LeanVM.Guest.Word

/-!
# Powers of `g` the kernel evaluates

The kernel evaluates a product of `K` bit by bit, through `BitVec` and a well-founded fold, so
`gpowK e`, square-and-multiply, costs it about a fifth of a second for an exponent of the guest's
code size. `gpowBits e` is the same word: for `e < 2^20` the product of the five entries
`g^(d·16^w)` of `gtab`, one per hexadecimal digit of `e` (`gtab_eq`, decided once), each product
on words in `ℕ` by `BF64.mulShift`'s loop (`mulN`, `ofBits_mulN`), as `Guest.Pow` does for the
certificates' search trees; past `2^20`, `gpowK e`. Compiled code runs `gpowK` (`@[csimp]`).
-/

namespace LeanVM.Guest.Backend

open LeanVM.Parameters LeanVM.Guest

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

/-- `g^(d·16^w)` at row `w`, column `d`, as bits. -/
def gtab : List (List Nat) := [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768],
  [1, 65536, 4294967296, 281474976710656, 27, 1769472, 115964116992, 7599824371187712, 325, 21299200, 1395864371200, 91479367430963200, 7607, 498532352, 32671816220672, 2141180147837960192],
  [1, 69649, 4311744769, 300171238899985, 281474976776218, 1157706583775027617, 72058805673394458, 1156204715243055626, 111669150020, 7777644629218564, 1873527540962903066, 11595395657381178945, 98517633419844840, 17721195178546253661, 1965051239618583364, 13302112368027285652],
  [1, 69052, 4300293456, 296795116402880, 18696262193435, 1285603378200698084, 6148844361094023964, 1599104603538818275, 72058698282434910, 13622451040716083975, 1948140847929922252, 12278025298851535155, 13523939124283682135, 16446658727474387284, 1985021245116858025, 6205059133350569810],
  [1, 98799108396552527, 7508852687479269, 16377646705614971421, 313291816297574, 12363572321019852651, 2051309156788280272, 5085194955728506420, 6076785667380547347, 18121698581730034875, 13538066639024870836, 4836112332347386018, 875272367584978439, 6432764574967583026, 17711403033813346583, 12917757563138364753]]

/-- `g^(d·16^w)`, from the table, as bits. -/
def gw (w d : Nat) : Nat := ((gtab.getD w []).getD d 0)

theorem gtab_eq : ∀ w < 5, ∀ d < 16, K.ofBits (gw w d) = gpowK (d * 16 ^ w) := by decide +kernel

/-- `g^e` for `e < 2^20`, by the hexadecimal digits of `e`, as a word in `ℕ`. -/
def gpowN (e : Nat) : Nat :=
  mulN (mulN (mulN (mulN (gw 0 (e % 16)) (gw 1 (e / 16 % 16))) (gw 2 (e / 256 % 16)))
    (gw 3 (e / 4096 % 16))) (gw 4 (e / 65536 % 16))

/-- The bits of `g^e`. -/
def gpowBits (e : Nat) : Nat :=
  if e < 2 ^ 20 then (K.ofBits (gpowN e)).toBitVec.toNat else (gpowK e).toBitVec.toNat

/-- `gpowBits` as compiled code runs it. -/
def gpowBitsC (e : Nat) : Nat := (gpowK e).toBitVec.toNat

theorem ofBits_gpowN {e : Nat} (h : e < 2 ^ 20) : K.ofBits (gpowN e) = gpowK e := by
  have hk : ∀ k, k < 2 ^ 20 → gpowK k = addressOfIndex k := fun k hk =>
    gpowK_eq (lt_of_lt_of_le hk (by decide))
  simp only [gpowN, ofBits_mulN]
  rw [gtab_eq 0 (by decide) _ (Nat.mod_lt _ (by decide)), gtab_eq 1 (by decide) _ (Nat.mod_lt _ (by decide)),
    gtab_eq 2 (by decide) _ (Nat.mod_lt _ (by decide)), gtab_eq 3 (by decide) _ (Nat.mod_lt _ (by decide)),
    gtab_eq 4 (by decide) _ (Nat.mod_lt _ (by decide)), hk _ (by omega), hk _ (by omega), hk _ (by omega),
    hk _ (by omega), hk _ (by omega), hk _ h, addressOfIndex, addressOfIndex, addressOfIndex,
    addressOfIndex, addressOfIndex, addressOfIndex, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-- **`gpowBits e` is the bits of `g^e`.** -/
@[csimp] theorem gpowBits_eq_C : @gpowBits = @gpowBitsC := by
  funext e
  unfold gpowBits gpowBitsC
  split
  · next h => rw [ofBits_gpowN h]
  · rfl

theorem gpowBits_eq (e : Nat) : gpowBits e = (gpowK e).toBitVec.toNat := by
  rw [gpowBits_eq_C]
  rfl

end
end LeanVM.Guest.Backend
