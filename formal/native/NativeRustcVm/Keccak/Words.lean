module

public import Native.Keccak.Lanes
public import NativeVm.Model.Verify

/-!
# `keccak256_words`, transcribed

`rustc/vm/src/keccak.rs`'s `keccak256_words(count, len, word)` on lanes: from the zero state,
each whole block XORs its 17 words into the rate and permutes (`wordBlocks`); the last XORs the
remaining 17 words and the padding (`padLane`: `PAD_FIRST`, `1`, at byte `len % 136`, `PAD_LAST`,
`0x80`, at byte 135) and permutes (`finalState`); the digest is the first four lanes
(`keccak256Words`). Word `i` is `word i` below `count`, `0` past it.

Where the words hold `len` bytes (`HoldsBytes`, the bytes past `len` zero), this is Keccak-256 of
the bytes (`finalState_eq`, `keccak256Words_eq`): the sponge of `keccak256` absorbs the same
lanes (`Native.Keccak.Proof.lane_block`, `lane_padBlock`). Hence the model's `hashWords`
(`hashWords_eq`) and `fiatShamirIv` (`fiatShamirIv_eq`, its words `ivWords` held in `9 + 8 n`
bytes, `holdsBytes_ivWords`, and word `k` of them `ivWord`, `iv_word`'s, `getD_ivWords`).
-/

namespace NativeRustcVm.Keccak

open LeanVM.Semantics LeanVM.Protocol.KeccakHash Native.Keccak Native.Keccak.Proof NativeVm.Model

@[expose] public section

/-- The state after the first `n` whole blocks of the words `w`. -/
def wordBlocks (w : Nat → UInt64) : Nat → KeccakState
  | 0 => Vector.replicate 25 0
  | n + 1 => keccakF1600 (xorRate (wordBlocks w n) fun k ↦ w (17 * n + k))

/-- The padding's lane `k` for `len` bytes: `1` at byte `len % 136`, `0x80` at byte 135. -/
def padLane (len k : Nat) : UInt64 :=
  (if k = len % 136 / 8 then 1 <<< (8 * (len % 136 % 8)).toUInt64 else 0) ^^^
    (if k = 16 then 0x8000000000000000 else 0)

/-- The state after the padded last block. -/
def finalState (w : Nat → UInt64) (len : Nat) : KeccakState :=
  keccakF1600 (xorRate (wordBlocks w (len / 136)) fun k ↦ w (17 * (len / 136) + k) ^^^ padLane len k)

/-- **`keccak256_words(count, len, word)`**: the first four lanes of the final state. -/
def keccak256Words (count len : Nat) (word : Nat → UInt64) : LeanVM.Protocol.Digest :=
  Vector.ofFn fun i : Fin 4 ↦
    Keccak.lane (finalState (fun i ↦ if i < count then word i else 0) len) i

/-- Word `k` of `ivWords bc`, as `iv_word(bc, k)` computes it: `tagLow`, then the top byte of word
`k - 1` of `ext` and the low seven of word `k`, `ext` the tag's ninth byte then the bytecode. -/
def ivWord (bc : List UInt64) (k : Nat) : UInt64 :=
  let ext := fun i ↦ if i = 0 then tagLast <<< 56 else bc.getD (i - 1) 0
  if k = 0 then tagLow else (ext (k - 1) >>> 56) ||| (ext k <<< 8)

end

public section

variable {ws : List UInt64} {len : Nat}

/-- After `j` of the `len / 136` whole blocks, the rest of `keccak256`'s absorption. -/
theorem absorbWith_blocks (hb : HoldsBytes ws len) {w : Nat → UInt64}
    (hw : ∀ i, w i = ws.getD i 0) (j : Nat) (hj : j ≤ len / 136) :
    absorbWith perm (len / 136) (Vector.replicate 25 0) ((wordsBytes ws).take len) =
      absorbWith perm (len / 136 - j) (wordBlocks w j) (((wordsBytes ws).take len).drop (136 * j)) := by
  induction j with
  | zero =>
    rw [Nat.sub_zero, Nat.mul_zero, List.drop_zero]
    rfl
  | succ j ih =>
    rw [ih (by omega), show len / 136 - j = (len / 136 - (j + 1)) + 1 by omega, absorbWith_succ,
      List.drop_drop, show 136 * j + 136 = 136 * (j + 1) by omega]
    have hx : xorRate (wordBlocks w j) (littleEndianLane
        ((((wordsBytes ws).take len).drop (136 * j)).take 136)) =
        xorRate (wordBlocks w j) fun k ↦ w (17 * j + k) :=
      xorRate_congr _ fun k hk ↦ by rw [lane_block hb j hk, hw]
    rw [hx]
    rfl

/-- **The final state is `keccak256`'s.** -/
theorem finalState_eq (hb : HoldsBytes ws len) {w : Nat → UInt64} (hw : ∀ i, w i = ws.getD i 0) :
    finalState w len =
      absorbWith perm (len / 136) (Vector.replicate 25 0) ((wordsBytes ws).take len) := by
  rw [absorbWith_blocks hb hw (len / 136) le_rfl, Nat.sub_self, absorbWith_zero, finalState]
  have hx : xorRate (wordBlocks w (len / 136)) (littleEndianLane
      (padBlock (((wordsBytes ws).take len).drop (136 * (len / 136))))) =
      xorRate (wordBlocks w (len / 136)) fun k ↦ w (17 * (len / 136) + k) ^^^ padLane len k :=
    xorRate_congr _ fun k hk ↦ by rw [lane_padBlock hb hk, hw, padLane, UInt64.xor_assoc]
  rw [hx]

/-- **`keccak256_words` is Keccak-256** of the `len` bytes its words hold. -/
theorem keccak256Words_eq (hb : HoldsBytes ws len) {count : Nat} {word : Nat → UInt64}
    (hw : ∀ i, (if i < count then word i else 0) = ws.getD i 0) :
    keccak256Words count len word = keccak256 ((wordsBytes ws).take len) := by
  apply Vector.ext
  intro i hi
  rw [keccak256Words, Vector.getElem_ofFn, keccak256_lane _ hi, length_held hb,
    finalState_eq hb hw]

/-- Words hold their own bytes. -/
theorem holdsBytes_self (ws : List UInt64) : HoldsBytes ws (8 * ws.length) := by
  refine ⟨by omega, fun b hb ↦ ?_⟩
  rw [List.drop_eq_nil_of_le (by rw [length_wordsBytes])] at hb
  cases hb

/-- **`hashWords`** is `keccak256_words(n, 8 n, ws[·])`. -/
theorem hashWords_eq (ws : List UInt64) :
    hashWords ws.toArray = keccak256Words ws.length (8 * ws.length) fun i ↦ ws.getD i 0 := by
  rw [keccak256Words_eq (holdsBytes_self ws) fun i ↦ by
      split
      · rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl]
  rw [hashWords, List.take_of_length_le (by rw [length_wordsBytes])]

theorem ivWord_succ (bc : List UInt64) (j : Nat) :
    ivWord bc (j + 1) =
      ((if j = 0 then tagLast <<< 56 else bc.getD (j - 1) 0) >>> 56) ||| (bc.getD j 0 <<< 8) := by
  simp [ivWord]

theorem getD_eq_zero {bc : List UInt64} {i : Nat} (h : bc.length ≤ i) : bc.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

theorem getElem?_append_zero (bc : List UInt64) (j : Nat) :
    (bc ++ [0])[j]?.getD 0 = bc[j]?.getD 0 := by
  by_cases h : j < bc.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (show bc.length ≤ j by omega)]
    cases j - bc.length <;> simp

theorem getElem?_ext (bc : List UInt64) (j : Nat) :
    (tagLast <<< 56 :: (bc ++ [0]))[j]?.getD 0 =
      if j = 0 then tagLast <<< 56 else bc[j - 1]?.getD 0 := by
  rcases j with _ | j
  · simp
  · simp [getElem?_append_zero]

/-- **Word `k` of `ivWords`** is `ivWord`. -/
theorem getD_ivWords (bc : List UInt64) (k : Nat) :
    (ivWords bc.toArray).toList.getD k 0 = ivWord bc k := by
  rcases k with _ | j
  · simp [ivWords, ivWord]
  · rw [ivWord_succ]
    by_cases hj : j < bc.length + 1
    · simp [ivWords, hj, getElem?_ext, List.getD_eq_getElem?_getD]
      have := getElem?_append_zero bc j
      rw [List.getElem?_eq_getElem (by simp; omega), Option.getD_some] at this
      rw [this]
    · rw [getD_eq_zero (show bc.length ≤ j by omega), getD_eq_zero (show bc.length ≤ j - 1 by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [ivWords]; omega)]
      simp [show j ≠ 0 by omega]

/-- A word shifted right by 56 has no byte past its first. -/
theorem toUInt8_shift56 (x : UInt64) {r : Nat} (h1 : 1 ≤ r) (h8 : r < 8) :
    (x >>> 56 >>> (8 * r).toUInt64).toUInt8 = 0 := by
  apply UInt8.toNat_inj.mp
  have hx := x.toNat_lt
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h56 : (56 : UInt64).toNat % 64 = 56 := rfl
  rw [h56]
  interval_cases r <;> simp <;> omega

theorem getElem_eq_getD' (l : List UInt8) {p : Nat} (h : p < l.length) : l[p] = l.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- `ivWords` holds `9 + 8 n` bytes. -/
theorem holdsBytes_ivWords (bc : List UInt64) :
    HoldsBytes (ivWords bc.toArray).toList (9 + 8 * bc.length) := by
  have hlen : (ivWords bc.toArray).toList.length = bc.length + 2 := by
    simp [ivWords]
  refine ⟨by rw [hlen]; omega, fun b hb ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  rw [List.getElem_drop, getElem_eq_getD', getD_wordsBytes, getD_ivWords]
  obtain ⟨q, hq⟩ : ∃ q, (9 + 8 * bc.length + i) / 8 = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos
    (show 0 < (9 + 8 * bc.length + i) / 8 by omega)).symm⟩
  rw [hq, ivWord_succ]
  by_cases hq' : q = bc.length
  · subst hq'
    rw [getD_eq_zero le_rfl, show (0 : UInt64) <<< 8 = 0 from rfl, UInt64.or_zero]
    exact toUInt8_shift56 _ (by omega) (by omega)
  · rw [getD_eq_zero (show bc.length ≤ q by omega), getD_eq_zero (show bc.length ≤ q - 1 by omega)]
    simp [show q ≠ 0 by omega]

/-- **`fiatShamirIv`** is `keccak256_words(n + 2, 9 + 8 n, iv_word)`. -/
theorem fiatShamirIv_eq (bc : List UInt64) :
    fiatShamirIv bc.toArray = keccak256Words (bc.length + 2) (9 + 8 * bc.length) (ivWord bc) := by
  rw [keccak256Words_eq (holdsBytes_ivWords bc) fun i ↦ by
      rw [getD_ivWords]
      split
      · rfl
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [ivWord_succ, getD_eq_zero (show bc.length ≤ j by omega),
          getD_eq_zero (show bc.length ≤ j - 1 by omega)]
        simp [show j ≠ 0 by omega]]
  rfl

end

end NativeRustcVm.Keccak
