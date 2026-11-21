module

public import Native.Keccak.Words
public import Statement.Fast.Keccak
public import Mathlib.Tactic.IntervalCases

/-!
# `Keccak.hash`'s proof: Keccak-256 over words

The sponge's blocks read as words: a lane of a byte string is its eight bytes' little-endian word
(`laneOf`, by its bits, `testBit_laneOf`); a lane of words' bytes is the word
(`littleEndianLane_wordsBytes`); a whole block of the hashed bytes is seventeen of the words
(`lane_block`), and the padded last block the remaining words XOR the two padding words
(`lane_padBlock`).
-/

@[expose] public section

namespace Native.Keccak.Proof

open LeanVM.Semantics LeanVM.Protocol.KeccakHash

/-! ## A lane's bits -/

/-- The little-endian word of the eight bytes `f 0, …, f 7`. -/
def laneOf (f : Nat → UInt8) : UInt64 :=
  (List.range 8).foldl (fun acc k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64)) 0

theorem littleEndianLane_eq (bytes : List UInt8) (i : Nat) :
    littleEndianLane bytes i = laneOf fun k ↦ bytes.getD (8 * i + k) 0 := (rfl)

theorem testBit_byte (b : UInt8) {j : Nat} (hj : 8 ≤ j) : b.toNat.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le b.toNat_lt (Nat.pow_le_pow_right (by omega) hj))

theorem testBit_laneOf_aux (f : Nat → UInt8) (m : Nat) (hm : m ≤ 8) (t : Nat) :
    ((List.range m).foldl (fun acc k ↦ acc ||| ((f k).toUInt64 <<< (8 * k).toUInt64))
      0).toNat.testBit t = (decide (t < 8 * m) && (f (t / 8)).toNat.testBit (t % 8)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, UInt64.toNat_or,
      Nat.testBit_or, ih (by omega), UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, UInt8.toNat_toUInt64]
    have h8 : (8 * m).toUInt64.toNat % 64 = 8 * m := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      omega
    rw [h8]
    by_cases h1 : t < 8 * m
    · simp [h1, show t < 8 * (m + 1) by omega, show ¬ 8 * m ≤ t by omega]
    · by_cases h2 : t < 8 * m + 8
      · have hq : t / 8 = m := by omega
        have hr : t % 8 = t - 8 * m := by omega
        simp [h1, show t < 8 * (m + 1) by omega, show 8 * m ≤ t by omega,
          show t < 64 by omega, hq, hr]
      · simp [h1, show ¬ t < 8 * (m + 1) by omega, testBit_byte _ (show 8 ≤ t - 8 * m by omega)]

/-- **A lane's bit `t` is bit `t % 8` of byte `t / 8`.** -/
theorem testBit_laneOf (f : Nat → UInt8) (t : Nat) :
    (laneOf f).toNat.testBit t = (decide (t < 64) && (f (t / 8)).toNat.testBit (t % 8)) :=
  testBit_laneOf_aux f 8 le_rfl t

theorem UInt64.eq_of_testBit {a b : UInt64} (h : ∀ t < 64, a.toNat.testBit t = b.toNat.testBit t) :
    a = b := by
  apply UInt64.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 64
  · exact h t ht
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.toNat_lt (Nat.pow_le_pow_right (by omega)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le b.toNat_lt
      (Nat.pow_le_pow_right (by omega) (by omega)))]

theorem laneOf_congr {f g : Nat → UInt8} (h : ∀ k < 8, f k = g k) : laneOf f = laneOf g :=
  UInt64.eq_of_testBit fun t ht ↦ by
    rw [testBit_laneOf, testBit_laneOf, h _ (by omega)]

/-- The lane of a word's bytes is the word. -/
theorem laneOf_word (w : UInt64) : laneOf (fun k ↦ (w >>> (8 * k).toUInt64).toUInt8) = w :=
  UInt64.eq_of_testBit fun t ht ↦ by
    have h8 : (8 * (t / 8)).toUInt64.toNat % 64 = 8 * (t / 8) := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      omega
    rw [testBit_laneOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8,
      Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [ht, Nat.mod_lt t (by omega : 8 > 0), show 8 * (t / 8) + t % 8 = t by omega]

theorem laneOf_xor (f g : Nat → UInt8) :
    laneOf (fun k ↦ f k ^^^ g k) = laneOf f ^^^ laneOf g :=
  UInt64.eq_of_testBit fun t ht ↦ by
    rw [UInt64.toNat_xor, Nat.testBit_xor, testBit_laneOf, testBit_laneOf, testBit_laneOf,
      UInt8.toNat_xor, Nat.testBit_xor]
    simp [ht]

theorem laneOf_zero : laneOf (fun _ ↦ 0) = 0 :=
  UInt64.eq_of_testBit fun t ht ↦ by simp [testBit_laneOf]

/-- The lane of one byte `b` at position `c`. -/
theorem laneOf_single (b : UInt8) {c : Nat} (hc : c < 8) :
    laneOf (fun k ↦ if k = c then b else 0) = b.toUInt64 <<< (8 * c).toUInt64 :=
  UInt64.eq_of_testBit fun t ht ↦ by
    have h8 : (8 * c).toUInt64.toNat % 64 = 8 * c := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      omega
    rw [testBit_laneOf, UInt64.toNat_shiftLeft, h8, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
      UInt8.toNat_toUInt64]
    by_cases hq : t / 8 = c
    · simp [ht, hq, show 8 * c ≤ t by omega, show t % 8 = t - 8 * c by omega]
    · by_cases hlt : t < 8 * c
      · simp [hq, show ¬ 8 * c ≤ t by omega]
      · simp [hq, ht, testBit_byte _ (show 8 ≤ t - 8 * c by omega)]

/-! ## Bytes of words -/

theorem getD_take (l : List UInt8) (n p : Nat) :
    (l.take n).getD p 0 = if p < n then l.getD p 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  split <;> rfl

theorem getD_drop (l : List UInt8) (n p : Nat) : (l.drop n).getD p 0 = l.getD (n + p) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem length_wordsBytes (ws : List UInt64) : (wordsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [wordsBytes, List.flatMap_cons, List.length_append, ← wordsBytes, ih]
    simp [wordBytes]
    omega

theorem getD_wordsBytes (ws : List UInt64) (p : Nat) :
    (wordsBytes ws).getD p 0 = (ws.getD (p / 8) 0 >>> (8 * (p % 8)).toUInt64).toUInt8 := by
  induction ws generalizing p with
  | nil => simp [wordsBytes]
  | cons w ws ih =>
    have hw : (wordBytes w).length = 8 := by simp [wordBytes]
    rw [wordsBytes, List.flatMap_cons, ← wordsBytes]
    by_cases hp : p < 8
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
      simp [wordBytes, hp, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hw,
        ← List.getD_eq_getElem?_getD, ih, show p / 8 = (p - 8) / 8 + 1 by omega,
        show (p - 8) % 8 = p % 8 by omega]
      simp

/-- **A lane of words' bytes is the word.** -/
theorem littleEndianLane_wordsBytes (ws : List UInt64) (i : Nat) :
    littleEndianLane (wordsBytes ws) i = ws.getD i 0 := by
  rw [littleEndianLane_eq, ← laneOf_word (ws.getD i 0)]
  refine laneOf_congr fun k hk ↦ ?_
  rw [getD_wordsBytes, show (8 * i + k) / 8 = i by omega, show (8 * i + k) % 8 = k by omega]

section Held

variable {ws : List UInt64} {len : Nat}

theorem getD_wordsBytes_of_le (hb : HoldsBytes ws len) {p : Nat} (hp : len ≤ p) :
    (wordsBytes ws).getD p 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : (wordsBytes ws)[p]? with
  | none => rfl
  | some b =>
    have hm : b ∈ (wordsBytes ws).drop len := by
      rw [List.mem_iff_getElem?]
      exact ⟨p - len, by rw [List.getElem?_drop, Nat.add_sub_cancel' hp]; exact h⟩
    simp [hb.2 b hm]

/-- The held bytes read as the words' bytes. -/
theorem getD_held (hb : HoldsBytes ws len) (p : Nat) :
    ((wordsBytes ws).take len).getD p 0 = (wordsBytes ws).getD p 0 := by
  rw [getD_take]
  split
  · rfl
  · rw [getD_wordsBytes_of_le hb (by omega)]

theorem length_held (hb : HoldsBytes ws len) : ((wordsBytes ws).take len).length = len := by
  rw [List.length_take, length_wordsBytes, hb.1]
  omega

/-- A word past the held bytes is zero. -/
theorem getD_words_of_le (hb : HoldsBytes ws len) {i : Nat} (hi : len ≤ 8 * i) :
    ws.getD i 0 = 0 := by
  rw [← littleEndianLane_wordsBytes, littleEndianLane_eq,
    laneOf_congr (g := fun _ ↦ 0) fun k _ ↦ getD_wordsBytes_of_le hb (by omega), laneOf_zero]

/-- **Lane `k` of the `j`-th whole block is word `17 j + k`.** -/
theorem lane_block (hb : HoldsBytes ws len) (j : Nat) {k : Nat} (hk : k < 17) :
    littleEndianLane ((((wordsBytes ws).take len).drop (136 * j)).take 136) k =
      ws.getD (17 * j + k) 0 := by
  rw [← littleEndianLane_wordsBytes, littleEndianLane_eq, littleEndianLane_eq]
  refine laneOf_congr fun t ht ↦ ?_
  rw [getD_take, ite_eq_left (by omega), getD_drop, getD_held hb]
  congr 1
  omega

/-- The padded block's bytes: the remaining bytes, `PAD_FIRST` after them, `PAD_LAST` last. -/
theorem getD_padBlock (rem : List UInt8) (hr : rem.length < 136) {p : Nat} (hp : p < 136) :
    (padBlock rem).getD p 0 = rem.getD p 0 ^^^ (if p = rem.length then 1 else 0) ^^^
      (if p = 135 then 0x80 else 0) := by
  simp only [padBlock, rate, padFirst, padLast, List.getD_eq_getElem?_getD, List.getElem?_modify,
    List.getElem?_append, List.getElem?_replicate]
  by_cases h1 : p < rem.length
  · simp [h1, show ¬ rem.length = p by omega, show ¬ p = rem.length by omega,
      show ¬ 135 = p by omega, show ¬ p = 135 by omega]
  · simp only [h1, ↓reduceIte, show p - rem.length < 136 - rem.length by omega,
      List.getElem?_eq_none (show rem.length ≤ p by omega)]
    by_cases h2 : p = 135
    · subst h2
      by_cases h3 : rem.length = 135
      · simp [h3]
      · simp [h3, Ne.symm h3]
    · by_cases h3 : p = rem.length
      · subst h3; simp [h2, Ne.symm h2]
      · simp [h2, h3, Ne.symm h2, Ne.symm h3]

/-- **Lane `k` of the padded last block**: the remaining word `17 N + k` (zero past the held
bytes), `PAD_FIRST` at byte `len % 136`, `PAD_LAST` at byte `135`. -/
theorem lane_padBlock (hb : HoldsBytes ws len) {k : Nat} (hk : k < 17) :
    littleEndianLane (padBlock (((wordsBytes ws).take len).drop (136 * (len / 136)))) k =
      ws.getD (17 * (len / 136) + k) 0 ^^^
        (if k = len % 136 / 8 then 1 <<< (8 * (len % 136 % 8)).toUInt64 else 0) ^^^
        (if k = 16 then 0x8000000000000000 else 0) := by
  have hl : (((wordsBytes ws).take len).drop (136 * (len / 136))).length = len % 136 := by
    rw [List.length_drop, length_held hb]
    omega
  rw [littleEndianLane_eq]
  rw [laneOf_congr (g := fun t ↦ (wordsBytes ws).getD (8 * (17 * (len / 136) + k) + t) 0 ^^^
      (if 8 * k + t = len % 136 then 1 else 0) ^^^ (if 8 * k + t = 135 then 0x80 else 0))
    fun t ht ↦ by
      rw [getD_padBlock _ (by omega) (by omega), hl, getD_drop, getD_held hb,
        show 136 * (len / 136) + (8 * k + t) = 8 * (17 * (len / 136) + k) + t by omega]]
  rw [laneOf_xor, laneOf_xor, ← littleEndianLane_eq, littleEndianLane_wordsBytes]
  congr 2
  · by_cases h : k = len % 136 / 8
    · rw [ite_eq_left h, laneOf_congr (g := fun t ↦ if t = len % 136 % 8 then 1 else 0)
        fun t ht ↦ by
          simp only [show 8 * k + t = len % 136 ↔ t = len % 136 % 8 from
            ⟨fun _ ↦ by omega, fun _ ↦ by omega⟩],
        laneOf_single _ (by omega)]
      rfl
    · rw [ite_eq_right h, laneOf_congr (g := fun _ ↦ 0) fun t ht ↦ ite_eq_right (by omega),
        laneOf_zero]
  · by_cases h : k = 16
    · rw [ite_eq_left h, laneOf_congr (g := fun t ↦ if t = 7 then 0x80 else 0)
        fun t ht ↦ by
          simp only [show 8 * k + t = 135 ↔ t = 7 from ⟨fun _ ↦ by omega, fun _ ↦ by omega⟩],
        laneOf_single _ (by omega)]
      rfl
    · rw [ite_eq_right h, laneOf_congr (g := fun _ ↦ 0) fun t ht ↦ ite_eq_right (by omega),
        laneOf_zero]

end Held

/-! ## The sponge -/

/-- Keccak-f[1600] in `Id`, the permutation `keccak256` absorbs with. -/
abbrev perm : KeccakState → Id KeccakState := fun s ↦ pure (keccakF1600 s)

/-- XOR the lanes `f 0, …, f 16` into the rate. -/
def xorRate (A : KeccakState) (f : Nat → UInt64) : KeccakState :=
  Vector.ofFn fun i ↦ if i.val < 17 then Keccak.lane A i ^^^ f i else Keccak.lane A i

theorem lane_ofFn (f : Fin 25 → UInt64) {t : Nat} (ht : t < 25) :
    Keccak.lane (Vector.ofFn f) t = f ⟨t, ht⟩ := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?, ht]

theorem lane_xorRate (A : KeccakState) (f : Nat → UInt64) {t : Nat} (ht : t < 25) :
    Keccak.lane (xorRate A f) t =
      if t < 17 then Keccak.lane A t ^^^ f t else Keccak.lane A t := by
  rw [xorRate, lane_ofFn _ ht]

theorem xorRate_congr (A : KeccakState) {f g : Nat → UInt64} (h : ∀ i < 17, f i = g i) :
    xorRate A f = xorRate A g := by
  unfold xorRate
  congr 1
  funext i
  split
  · rw [h i.val (by omega)]
  · rfl

theorem lane_replicate {t : Nat} (ht : t < 25) : Keccak.lane (Vector.replicate 25 0) t = 0 := by
  simp [Keccak.lane, Array.getD_eq_getD_getElem?, ht]

theorem absorbWith_succ (m : Nat) (A : KeccakState) (D : List UInt8) :
    absorbWith perm (m + 1) A D =
      absorbWith perm m (keccakF1600 (xorRate A (littleEndianLane (D.take 136)))) (D.drop 136) :=
  (rfl)

theorem absorbWith_zero (A : KeccakState) (D : List UInt8) :
    absorbWith perm 0 A D = keccakF1600 (xorRate A (littleEndianLane (padBlock D))) := (rfl)

/-- `keccak256`'s lanes are the absorbed state's first four. -/
theorem keccak256_lane (data : List UInt8) {k : Nat} (hk : k < 4) :
    (keccak256 data)[k] =
      Keccak.lane (absorbWith perm (data.length / 136) (Vector.replicate 25 0) data) k := by
  rw [keccak256, LeanVM.Fast.Keccak.keccak256With_id]
  interval_cases k <;> rfl

/-- **The state before the last permutation**: lane `i` is the lane XOR the remaining word
`17 N + i` (zero past the held bytes) XOR the padding's two words. -/
theorem lane_lastBlock {ws : List UInt64} {len : Nat} (hb : HoldsBytes ws len) (A : KeccakState)
    {i : Nat} (hi : i < 25) :
    Keccak.lane (xorRate A (littleEndianLane
        (padBlock (((wordsBytes ws).take len).drop (136 * (len / 136)))))) i =
      Keccak.lane A i ^^^ ws.getD (17 * (len / 136) + i) 0 ^^^
        (if i = len % 136 / 8 then 1 <<< (8 * (len % 136 % 8)).toUInt64 else 0) ^^^
        (if i = 16 then 0x8000000000000000 else 0) := by
  rw [lane_xorRate _ _ hi]
  split
  · rw [lane_padBlock hb ‹_›]
    simp only [UInt64.xor_assoc]
  · rw [getD_words_of_le hb (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    simp

end Native.Keccak.Proof
