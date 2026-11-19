module

public import NativeVm.Transcript.Finish

/-!
# The seed's hash input

`fiatShamirIvWith` hashes the tag `"leanvm-v1"` then the bytecode's words, so the words after the
tag's first eight bytes sit one byte off the word boundary. `seed` builds the input in words: the
tag's first eight bytes, then each bytecode word shifted up a byte with the previous word's top
byte (first the tag's ninth) below it (`shiftWords`), then the last word's top byte.
`shiftWords_bytes`: their bytes are that byte, the words' bytes, then seven zeros.
-/

@[expose] public section

namespace NativeVm.Transcript

open Native LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

theorem u8_eq {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.toNat_inj.mp h

theorem toUInt8_toNat (y : UInt64) : y.toUInt8.toNat = y.toNat % 256 := by
  simp [UInt64.toNat_toUInt8]

theorem byte_shl_add (x p : UInt64) (hp : p.toNat < 256) (k : Nat) (hk : k < 8) :
    (((x <<< (8 : UInt64)) + p) >>> (8 * k).toUInt64).toUInt8 =
      if k = 0 then p.toUInt8 else (x >>> (8 * (k - 1)).toUInt64).toUInt8 := by
  have hx := x.toNat_lt
  have hsum : ((x <<< (8 : UInt64)) + p).toNat = x.toNat % 2 ^ 56 * 256 + p.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_shiftLeft]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq]
    omega
  split
  · subst_vars
    apply u8_eq
    rw [toUInt8_toNat, toUInt8_toNat]
    simp only [Nat.mul_zero, UInt64.toNat_shiftRight, hsum]
    simp
  · apply u8_eq
    rw [toUInt8_toNat, toUInt8_toNat, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, hsum,
      toNat_toUInt64 (by omega), toNat_toUInt64 (by omega), Nat.mod_eq_of_lt (by omega : 8 * k < 64),
      Nat.mod_eq_of_lt (by omega : 8 * (k - 1) < 64), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show 8 * (j + 1) = 8 + 8 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    rw [show (x.toNat % 2 ^ 56 * 256 + p.toNat) / 2 ^ 8 = x.toNat % 2 ^ 56 by omega]
    have hj : j < 7 := by omega
    interval_cases j <;> simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.reduceMul,
      Nat.reducePow] <;> omega

theorem wordBytes_shl_add (x p : UInt64) (hp : p.toNat < 256) :
    wordBytes ((x <<< (8 : UInt64)) + p) = p.toUInt8 :: (wordBytes x).take 7 := by
  apply List.ext_getElem (by simp [wordBytes])
  intro k h1 h2
  simp only [wordBytes, List.length_map, List.length_range] at h1
  simp only [wordBytes, List.getElem_map, List.getElem_range]
  rw [byte_shl_add x p hp k h1]
  split
  · subst_vars; rfl
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [List.getElem_cons_succ, List.getElem_take, List.getElem_map, List.getElem_range,
      Nat.add_sub_cancel]

theorem wordBytes_small (p : UInt64) (hp : p.toNat < 256) :
    wordBytes p = p.toUInt8 :: List.replicate 7 0 := by
  have := wordBytes_shl_add 0 p hp
  simp only [UInt64.zero_shiftLeft, UInt64.zero_add] at this
  rw [this]
  rfl

theorem shr56_lt (x : UInt64) : (x >>> (56 : UInt64)).toNat < 256 := by
  rw [UInt64.toNat_shiftRight]
  have := x.toNat_lt
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
  omega

theorem wordBytes_split (x : UInt64) :
    wordBytes x = (wordBytes x).take 7 ++ [(x >>> (56 : UInt64)).toUInt8] := by
  apply List.ext_getElem (by simp [wordBytes])
  intro k h1 h2
  simp only [wordBytes, List.length_map, List.length_range] at h1
  by_cases hk : k < 7
  · rw [List.getElem_append_left (by simp [wordBytes]; omega)]
    simp
  · have : k = 7 := by omega
    subst this
    rw [List.getElem_append_right (by simp [wordBytes])]
    simp [wordBytes]

/-- Words shifted up by a byte, the previous word's top byte (first `p`) below. -/
def shiftWords : UInt64 → List UInt64 → List UInt64
  | p, [] => [p]
  | p, x :: xs => ((x <<< (8 : UInt64)) + p) :: shiftWords (x >>> (56 : UInt64)) xs

theorem shiftWords_bytes (p : UInt64) (hp : p.toNat < 256) (l : List UInt64) :
    Keccak.wordsBytes (shiftWords p l) = p.toUInt8 :: Keccak.wordsBytes l ++ List.replicate 7 0 := by
  induction l generalizing p with
  | nil => simp [shiftWords, Keccak.wordsBytes, wordBytes_small p hp]
  | cons x xs ih =>
    simp only [shiftWords, Keccak.wordsBytes, List.flatMap_cons] at ih ⊢
    rw [wordBytes_shl_add x p hp, ih _ (shr56_lt x)]
    conv_rhs => rw [wordBytes_split x]
    simp

/-- The byte below word `c` of `shiftWords p l`. -/
def shiftPrev (p : UInt64) (l : List UInt64) (c : Nat) : UInt64 :=
  if c = 0 then p else l.getD (c - 1) 0 >>> (56 : UInt64)

theorem shiftWords_length (p : UInt64) (l : List UInt64) : (shiftWords p l).length = l.length + 1 := by
  induction l generalizing p with
  | nil => rfl
  | cons x xs ih => simp [shiftWords, ih]

theorem shiftWords_getD (p : UInt64) (l : List UInt64) (c : Nat) (hc : c ≤ l.length) :
    (shiftWords p l).getD c 0 =
      if c < l.length then (l.getD c 0 <<< (8 : UInt64)) + shiftPrev p l c else shiftPrev p l c := by
  induction l generalizing p c with
  | nil =>
    simp only [List.length_nil, Nat.le_zero] at hc
    subst hc
    rfl
  | cons x xs ih =>
    cases c with
    | zero => simp [shiftWords, shiftPrev]
    | succ c =>
      simp only [shiftWords, List.getD_cons_succ, List.length_cons] at hc ⊢
      rw [ih _ c (by omega)]
      simp only [shiftPrev, Nat.add_one_sub_one, Nat.add_lt_add_iff_right]
      cases c with
      | zero => simp
      | succ c => simp

theorem versionTag_chars : "leanvm-v1".toList = ['l', 'e', 'a', 'n', 'v', 'm', '-', 'v', '1'] := by simp

theorem versionTag_eq : versionTag = wordBytes tagWord.toUInt64 ++ [0x31] := by
  unfold versionTag
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, versionTag_chars]
  decide +kernel

theorem flatMap_toBytes (bc : List K) : bc.flatMap K.toBytes = Keccak.wordsBytes (bc.map K.lane) := by
  unfold Keccak.wordsBytes; rw [List.flatMap_map]; rfl

/-- The seed over Keccak-f[1600]. -/
theorem spongeSeed_eq (bc : List K) (pub : Digest) : Id.run (spongeSeedWith (m := Id) keccakF1600 bc pub) =
    keccakF1600 (seedInput (keccak256 (versionTag ++ bc.flatMap K.toBytes)) pub) := (rfl)

/-- The seed's hash input in words. -/
def seedWords (bc : List K) : List UInt64 := tagWord.toUInt64 :: shiftWords 0x31 (bc.map K.lane)

theorem seedWords_length (bc : List K) : (seedWords bc).length = bc.length + 2 := by
  simp [seedWords, shiftWords_length]

theorem seedWords_bytes (bc : List K) :
    Keccak.wordsBytes (seedWords bc) = versionTag ++ bc.flatMap K.toBytes ++ List.replicate 7 0 := by
  rw [seedWords, Keccak.wordsBytes, List.flatMap_cons, ← Keccak.wordsBytes,
    shiftWords_bytes _ (by decide), versionTag_eq, flatMap_toBytes]
  simp

theorem wordsBytes_length (ws : List UInt64) : (Keccak.wordsBytes ws).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [Keccak.wordsBytes, List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    simp [wordBytes]
    omega

theorem seedBytes_length (bc : List K) :
    (versionTag ++ bc.flatMap K.toBytes).length = 8 * bc.length + 9 := by
  rw [flatMap_toBytes, versionTag_eq, List.length_append, List.length_append, wordsBytes_length]
  simp [wordBytes]
  omega

theorem seedWords_holds (bc : List K) : Keccak.HoldsBytes (seedWords bc) (8 * bc.length + 9) := by
  refine ⟨by rw [seedWords_length]; omega, fun b hb ↦ ?_⟩
  rw [seedWords_bytes, List.drop_append_of_le_length (by rw [seedBytes_length]),
    List.drop_eq_nil_of_le (by rw [seedBytes_length]), List.nil_append] at hb
  exact List.eq_of_mem_replicate hb

theorem seedWords_take (bc : List K) :
    (Keccak.wordsBytes (seedWords bc)).take (8 * bc.length + 9) = versionTag ++ bc.flatMap K.toBytes := by
  rw [seedWords_bytes, List.take_append_of_le_length (by rw [seedBytes_length]),
    List.take_of_length_le (by rw [seedBytes_length])]

end NativeVm.Transcript
