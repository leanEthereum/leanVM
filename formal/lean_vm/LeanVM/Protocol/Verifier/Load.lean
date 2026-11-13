/-
  LeanVM.Protocol.Verifier.Load

  The serializers of the proof files' words, digests and scalars, and their round trips.
-/

module

public import LeanVM.Protocol.Verifier
import LeanVM.Protocol.Compile.Rom.Encoding

/-!
# The proof files, round trips

The serializers of scalars and the stream (`eBytes`, `encodeScalars`), and the round trips of the
decoders of `LeanVM.Protocol.Verifier`, both ways: decoding a serialized value gives it back, and a
byte string that decodes is the serialization of what it decodes to.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## The serializers -/

/-- The 16 bytes of a scalar (`E.to_bytes`): its two limbs'. -/
def eBytes (x : E) : Bytes := K.toBytes (x.limb 0) ++ K.toBytes (x.limb 1)

/-- The stream's bytes. -/
def encodeScalars (xs : List E) : Bytes := xs.flatMap eBytes

/-! ## Round trips -/

/-- A lane is read back from the head of its eight bytes (`wordBytes`). -/
theorem laneOfBytes_wordBytes_append (w : UInt64) (rest : Bytes) :
    laneOfBytes (wordBytes w ++ rest) = w := by
  apply UInt64.toNat_inj.mp
  have hw := w.toNat_lt
  simp only [laneOfBytes, wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.foldr_cons,
    List.foldr_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  norm_num
  omega

/-- The bytes of the lane read from the head of a byte string are its first eight. -/
theorem wordBytes_laneOfBytes {b : Bytes} (h : 8 ≤ b.length) :
    wordBytes (laneOfBytes b) = b.take 8 := by
  match b, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ =>
    have h0 := b0.toNat_lt
    have h1 := b1.toNat_lt
    have h2 := b2.toNat_lt
    have h3 := b3.toNat_lt
    have h4 := b4.toNat_lt
    have h5 := b5.toNat_lt
    have h6 := b6.toNat_lt
    have h7 := b7.toNat_lt
    simp only [wordBytes, laneOfBytes, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.cons_append, List.foldr_cons,
      List.foldr_nil, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, List.take_succ_cons, List.take_zero,
      List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
      simp only [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow] <;> norm_num at h0 h1 h2 h3 h4 h5 h6 h7 ⊢ <;> omega

/-- A `K` word is read back from the head of its bytes. -/
theorem kOfBytes_kBytes_append (a : K) (rest : Bytes) : kOfBytes (K.toBytes a ++ rest) = a := by
  simp only [kOfBytes, K.toBytes, laneOfBytes_wordBytes_append, K.ofLane_lane]

/-- The bytes of the word read from the head of a byte string are its first eight. -/
theorem kBytes_kOfBytes {b : Bytes} (h : 8 ≤ b.length) : K.toBytes (kOfBytes b) = b.take 8 := by
  simp only [kOfBytes, K.toBytes, K.lane_ofLane, wordBytes_laneOfBytes h]


/-! ### Lists of fixed-size values -/

section ReadMany

variable {α : Type} {size : ℕ} {decode : Bytes → α} {enc : α → Bytes}

/-- What is read is the head of the bytes: the values' bytes, then the rest. -/
theorem readMany_spec (henc : ∀ c, c.length = size → enc (decode c) = c) :
    ∀ {n : ℕ} {b rest : Bytes} {xs : List α}, readMany size decode n b = some (xs, rest) →
      xs.length = n ∧ xs.flatMap enc ++ rest = b
  | 0, b, rest, xs, h => by
    simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, b, rest, xs, h => by
    simp only [readMany] at h
    split_ifs at h with hs
    obtain ⟨⟨ys, r⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2⟩ := readMany_spec henc hr
    refine ⟨by simp [h1], ?_⟩
    rw [List.flatMap_cons, henc _ hs, List.append_assoc, h2, List.take_append_drop]

end ReadMany

/-! ### The files -/

theorem digestBytes_length' (d : Digest) : (digestBytes d).length = 32 := digestBytes_length d

end
end LeanVM.Protocol.Verifier
