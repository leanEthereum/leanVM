/-
  LeanVM.Protocol.Verifier.Load

  The serializers of the four proof files, and the round trips: each decoder of
  `LeanVM.Protocol.Verifier` (section "Loading a proof from its four files") inverts one.
-/

module

public import LeanVM.Protocol.Verifier
import LeanVM.Protocol.Compile.Rom.Encoding

/-!
# The proof files, round trips

The serializers of the four files the verifier reads (`eBytes`, `encodeScalars`,
`openingBytes`, `encodeOpenings`), and the round trips: every decoder of
`LeanVM.Protocol.Verifier` inverts a serializer, both ways: decoding a serialized value gives
it back, and a byte string that decodes is the serialization of what it decodes to. The openings
file's cut is complete by `splitOpenings_encodeOpenings` and its bytes are the Python's reads in
order by `encodeOpenings_splitOpenings`.
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile
open LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## The serializers -/

/-- The 24 bytes of a scalar (`E.to_bytes`). -/
def eBytes (x : E) : Bytes := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-- The stream's bytes. -/
def encodeScalars (xs : List E) : Bytes := xs.flatMap eBytes

/-- An opening's bytes: its leaf's words, then its siblings from the leaf up
(`Transcript.merkle`). -/
def openingBytes (o : Opening) : Bytes := o.leaf.flatMap kBytes ++ o.path.flatMap digestBytes

/-- The openings file's bytes. -/
def encodeOpenings (os : List Opening) : Bytes := os.flatMap openingBytes

/-! ## Round trips -/

/-- A word is read back from its four bytes (`wordBytes`). -/
theorem wordOfBytes_wordBytes (w : UInt32) :
    wordOfBytes w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8 = w := by
  apply UInt32.toNat_inj.mp
  simp only [wordOfBytes, UInt32.toNat_ofNat, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  norm_num at this ⊢
  omega

theorem wordBytes_wordOfBytes (b0 b1 b2 b3 : UInt8) :
    wordBytes (wordOfBytes b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  simp only [wordBytes, wordOfBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] <;> norm_num at h0 h1 h2 h3 ⊢ <;> omega

/-- A `K` word is read back from the head of its bytes. -/
theorem kOfBytes_kBytes_append (a : K) (rest : Bytes) : kOfBytes (kBytes a ++ rest) = a := by
  have hl := wordOfBytes_wordBytes (lowWord a)
  have hh := wordOfBytes_wordBytes (highWord a)
  simpa [kOfBytes, kBytes, wordBytes, hl, hh] using ofWords_lowWord_highWord a

theorem kOfBytes_kBytes (a : K) : kOfBytes (kBytes a) = a := by
  simpa using kOfBytes_kBytes_append a []

/-- The bytes of the word read from the head of a byte string are its first eight. -/
theorem kBytes_kOfBytes {b : Bytes} (h : 8 ≤ b.length) : kBytes (kOfBytes b) = b.take 8 := by
  match b, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ =>
    simp [kOfBytes, kBytes, lowWord_ofWords, highWord_ofWords, wordBytes_wordOfBytes]

theorem digestOfBytes_digestBytes (d : Digest) : digestOfBytes (digestBytes d) = d := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    have := wordOfBytes_wordBytes
    ext j hj
    interval_cases j <;> simp [digestOfBytes, digestBytes, wordBytes, this]

theorem digestBytes_digestOfBytes {b : Bytes} (h : b.length = 32) :
    digestBytes (digestOfBytes b) = b := by
  match b, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
      b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ =>
    simp [digestOfBytes, digestBytes, wordBytes_wordOfBytes, Vector.toList_ofFn, List.ofFn_succ]

theorem eBytes_length (x : E) : (eBytes x).length = 24 := rfl

theorem eOfBytes_eBytes (x : E) : eOfBytes (eBytes x) = x := by
  simp only [eOfBytes, eBytes, List.append_assoc, kOfBytes_kBytes_append]
  rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, List.drop_left' (kBytes_length _),
    List.drop_left' (kBytes_length _), kOfBytes_kBytes_append, kOfBytes_kBytes]
  exact ofLimbs_limb x

theorem eBytes_eOfBytes {b : Bytes} (h : b.length = 24) : eBytes (eOfBytes b) = b := by
  simp only [eBytes, eOfBytes, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [kBytes_kOfBytes (by omega), kBytes_kOfBytes (by simp; omega),
    kBytes_kOfBytes (by simp; omega), List.take_of_length_le (l := b.drop 16) (by simp; omega),
    show 16 = 8 + 8 from rfl, ← List.drop_drop, List.append_assoc, List.take_append_drop,
    List.take_append_drop]


/-! ### Lists of fixed-size values -/

section ReadMany

variable {α : Type} {size : ℕ} {decode : Bytes → α} {enc : α → Bytes}

theorem length_flatMap_of_length (hlen : ∀ x, (enc x).length = size) (xs : List α) :
    (xs.flatMap enc).length = xs.length * size := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, hlen, ih, Nat.succ_mul, Nat.add_comm]

/-- Reading values back from their bytes gives them, and the bytes after them. -/
theorem readMany_flatMap (hlen : ∀ x, (enc x).length = size) (hdec : ∀ x, decode (enc x) = x)
    (xs : List α) (rest : Bytes) :
    readMany size decode xs.length (xs.flatMap enc ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany,
      List.take_left' (hlen x), hlen x, ↓reduceIte, List.drop_left' (hlen x), ih, hdec,
      Option.map_some]

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

theorem decodeAll_flatMap (hpos : 0 < size) (hlen : ∀ x, (enc x).length = size)
    (hdec : ∀ x, decode (enc x) = x) (xs : List α) :
    decodeAll size decode (xs.flatMap enc) = some xs := by
  have h := readMany_flatMap hlen hdec xs []
  rw [List.append_nil] at h
  simp only [decodeAll, length_flatMap_of_length hlen, Nat.mul_div_cancel _ hpos, h]

theorem decodeAll_spec (henc : ∀ c, c.length = size → enc (decode c) = c) {b : Bytes}
    {xs : List α} (h : decodeAll size decode b = some xs) : xs.flatMap enc = b := by
  unfold decodeAll at h
  split at h
  · rename_i hr
    cases h
    simpa using (readMany_spec henc hr).2
  · cases h

end ReadMany

/-! ### The files -/

theorem kBytes_kOfBytes_of_length {c : Bytes} (h : c.length = 8) : kBytes (kOfBytes c) = c := by
  rw [kBytes_kOfBytes (by omega), List.take_of_length_le (by omega)]

theorem digestBytes_length' (d : Digest) : (digestBytes d).length = 32 := digestBytes_length d

/-- **The bytecode file round-trips**: a word list is read back from its bytes. -/
theorem decodeWords_flatMap (ws : List K) : decodeWords (ws.flatMap kBytes) = some ws :=
  decodeAll_flatMap (by decide) kBytes_length kOfBytes_kBytes ws

/-- A bytecode file that decodes is the bytes of its words. -/
theorem flatMap_of_decodeWords {b : Bytes} {ws : List K} (h : decodeWords b = some ws) :
    ws.flatMap kBytes = b :=
  decodeAll_spec (fun _ ↦ kBytes_kOfBytes_of_length) h

/-- **The stream file round-trips**: a stream is read back from its bytes. -/
theorem decodeScalars_encodeScalars (xs : List E) : decodeScalars (encodeScalars xs) = some xs :=
  decodeAll_flatMap (by decide) eBytes_length eOfBytes_eBytes xs

/-- A stream file that decodes is the bytes of its scalars. -/
theorem encodeScalars_of_decodeScalars {b : Bytes} {xs : List E} (h : decodeScalars b = some xs) :
    encodeScalars xs = b :=
  decodeAll_spec (fun _ ↦ eBytes_eOfBytes) h

/-- **The public input file round-trips.** -/
theorem decodeDigest_digestBytes (d : Digest) : decodeDigest (digestBytes d) = some d := by
  simp [decodeDigest, digestBytes_length, digestOfBytes_digestBytes]

/-- A public input file that decodes is the bytes of its digest. -/
theorem digestBytes_of_decodeDigest {b : Bytes} {d : Digest} (h : decodeDigest b = some d) :
    digestBytes d = b := by
  unfold decodeDigest at h
  split_ifs at h with hl
  cases h
  exact digestBytes_digestOfBytes hl

/-! ### The openings -/

/-- An opening's shape: its height (siblings) and width (leaf words). -/
def openingShape (o : Opening) : ℕ × ℕ := (o.path.length, o.leaf.length)

theorem readOpening_bytes (o : Opening) (rest : Bytes) :
    readOpening o.path.length o.leaf.length (openingBytes o ++ rest) = some (o, rest) := by
  simp [readOpening, openingBytes, readMany_flatMap kBytes_length kOfBytes_kBytes,
    readMany_flatMap digestBytes_length digestOfBytes_digestBytes]

theorem readOpening_spec {height width : ℕ} {b rest : Bytes} {o : Opening}
    (h : readOpening height width b = some (o, rest)) :
    openingShape o = (height, width) ∧ openingBytes o ++ rest = b := by
  simp only [readOpening, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨leaf, b1⟩, h1, ⟨path, b2⟩, h2, he⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hl1, hb1⟩ := readMany_spec (fun _ ↦ kBytes_kOfBytes_of_length) h1
  obtain ⟨hl2, hb2⟩ := readMany_spec (fun _ ↦ digestBytes_digestOfBytes) h2
  refine ⟨by simp [openingShape, hl1, hl2], ?_⟩
  simp only [openingBytes, List.append_assoc, hb2, hb1]

theorem readOpenings_encodeOpenings (os : List Opening) (rest : Bytes) :
    readOpenings (os.map openingShape) (encodeOpenings os ++ rest) = some (os, rest) := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, openingShape, encodeOpenings, List.flatMap_cons,
      List.append_assoc, readOpenings, readOpening_bytes]
    simp only [encodeOpenings] at ih
    simp [ih]

theorem readOpenings_spec :
    ∀ {shapes : List (ℕ × ℕ)} {b rest : Bytes} {os : List Opening},
      readOpenings shapes b = some (os, rest) →
        os.map openingShape = shapes ∧ encodeOpenings os ++ rest = b
  | [], b, rest, os, h => by
    simp only [readOpenings, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encodeOpenings]
  | (height, width) :: shapes, b, rest, os, h => by
    simp only [readOpenings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨o, b1⟩, h1, ⟨os', b2⟩, h2, he⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hs1, hb1⟩ := readOpening_spec h1
    obtain ⟨hs2, hb2⟩ := readOpenings_spec h2
    refine ⟨by simp [hs1, hs2], ?_⟩
    simp only [encodeOpenings, List.flatMap_cons, List.append_assoc] at hb2 ⊢
    rw [hb2, hb1]

/-- **The openings file round-trips**: openings are cut back out of their bytes at their own
shapes. -/
theorem splitOpenings_encodeOpenings (os : List Opening) :
    splitOpenings (os.map openingShape) (encodeOpenings os) = some os := by
  have h := readOpenings_encodeOpenings os []
  rw [List.append_nil] at h
  simp only [splitOpenings, h]

/-- An openings file that is cut is the bytes of its openings, in the shapes asked for. -/
theorem encodeOpenings_splitOpenings {shapes : List (ℕ × ℕ)} {b : Bytes} {os : List Opening}
    (h : splitOpenings shapes b = some os) :
    os.map openingShape = shapes ∧ encodeOpenings os = b := by
  unfold splitOpenings at h
  split at h
  · rename_i hr
    cases h
    simpa using readOpenings_spec hr
  · cases h

end
end LeanVM.Protocol.Verifier
