module

public import Native.Keccak.Lanes
public import Native.Xmss.ModelSpec

/-!
# Byte arrays in memory

The byte-level vocabulary of the models of the rustc-compiled verifiers: a write of bytes into a
byte array (`writeAt`, what `copy_from_slice` and a store do), what `memcpy` and `memset`
(`rustc/mem.rs`) leave in their destination (`memcpyBytes`, `memsetBytes`), the little-endian
bytes of a `u32` (`u32Bytes`) and of words (`Native.Keccak.wordsBytes`), the little-endian number
of a byte string (`leNat`, `u32::from_le_bytes`, `u128::from_le_bytes`) and slices (`slice`), with
the facts the models' proofs read them by.
-/

@[expose] public section

namespace NativeRustc

open LeanVM.Protocol.KeccakHash Native.Keccak Native

/-! ## Writes -/

/-- `h` with `src` written from byte `off` on (`h[off..off + src.len()].copy_from_slice(src)`). -/
def writeAt (h : List UInt8) (off : Nat) (src : List UInt8) : List UInt8 :=
  h.take off ++ src ++ h.drop (off + src.length)

/-- `memcpy(dest, src, n)` (`rustc/mem.rs`): the `n` bytes at `dest` become `src`'s first `n`. -/
def memcpyBytes (src : List UInt8) (n : Nat) : List UInt8 := src.take n

/-- `memset(dest, c, n)` (`rustc/mem.rs`): the `n` bytes at `dest` become `c as u8`. -/
def memsetBytes (c : UInt32) (n : Nat) : List UInt8 := List.replicate n c.toUInt8

/-- Writing `src` at the end of the prefix `p`. -/
theorem writeAt_append (p q src : List UInt8) {off : Nat} (hoff : off = p.length) :
    writeAt (p ++ q) off src = p ++ (src ++ q.drop src.length) := by
  subst hoff
  rw [writeAt, List.take_left' rfl, List.drop_length_add_append, List.append_assoc]

/-- Writing `src` over the first bytes of `q`, after the prefix `p`, split at its end. -/
theorem writeAt_append_append (p src q r : List UInt8) {off : Nat} (hoff : off = p.length)
    (hq : src.length = q.length) :
    writeAt (p ++ q ++ r) off src = p ++ src ++ r := by
  rw [List.append_assoc, writeAt_append p (q ++ r) src hoff,
    List.drop_left' hq.symm, List.append_assoc]

/-! ## Words and their bytes -/

theorem length_wordBytes (w : UInt64) : (wordBytes w).length = 8 := by
  simp [wordBytes]

/-- The first `8 n` bytes of words are the first `n` words' bytes. -/
theorem take_wordsBytes : ∀ (ws : List UInt64) (n : Nat),
    (wordsBytes ws).take (8 * n) = wordsBytes (ws.take n)
  | [], _ => by simp [wordsBytes]
  | _ :: _, 0 => by simp [wordsBytes]
  | w :: ws, n + 1 => by
    rw [show 8 * (n + 1) = (wordBytes w).length + 8 * n by rw [length_wordBytes]; omega]
    simp only [wordsBytes, List.flatMap_cons, List.take_succ_cons]
    rw [List.take_length_add_append]
    exact congrArg _ (take_wordsBytes ws n)

/-- Dropping `8 n` bytes of words drops `n` words. -/
theorem drop_wordsBytes : ∀ (ws : List UInt64) (n : Nat),
    (wordsBytes ws).drop (8 * n) = wordsBytes (ws.drop n)
  | [], _ => by simp [wordsBytes]
  | _ :: _, 0 => by simp
  | w :: ws, n + 1 => by
    rw [show 8 * (n + 1) = (wordBytes w).length + 8 * n by rw [length_wordBytes]; omega]
    simp only [wordsBytes, List.flatMap_cons, List.drop_succ_cons]
    rw [List.drop_length_add_append]
    exact drop_wordsBytes ws n

/-- Bytes `8 a` to `8 (a + b)` of words are the bytes of words `a` to `a + b`. -/
theorem slice_wordsBytes (ws : List UInt64) (a b : Nat) :
    ((wordsBytes ws).drop (8 * a)).take (8 * b) = wordsBytes ((ws.drop a).take b) := by
  rw [drop_wordsBytes, take_wordsBytes]

/-- Two consecutive values of a function on `range`. -/
theorem take_two_drop_map_range (f : Nat → UInt64) {n a : Nat} (h : a + 2 ≤ n) :
    (((List.range n).map f).drop a).take 2 = [f a, f (a + 1)] := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  have : i < 2 := by simpa using h2
  interval_cases i <;> simp

/-- A word's first byte. -/
theorem wordBytes_head (w : UInt64) (rest : List UInt64) :
    (wordsBytes (w :: rest)).take 8 = wordBytes w := by
  simp [wordsBytes, List.take_left' (length_wordBytes w)]

/-- The word of a word's bytes. -/
theorem littleEndianLane_wordBytes (w : UInt64) : littleEndianLane (wordBytes w) 0 = w := by
  have h := Proof.littleEndianLane_wordsBytes [w] 0
  simpa [wordsBytes] using h

/-! ## Little-endian numbers -/

/-- The little-endian number of a byte string (`u32::from_le_bytes`, `u128::from_le_bytes`). -/
def leNat (b : List UInt8) : Nat := b.foldr (fun x acc ↦ x.toNat + 256 * acc) 0

/-- The number of the first `n` little-endian bytes of `x` is `x mod 256^n`. -/
theorem leNat_bytes (x n : Nat) : leNat (XmssVerifier.bytes x n) = x % 256 ^ n := by
  rw [leNat, XmssVerifier.bytes, Proof.foldr_bytes n x 0 _ fun k _ ↦ by rw [UInt8.toNat_ofNat']]
  simp

/-- The number of a value's `n` little-endian bytes is the value. -/
theorem leNat_littleEndianBytes (n : Nat) (v : BitVec (8 * n)) :
    leNat (HashSig.littleEndianBytes n v) = v.toNat := by
  rw [XmssVerifier.littleEndianBytes_eq_bytes, leNat_bytes, Nat.mod_eq_of_lt]
  rw [show 256 ^ n = 2 ^ (8 * n) by rw [pow_mul]; rfl]
  exact v.isLt

/-- `littleEndianBytes` is injective. -/
theorem littleEndianBytes_inj {n : Nat} {v w : BitVec (8 * n)} :
    HashSig.littleEndianBytes n v = HashSig.littleEndianBytes n w ↔ v = w := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [← leNat_littleEndianBytes, h, leNat_littleEndianBytes]
  · rintro rfl; rfl

/-! ## `u32`s -/

/-- `u32::to_le_bytes`. -/
def u32Bytes (x : UInt32) : List UInt8 := XmssVerifier.bytes x.toNat 4

/-- `u32::from_le_bytes` of the first four bytes. -/
def u32Of (b : List UInt8) : UInt32 := UInt32.ofNat (leNat (b.take 4))

theorem length_u32Bytes (x : UInt32) : (u32Bytes x).length = 4 := rfl

/-- The `u32` of its bytes. -/
theorem u32Of_u32Bytes (x : UInt32) : u32Of (u32Bytes x) = x := by
  rw [u32Of, List.take_of_length_le (by rw [length_u32Bytes]), u32Bytes, leNat_bytes,
    Nat.mod_eq_of_lt (by have := x.toNat_lt; simpa using this)]
  exact UInt32.ofNat_toNat

/-- An `or` of a small value and a multiple of `2^n` is their sum. -/
theorem lor_eq_add {a b n : Nat} (ha : a < 2 ^ n) (hb : 2 ^ n ∣ b) : a ||| b = a + b := by
  obtain ⟨q, rfl⟩ := hb
  rw [Nat.or_comm, mul_comm, ← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt ha]
  omega

/-! ## Slices -/

/-- `bytes[off..off + len]`. -/
def slice (bytes : List UInt8) (off len : Nat) : List UInt8 := (bytes.drop off).take len

end NativeRustc
