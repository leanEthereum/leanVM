module

public import NativeRustc.Bytes

/-!
# Digests as bytes

A statement digest (`HashSig.Digest`, 128 bits) is held by the Rust code as its 16 little-endian
bytes, `le16` (`littleEndianBytes 16` on `Digest`; `le16_inj`, `leNat_le16`); its two words
(`le16_eq_wordsBytes`, `le16_ofWords`); Keccak-256's first 16 bytes (`take16_digestBytes`); the
bytes of a little-endian number (`leNat_append`, `leNat_lt`, `leNat_div_mod`).
-/

@[expose] public section

namespace NativeRustc

open HashSig LeanVM.Protocol.KeccakHash Native Native.Keccak

/-- A digest's 16 bytes, little-endian: the `[u8; 16]` the Rust code holds it as. -/
def le16 (d : Digest) : List UInt8 := littleEndianBytes 16 d

theorem length_le16 (d : Digest) : (le16 d).length = 16 := by
  simp [le16, littleEndianBytes]

/-- The number of a digest's bytes is the digest. -/
theorem leNat_le16 (d : Digest) : leNat (le16 d) = d.toNat := leNat_littleEndianBytes 16 d

/-- `le16` is injective. -/
theorem le16_inj {d d' : Digest} : le16 d = le16 d' ↔ d = d' := littleEndianBytes_inj

/-- A digest's bytes are its words'. -/
theorem le16_eq_wordsBytes (d : Digest) : le16 d = wordsBytes [digestLo d, digestHi d] :=
  littleEndianBytes_16 d

/-- The bytes of the digest of two words are the words'. -/
theorem le16_ofWords (lo hi : UInt64) : le16 (ofWords lo hi) = wordsBytes [lo, hi] := by
  show littleEndianBytes 16 (ofWords lo hi) = _
  rw [littleEndianBytes_16, digestLo_ofWords, digestHi_ofWords]

/-- The first 16 bytes of a Keccak-256 digest are its first two words'. -/
theorem take16_digestBytes (D : LeanVM.Protocol.Digest) :
    (digestBytes D).take 16 = wordsBytes [D[0], D[1]] := by
  rw [show digestBytes D = wordsBytes D.toList from rfl, show (16 : Nat) = 8 * 2 from rfl,
    take_wordsBytes]
  congr 1
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have hk : k < 2 := by simpa using h2
  interval_cases k <;> simp

/-! ## Little-endian numbers -/

theorem leNat_cons (x : UInt8) (b : List UInt8) : leNat (x :: b) = x.toNat + 256 * leNat b := rfl

/-- The number of an append. -/
theorem leNat_append (a b : List UInt8) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x a ih =>
    rw [List.cons_append, leNat_cons, leNat_cons, ih, List.length_cons, pow_succ]
    ring

/-- A number of `n` bytes is below `256^n`. -/
theorem leNat_lt (b : List UInt8) : leNat b < 256 ^ b.length := by
  induction b with
  | nil => simp [leNat]
  | cons x b ih =>
    rw [leNat_cons, List.length_cons, pow_succ]
    have : x.toNat < 256 := x.toNat_lt
    nlinarith

/-- **Byte `k` of a little-endian number** is the `k`-th byte. -/
theorem leNat_div_mod (b : List UInt8) {k : Nat} (hk : k < b.length) :
    leNat b / 256 ^ k % 256 = b[k].toNat := by
  induction b generalizing k with
  | nil => simp at hk
  | cons x b ih =>
    have hx : x.toNat < 256 := x.toNat_lt
    cases k with
    | zero => simp [leNat_cons]
    | succ k =>
      rw [leNat_cons, pow_succ', ← Nat.div_div_eq_div_mul,
        show (x.toNat + 256 * leNat b) / 256 = leNat b by omega, List.getElem_cons_succ]
      exact ih (by simpa using hk)

/-- Digests' bytes, concatenated, are `digestsPayload`. -/
theorem flatten_ofFn {n : Nat} (f : Fin n → Digest) :
    (List.ofFn fun i ↦ le16 (f i)).flatten = digestsPayload f := by
  show _ = List.flatten (List.map le16 (List.ofFn f))
  rw [List.map_ofFn]
  rfl

end NativeRustc
