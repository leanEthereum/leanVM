/-
  LeanVM.Guest.B1.Sig.Bytes

  The schemes' bit vectors as the guest's cells: a 128-bit value is the canonical cell of its
  two 64-bit halves, its bytes are the cell's bytes, a hash's truncation is its first output
  cell, and an address is the cell of its packed fields.
-/

module

public import LeanVM.Guest.Value.Hash
public import LeanVM.Spec.Node

/-!
# Cells as the schemes' values

The schemes hash byte strings `P || A || payload` of 16-byte fields (`LeanXmss.bytesLE`,
`Sphincs.bytesLE`), the guest hashes cells (`Value.cellBytes`). A field `v : BitVec 128` is the
cell `cellOf v`, and a cell `x` reads back as `cellVal x`, whose bytes are `x`'s for any `x`
(`bytesLE_cellVal`): the bytes ignore the top limb, which the compressions pin to zero.

Everything goes through `leBytes n k`, the `k` low little-endian bytes of `n`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-! ## Little-endian bytes of numbers -/

/-- The `k` low little-endian bytes of `n`. -/
def leBytes (n k : Nat) : List UInt8 := List.ofFn fun i : Fin k => UInt8.ofNat (n / 256 ^ i.val)

@[simp] theorem length_leBytes (n k : Nat) : (leBytes n k).length = k := by simp [leBytes]

theorem getElem_leBytes (n k i : Nat) (hi : i < (leBytes n k).length) :
    (leBytes n k)[i] = UInt8.ofNat (n / 256 ^ i) := by simp [leBytes]

theorem toNat_uint8_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.ofNat, UInt8.toNat, BitVec.toNat_ofNat]

theorem uint8_ofNat_eq_iff {a b : Nat} : UInt8.ofNat a = UInt8.ofNat b ↔ a % 256 = b % 256 := by
  constructor
  · intro h
    have := congrArg UInt8.toNat h
    simpa [toNat_uint8_ofNat] using this
  · intro h
    apply UInt8.toNat_inj.mp
    simpa [toNat_uint8_ofNat] using h

/-- Bytes depend only on the number modulo `256^k`. -/
theorem leBytes_mod (n k : Nat) : leBytes (n % 256 ^ k) k = leBytes n k := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [getElem_leBytes, uint8_ofNat_eq_iff]
  simp only [length_leBytes] at h1
  rw [show 256 ^ k = 256 ^ i * (256 * 256 ^ (k - i - 1)) by
      rw [← pow_succ', ← pow_add, show i + (k - i - 1 + 1) = k by omega],
    Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

theorem leBytes_append (n a b : Nat) : leBytes n a ++ leBytes (n / 256 ^ a) b = leBytes n (a + b) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [length_leBytes] at h2
  by_cases hi : i < a
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [getElem_leBytes]
  · rw [List.getElem_append_right (by simpa using hi)]
    simp only [getElem_leBytes, length_leBytes, Nat.div_div_eq_div_mul, ← pow_add]
    congr 3
    omega

theorem leBytes_add_mul (lo hi a b : Nat) (hlo : lo < 256 ^ a) :
    leBytes (lo + 256 ^ a * hi) (a + b) = leBytes lo a ++ leBytes hi b := by
  rw [← leBytes_append, ← leBytes_mod (lo + 256 ^ a * hi) a, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hlo, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlo, zero_add]

/-- The bytes of a bit vector, as `LeanXmss.bytesLE` writes them. -/
theorem bytesLE_eq (k : Nat) (v : BitVec (8 * k)) : LeanXmss.bytesLE k v = leBytes v.toNat k := by
  apply List.ext_getElem (by simp [LeanXmss.bytesLE])
  intro i h1 h2
  simp only [LeanXmss.bytesLE, List.getElem_ofFn, getElem_leBytes]
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, toNat_uint8_ofNat, Nat.shiftRight_eq_div_pow,
    pow_mul]
  norm_num

theorem sphincs_bytesLE_eq (k : Nat) (v : BitVec (8 * k)) : Sphincs.bytesLE k v = leBytes v.toNat k :=
  bytesLE_eq k v

/-- A word's bytes. -/
theorem wordBytes_eq (w : UInt32) : wordBytes w = leBytes w.toNat 4 := by
  apply List.ext_getElem (by simp [wordBytes])
  intro i h1 h2
  simp only [length_leBytes] at h2
  simp only [getElem_leBytes]
  apply UInt8.toNat_inj.mp
  interval_cases i <;> simp [wordBytes, Nat.shiftRight_eq_div_pow]

/-- A `K` word's bytes. -/
theorem kBytes_eq (a : K) : kBytes a = leBytes (kToNat a) 8 := by
  have hlt : kToNat a < 2 ^ 64 := (a.toBitVec).isLt
  rw [kBytes, wordBytes_eq, wordBytes_eq]
  have hl : (lowWord a).toNat = kToNat a % 2 ^ 32 := by
    simp [lowWord, kToNat, UInt32.toNat, BitVec.extractLsb'_toNat]
  have hh : (highWord a).toNat = kToNat a / 2 ^ 32 := by
    simp only [highWord, kToNat, UInt32.toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt (by have := (a.toBitVec).isLt; omega)
  rw [hl, hh, show (2 : Nat) ^ 32 = 256 ^ 4 by norm_num, leBytes_mod, leBytes_append]

/-! ## Cells as 128-bit values -/

/-- The number a cell's two low limbs hold. -/
def cellNat (x : E) : Nat := kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)

theorem cellNat_lt (x : E) : cellNat x < 2 ^ 128 := by
  have h0 : kToNat (x.limb 0) < 2 ^ 64 := ((x.limb 0).toBitVec).isLt
  have h1 : kToNat (x.limb 1) < 2 ^ 64 := ((x.limb 1).toBitVec).isLt
  unfold cellNat; omega

/-- A cell's bytes are its number's. -/
theorem cellBytes_eq_leBytes (x : E) : cellBytes x = leBytes (cellNat x) 16 := by
  rw [cellBytes, kBytes_eq, kBytes_eq, cellNat, show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num,
    show 16 = 8 + 8 from rfl, leBytes_add_mul _ _ _ _ (by
      have := ((x.limb 0).toBitVec).isLt; simpa [kToNat] using this)]

/-- The 128-bit value of a cell. -/
def cellVal (x : E) : BitVec 128 := BitVec.ofNat 128 (cellNat x)

/-- The cell of a 128-bit value. -/
def cellOf (v : BitVec 128) : E := E.ofLimbs (K.ofBits v.toNat) (K.ofBits (v.toNat / 2 ^ 64)) 0

theorem toNat_cellVal (x : E) : (cellVal x).toNat = cellNat x := by
  rw [cellVal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (cellNat_lt x)]

/-- **A cell's bytes are its value's**, whatever its top limb. -/
theorem bytesLE_cellVal (x : E) : LeanXmss.bytesLE 16 (cellVal x) = cellBytes x := by
  rw [bytesLE_eq, toNat_cellVal, cellBytes_eq_leBytes]

theorem sphincs_bytesLE_cellVal (x : E) : Sphincs.bytesLE 16 (cellVal x) = cellBytes x :=
  bytesLE_cellVal x

theorem cellNat_cellOf (v : BitVec 128) : cellNat (cellOf v) = v.toNat := by
  have hv := v.isLt
  simp only [cellNat, cellOf, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits]
  omega

theorem cellVal_cellOf (v : BitVec 128) : cellVal (cellOf v) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cellVal, cellNat_cellOf]

theorem isCanonical128_cellOf (v : BitVec 128) : IsCanonical128 (cellOf v) := rfl

theorem cellOf_cellVal {x : E} (h : IsCanonical128 x) : cellOf (cellVal x) = x := by
  have h0 : kToNat (x.limb 0) < 2 ^ 64 := ((x.limb 0).toBitVec).isLt
  rw [eq_ofLimbs_of_canonical h]
  simp only [cellOf, toNat_cellVal, cellNat, ofLimbs_limb0, ofLimbs_limb1]
  rw [ofLimbs_inj]
  refine ⟨?_, ?_, rfl⟩
  · rw [← ofBits_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0, ofBits_kToNat]
  · rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h0, zero_add, ofBits_kToNat]

theorem cellBytes_cellOf (v : BitVec 128) : cellBytes (cellOf v) = LeanXmss.bytesLE 16 v := by
  rw [← bytesLE_cellVal, cellVal_cellOf]

/-- Two canonical cells are equal when their values are. -/
theorem cellVal_inj {x y : E} (hx : IsCanonical128 x) (hy : IsCanonical128 y)
    (h : cellVal x = cellVal y) : x = y := by
  rw [← cellOf_cellVal hx, ← cellOf_cellVal hy, h]

/-- The cell of a small number. -/
theorem kToNat_zero : kToNat (0 : K) = 0 := rfl

theorem cellNat_eOfNat {n : Nat} (h : n < 2 ^ 64) : cellNat (eOfNat n) = n := by
  rw [cellNat, eOfNat_eq_ofLimbs, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits, Nat.mod_eq_of_lt h,
    kToNat_zero, mul_zero, add_zero]

theorem cellBytes_eOfNat {n : Nat} (h : n < 2 ^ 64) : cellBytes (eOfNat n) = leBytes n 16 := by
  rw [cellBytes_eq_leBytes, cellNat_eOfNat h]

/-! ## Hash outputs -/

/-- The little-endian number of bytes. -/
def leNat (bs : List UInt8) : Nat := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

theorem leNat_append (xs ys : List UInt8) : leNat (xs ++ ys) = leNat xs + 256 ^ xs.length * leNat ys := by
  induction xs with
  | nil => simp [leNat]
  | cons x xs ih =>
      simp only [leNat, List.cons_append, List.foldr_cons, List.length_cons] at ih ⊢
      rw [ih, pow_succ]
      ring

theorem leNat_leBytes (n k : Nat) : leNat (leBytes n k) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [leNat, leBytes, Nat.mod_one]
  | succ k ih =>
      have e : leBytes n (k + 1) = UInt8.ofNat n :: leBytes (n / 256) k := by
        apply List.ext_getElem (by simp)
        intro i h1 h2
        cases i with
        | zero => simp [getElem_leBytes]
        | succ i => simp [getElem_leBytes, Nat.div_div_eq_div_mul, pow_succ']
      rw [e]
      simp only [leNat, List.foldr_cons] at ih ⊢
      rw [ih, toNat_uint8_ofNat, pow_succ', Nat.mod_mul]

/-- The number of a digest's 32 bytes: its two cells'. -/
theorem leNat_digestBytes (d : Digest) :
    leNat (digestBytes d) = cellNat (digestScalars d).1 + 2 ^ 128 * cellNat (digestScalars d).2 := by
  rw [digestBytes_eq, leNat_append, cellBytes_eq_leBytes, cellBytes_eq_leBytes, leNat_leBytes,
    leNat_leBytes, length_leBytes, Nat.mod_eq_of_lt (by have := cellNat_lt (digestScalars d).1; norm_num; omega),
    Nat.mod_eq_of_lt (by have := cellNat_lt (digestScalars d).2; norm_num; omega)]
  norm_num

theorem blake2sBits_toNat (I : List UInt8) :
    (Node.blake2sBits I).toNat = cellNat (digestScalars (blake2sBytes I)).1 +
      2 ^ 128 * cellNat (digestScalars (blake2sBytes I)).2 := by
  have h0 := cellNat_lt (digestScalars (blake2sBytes I)).1
  have h1 := cellNat_lt (digestScalars (blake2sBytes I)).2
  have e : (digestBytes (blake2sBytes I)).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      leNat (digestBytes (blake2sBytes I)) := rfl
  rw [Node.blake2sBits, BitVec.toNat_ofNat, e, leNat_digestBytes, Nat.mod_eq_of_lt (by omega)]

/-- **A hash's truncation is its first output cell.** -/
theorem truncateHash_blake2sBits (I : List UInt8) :
    LeanXmss.truncateHash (Node.blake2sBits I) = cellVal (digestScalars (blake2sBytes I)).1 := by
  apply BitVec.eq_of_toNat_eq
  have h : (LeanXmss.truncateHash (Node.blake2sBits I)).toNat = (Node.blake2sBits I).toNat % 2 ^ 128 := by
    show ((Node.blake2sBits I).toNat >>> 0) % 2 ^ 128 = _
    rw [Nat.shiftRight_zero]
  have h0 := cellNat_lt (digestScalars (blake2sBytes I)).1
  rw [h, blake2sBits_toNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  exact (toNat_cellVal _).symm

theorem sphincs_truncateHash_blake2sBits (I : List UInt8) :
    Sphincs.truncateHash (Node.blake2sBits I) = cellVal (digestScalars (blake2sBytes I)).1 :=
  truncateHash_blake2sBits I

/-! ## Addresses -/

/-- The number an address's four fields pack into: `lo`, `hi` from bit 32, the type and step
byte from bit 56. -/
def addrNat (tag step hi lo : Nat) : Nat :=
  lo % 2 ^ 32 + 2 ^ 32 * (hi % 2 ^ 24) + 2 ^ 56 * (tag % 32 + 32 * (step % 8))

theorem addrNat_lt (tag step hi lo : Nat) : addrNat tag step hi lo < 2 ^ 64 := by
  have := Nat.mod_lt lo (show 2 ^ 32 > 0 by norm_num)
  have := Nat.mod_lt hi (show 2 ^ 24 > 0 by norm_num)
  have := Nat.mod_lt tag (show 32 > 0 by norm_num)
  have := Nat.mod_lt step (show 8 > 0 by norm_num)
  unfold addrNat; omega

/-- **An address is the cell of its packed fields.** -/
theorem fieldBytes_tweakFields (tag step hi lo : Nat) :
    LeanXmss.fieldBytes (LeanXmss.tweakFields tag step hi lo) = cellBytes (eOfNat (addrNat tag step hi lo)) := by
  have hS : (BitVec.ofNat 3 step ++ BitVec.ofNat 5 tag).toNat = tag % 32 + 32 * (step % 8) := by
    rw [BitVec.toNat_append, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, mul_comm,
      two_pow_mul_or (Nat.mod_lt _ (by norm_num))]
    norm_num
    ring
  have hlo := Nat.mod_lt lo (show 2 ^ 32 > 0 by norm_num)
  have hhi := Nat.mod_lt hi (show 2 ^ 24 > 0 by norm_num)
  have htag := Nat.mod_lt tag (show 32 > 0 by norm_num)
  have hst := Nat.mod_lt step (show 8 > 0 by norm_num)
  rw [cellBytes_eOfNat (addrNat_lt _ _ _ _), LeanXmss.fieldBytes, LeanXmss.tweakFields,
    bytesLE_eq, bytesLE_eq, bytesLE_eq, bytesLE_eq, hS]
  simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, Nat.zero_mod]
  rw [show addrNat tag step hi lo = lo % 2 ^ 32 + 256 ^ 4 * (hi % 2 ^ 24 + 256 ^ 3 *
      ((tag % 32 + 32 * (step % 8)) + 256 ^ 1 * 0)) by unfold addrNat; ring,
    show (16 : Nat) = 4 + (3 + (1 + 8)) from rfl, leBytes_add_mul _ _ _ _ (by norm_num; omega),
    leBytes_add_mul _ _ _ _ (by norm_num; omega), leBytes_add_mul _ _ _ _ (by norm_num; omega)]
  simp only [List.append_assoc]

theorem sphincs_fieldBytes_tweakFields (tag step hi lo : Nat) :
    Sphincs.fieldBytes (Sphincs.tweakFields tag step hi lo) = cellBytes (eOfNat (addrNat tag step hi lo)) :=
  fieldBytes_tweakFields tag step hi lo

end
end LeanVM.Guest.B1.Sig
