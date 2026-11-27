/-
  LeanVM.Guest.B1.Sig.Bytes

  The schemes' bit vectors as the guest's cells: a 128-bit value is the cell of its two
  64-bit halves, its bytes are the cell's bytes, a hash's truncation is its first output cell, and
  a leanXMSS address is the cell of its encoding.
-/

module

public import LeanVM.Guest.B1.Sig.InterfaceP
public import LeanVM.Guest.Value.Keccak
public import LeanVM.Guest.WithHash
public import EthLib.Cryptography.Proofs.Hash.Keccak.Lanes
public import EthLib.Cryptography.Proofs.Xmss.Address

/-!
# Cells as the schemes' values

leanSPHINCS hashes byte strings `P || A || payload` of 16-byte fields (`HashSig.littleEndianBytes`,
`Sphincs.bytesLE`), the guest hashes cells (`Value.Keccak.cellBytes`). A field `v : BitVec 128` is
the cell `cellOf128 v`, and a cell `x` reads back as `cellVal x`, whose bytes are `x`'s
(`bytesLE_cellVal`). leanXMSS's fields are EthLib's lanes: a cell `x` is the lanes `xl x`, whose
bytes are `x`'s (`bytes_xl`), and an address's cell has the bytes of its encoding
(`cellBytes_address`).

Everything goes through `leBytes n k`, the `k` low little-endian bytes of `n`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Value LeanVM.Guest.Value.Keccak

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

/-- The bytes of a bit vector, as `HashSig.littleEndianBytes` writes them. -/
theorem bytesLE_eq (k : Nat) (v : BitVec (8 * k)) : HashSig.littleEndianBytes k v = leBytes v.toNat
    k := by
  apply List.ext_getElem (by simp [HashSig.littleEndianBytes])
  intro i h1 h2
  simp only [HashSig.littleEndianBytes, List.getElem_ofFn, getElem_leBytes]
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, toNat_uint8_ofNat, Nat.shiftRight_eq_div_pow,
    pow_mul]
  norm_num

/-- A 64-bit word's bytes. -/
theorem wordBytes_eq (w : UInt64) : wordBytes w = leBytes w.toNat 8 := by
  apply List.ext_getElem (by simp [wordBytes])
  intro i h1 h2
  simp only [length_leBytes] at h2
  simp only [getElem_leBytes]
  apply UInt8.toNat_inj.mp
  have hw := w.toNat_lt
  interval_cases i <;> simp [wordBytes, Nat.shiftRight_eq_div_pow, UInt64.toNat_shiftRight]

/-- A `K` word's bytes. -/
theorem kBytes_eq (a : K) : K.toBytes a = leBytes (kToNat a) 8 := by
  rw [K.toBytes, wordBytes_eq]
  rfl

/-! ## Cells as 128-bit values -/

/-- The number a cell's two low limbs hold. -/
def cellNat (x : E) : Nat := kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)

theorem cellNat_lt (x : E) : cellNat x < 2 ^ 128 := by
  have h0 := kToNat_lt (x.limb 0)
  have h1 := kToNat_lt (x.limb 1)
  unfold cellNat; omega

/-- A cell's bytes are its number's. -/
theorem cellBytes_eq_leBytes (x : E) : cellBytes x = leBytes (cellNat x) 16 := by
  rw [cellBytes, kBytes_eq, kBytes_eq, cellNat, show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num,
    show 16 = 8 + 8 from rfl, leBytes_add_mul _ _ _ _ (by
      have := kToNat_lt (x.limb 0); norm_num; omega)]

theorem toNat_cellVal (x : E) : (cellVal x).toNat = cellNat x := by
  have h0 := kToNat_lt (x.limb 0)
  show ((x.limb 1).toBitVec ++ (x.limb 0).toBitVec).toNat = kToNat (x.limb 0) + 2 ^ 64 * kToNat (x.limb 1)
  rw [BitVec.toNat_append, Nat.shiftLeft_eq, mul_comm]
  change 2 ^ 64 * kToNat (x.limb 1) ||| kToNat (x.limb 0) = _
  rw [two_pow_mul_or h0]
  omega

/-- **A cell's bytes are its value's.** -/
theorem bytesLE_cellVal (x : E) : HashSig.littleEndianBytes 16 (cellVal x) = cellBytes x := by
  rw [bytesLE_eq, toNat_cellVal, cellBytes_eq_leBytes]

theorem cellNat_cellOf128 (v : BitVec 128) : cellNat (cellOf128 v) = v.toNat := by
  have hv := v.isLt
  simp only [cellNat, cellOf128, ofLimbs_limb0, ofLimbs_limb1]
  show (v.extractLsb' 0 64).toNat + 2 ^ 64 * (v.extractLsb' 64 64).toNat = v.toNat
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have : v.toNat / 2 ^ 64 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]
  omega

theorem cellVal_cellOf128 (v : BitVec 128) : cellVal (cellOf128 v) = v := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_cellVal, cellNat_cellOf128]

theorem limb_eq_of_kToNat {a b : K} (h : kToNat a = kToNat b) : a = b := by
  rw [← ofBits_kToNat a, ← ofBits_kToNat b, h]

theorem cellOf128_cellVal (x : E) : cellOf128 (cellVal x) = x := by
  rw [eq_ofLimbs x, cellOf128, ofLimbs_inj]
  have h0 := kToNat_lt (x.limb 0)
  have h1 := kToNat_lt (x.limb 1)
  have ht := toNat_cellVal x
  refine ⟨limb_eq_of_kToNat ?_, limb_eq_of_kToNat ?_⟩
  · show ((cellVal x).extractLsb' 0 64).toNat = _
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, ht, cellNat,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  · show ((cellVal x).extractLsb' 64 64).toNat = _
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, ht, cellNat,
      Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt h0, zero_add, Nat.mod_eq_of_lt h1]

/-- Two cells are equal when their values are. -/
theorem cellVal_inj {x y : E} (h : cellVal x = cellVal y) : x = y := by
  rw [← cellOf128_cellVal x, ← cellOf128_cellVal y, h]

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

/-- A digest's bytes are its two cells'. -/
theorem digestBytes_eq (d : Digest) :
    digestBytes d = cellBytes (digestHalves d).1 ++ cellBytes (digestHalves d).2 := by
  rw [digestBytes, digestHalves]
  simp only [cellBytes, K.toBytes, ofLimbs_limb0, ofLimbs_limb1, lane_ofLane]
  rcases d with ⟨⟨l⟩, hl⟩
  simp only [List.size_toArray] at hl
  match l, hl with
  | [a, b, c, e], _ => rfl

/-- The number of a digest's 32 bytes: its two cells'. -/
theorem leNat_digestBytes (d : Digest) :
    leNat (digestBytes d) = cellNat (digestHalves d).1 + 2 ^ 128 * cellNat (digestHalves d).2 := by
  rw [digestBytes_eq, leNat_append, cellBytes_eq_leBytes, cellBytes_eq_leBytes, leNat_leBytes,
    leNat_leBytes, length_leBytes,
    Nat.mod_eq_of_lt (by have := cellNat_lt (digestHalves d).1; norm_num; omega),
    Nat.mod_eq_of_lt (by have := cellNat_lt (digestHalves d).2; norm_num; omega)]
  norm_num

theorem keccakBits_toNat (I : List UInt8) :
    (Node.keccakBits I).toNat = cellNat (digestHalves (keccak256 I)).1 +
      2 ^ 128 * cellNat (digestHalves (keccak256 I)).2 := by
  have h0 := cellNat_lt (digestHalves (keccak256 I)).1
  have h1 := cellNat_lt (digestHalves (keccak256 I)).2
  have e : (digestBytes (keccak256 I)).foldr (fun b acc ↦ b.toNat + 256 * acc) 0 =
      leNat (digestBytes (keccak256 I)) := rfl
  rw [Node.keccakBits, Node.digestBits, BitVec.toNat_ofNat, e, leNat_digestBytes,
    Nat.mod_eq_of_lt (by omega)]

/-- **A hash's truncation is its first output cell.** -/
theorem truncateHash_keccakBits (I : List UInt8) :
    HashSig.truncateHash (Node.keccakBits I) = cellVal (digestHalves (keccak256 I)).1 := by
  apply BitVec.eq_of_toNat_eq
  have h : (HashSig.truncateHash (Node.keccakBits I)).toNat = (Node.keccakBits I).toNat % 2 ^ 128 := by
    show ((Node.keccakBits I).toNat >>> 0) % 2 ^ 128 = _
    rw [Nat.shiftRight_zero]
  have h0 := cellNat_lt (digestHalves (keccak256 I)).1
  rw [h, keccakBits_toNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  exact (toNat_cellVal _).symm

/-! ## Addresses -/

/-- A cell's bytes from its 128-bit number. -/
theorem cellNat_eOfNat128 {n : Nat} (h : n < 2 ^ 128) : cellNat (eOfNat128 n) = n := by
  simp only [cellNat, eOfNat128, ofLimbs_limb0, ofLimbs_limb1, kToNat_ofBits]
  have h2 : n / 2 ^ 64 < 2 ^ 64 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc n < 2 ^ 128 := h
      _ = 2 ^ 64 * 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt h2]
  have := Nat.mod_add_div n (2 ^ 64)
  omega

/-- The bytes of `toLE` are the number's little-endian bytes. -/
theorem toList_toLE (k n : Nat) : (EthLib.Base.ByteOrder.toLE k n).toList = leBytes n k := by
  simp only [EthLib.Base.ByteOrder.toLE, Vector.toList_ofFn, leBytes, Nat.shiftRight_eq_div_pow,
    pow_mul]
  norm_num

/-- **A cell holding an address's number has the address's bytes**, for a number below `2^64`
(`Address.encode`'s second lane is zero). -/
theorem cellBytes_address {a : EthLib.Cryptography.Xmss.Address} {N : Nat}
    (h : a.encode.toNat = N) (hN : N < 2 ^ 64) :
    cellBytes (eOfNat N) = a.encode.bytes.toList := by
  rw [EthLib.Cryptography.Hash.Keccak.Lanes2.bytes_eq_toLE, toList_toLE, h, cellBytes_eOfNat hN]

/-! ## Cells as EthLib's lanes -/

open EthLib.Cryptography.Hash.Keccak (Lanes2 Lanes4)

/-- A cell's bytes are its two lanes'. -/
theorem bytes_xl (x : E) : (xl x).bytes.toList = cellBytes x := by
  simp [xl, Lanes2.bytes, cellBytes, K.toBytes, wordBytes, List.range_succ]

theorem toNat_xl (x : E) : (xl x).toNat = cellNat x := rfl

theorem xl_xc (w : Lanes2) : xl (xc w) = w := by
  simp [xl, xc]

theorem xc_xl (x : E) : xc (xl x) = x := by
  rw [xc, eq_ofLimbs x]
  rfl

theorem xl_inj {x y : E} (h : xl x = xl y) : x = y := by
  rw [← xc_xl x, ← xc_xl y, h]

/-- A cell as a 128-bit value is its two lanes' number. -/
theorem ofNat_toNat_xl (x : E) : BitVec.ofNat 128 (xl x).toNat = cellVal x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, toNat_xl, toNat_cellVal, Nat.mod_eq_of_lt (cellNat_lt x)]

/-- A cell of a key half's number is the half's cell. -/
theorem cellOf128_toNat (w : Lanes2) : cellOf128 (BitVec.ofNat 128 w.toNat) = xc w := by
  have h := ofNat_toNat_xl (xc w)
  rw [xl_xc] at h
  rw [h, cellOf128_cellVal]

theorem lane_byte (v : BitVec 256) (k q : Nat) (hq : q < 8) :
    ((UInt64.ofBitVec (v.extractLsb' (64 * k) 64)) >>> (8 * q).toUInt64).toUInt8 =
      UInt8.ofBitVec (v.extractLsb' (8 * (8 * k + q)) 8) := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat,
    UInt64.toNat_shiftRight, UInt64.toNat_ofBitVec, Nat.shiftRight_eq_div_pow]
  have h8 : (8 * q).toUInt64.toNat % 64 = 8 * q := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  rw [h8]
  have e : 2 ^ 64 = 2 ^ (8 * q) * 2 ^ (64 - 8 * q) := by rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

/-- **A message as four lanes has the message's bytes.** -/
theorem lanesOfBits_bytes (v : BitVec 256) :
    (LeanXmss.lanesOfBits v).bytes.toList = HashSig.littleEndianBytes 32 v := by
  apply List.ext_getElem (by simp [HashSig.littleEndianBytes])
  intro j h1 h2
  have hj : j < 32 := by simpa [HashSig.littleEndianBytes] using h2
  simp only [HashSig.littleEndianBytes, List.getElem_ofFn, Vector.getElem_toList]
  rw [EthLib.Cryptography.Hash.Keccak.getElem_lanes4_bytes _ j hj,
    EthLib.Cryptography.Hash.Keccak.getD_bytesOfLane _ _ (by omega)]
  have key := lane_byte v (j / 8) (j % 8) (by omega)
  rw [show 8 * (8 * (j / 8) + j % 8) = 8 * j by omega] at key
  rw [← key]
  rcases (by omega : j / 8 = 0 ∨ j / 8 = 1 ∨ j / 8 = 2 ∨ j / 8 = 3) with h | h | h | h <;>
    simp only [h, LeanXmss.lanesOfBits]
  · simp [show j < 8 by omega]
  · simp [show ¬ j < 8 by omega, show j < 16 by omega]
  · simp [show ¬ j < 8 by omega, show ¬ j < 16 by omega, show j < 24 by omega]
  · simp [show ¬ j < 8 by omega, show ¬ j < 16 by omega, show ¬ j < 24 by omega]

end
end LeanVM.Guest.B1.Sig
