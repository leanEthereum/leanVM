module

public import LeanXmss.Scheme

@[expose] public section

/-!
# Byte encodings and domain separation

An input determines its parameter, its address and its payload, and an address determines the call:
two hash calls of different kinds, or of the same kind at different places, never share an input.
-/

namespace LeanXmss

open HashSig

theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : littleEndianBytes n x =
    littleEndianBytes n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (littleEndianBytes n x).length = n := by
  simp [littleEndianBytes]

@[simp] theorem bytesLE_length_publicParameter (x : PublicParameter) :
    (littleEndianBytes 16 x).length = 16 :=
  bytesLE_length 16 x

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

/-- A concatenation determines its two halves. -/
theorem bitVec_append_inj {n m : Nat} {a a' : BitVec n} {b b' : BitVec m}
    (h : a ++ b = a' ++ b') : a = a' ∧ b = b' := by
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD (m + i)) h
    simpa [BitVec.getLsbD_append] using this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun v : BitVec (n + m) => v.getLsbD i) h
    simpa [BitVec.getLsbD_append, hi] using this

/-- The 16 address bytes determine the type, the step and the two fields. -/
theorem fieldBytes_injective {t1 t2 : TweakFields} (h : addressBytes t1 = addressBytes t2) : t1 = t2 := by
  obtain ⟨tag1, step1, hi1, lo1⟩ := t1
  obtain ⟨tag2, step2, hi2, lo2⟩ := t2
  simp only [addressBytes] at h
  obtain ⟨h, _⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htag⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hlo, hhi⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨hstep, htag⟩ := bitVec_append_inj (bytesLE_injective htag)
  simp only [bytesLE_injective hlo, bytesLE_injective hhi, hstep, htag]

/-! ### The seed hash

Its input is 40 bytes, every other input at least 64: `P || A` then a 32-byte seed, or a payload that
is never 8 bytes (the scheme's payloads are at least 32). -/

theorem seedHashInput_injective : Function.Injective seedHashInput :=
  fun _ _ h => bytesLE_injective (List.append_cancel_left h)

/-! ### Address fields -/

theorem key_lt (key : KeyIndex) : key.val < 2 ^ 32 := by
  have := key.isLt; simp only [lifetime, layerCount, layerHeight] at this; omega

theorem layerHi_lt (lay : Layer) {a : Nat} (ha : a < 2 ^ 23) : layerHi lay a < 2 ^ 24 := by
  have := lay.isLt; simp only [layerHi, layerCount] at *; omega

/-- A domain is in range when its node coordinates are: a level at most 16 and an index below
`2^32`, as every honest node and every node the verifier hashes. -/
def HashDomain.InRange : HashDomain → Prop
  | .node _ level nodeIdx => level ≤ layerHeight ∧ nodeIdx < 2 ^ 32
  | _ => True

/-- The four address fields of a domain, as numbers. -/
def HashDomain.code : HashDomain → Nat × Nat × Nat × Nat
  | .chain lay key step => (1, step, layerHi lay 0, key)
  | .leaf lay key => (2, 0, layerHi lay 0, key)
  | .node lay level nodeIdx => (3, 0, layerHi lay level, nodeIdx)
  | .message lay key => (12, 0, layerHi lay 0, key)

end LeanXmss
