module

public import LeanXmss.Scheme

@[expose] public section

/-!
# Byte encodings

Little-endian byte strings determine the bit vectors they encode, and a seed-hash input determines
its seed.
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

/-! ### The seed hash

Its input is 40 bytes, every other input at least 64: `P || A` then a 32-byte seed, or a payload that
is never 8 bytes (the scheme's payloads are at least 32). -/

theorem seedHashInput_injective : Function.Injective seedHashInput :=
  fun _ _ h => bytesLE_injective (List.append_cancel_left h)

end LeanXmss
