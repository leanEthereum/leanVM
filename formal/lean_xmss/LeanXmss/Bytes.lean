module

public import LeanXmss.Scheme
public import Common.ByteArray

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
    x = y :=
  Common.ofFn_extractLsb'_bytes_injective n h

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (littleEndianBytes n x).length = n := by
  simp [littleEndianBytes]

@[simp] theorem bytesLE_length_publicParameter (x : PublicParameter) :
    (littleEndianBytes 16 x).length = 16 :=
  bytesLE_length 16 x

/-! ### The seed hash

A seed-hash input determines its seed. -/

theorem seedHashInput_injective : Function.Injective seedHashInput :=
  fun _ _ h => bytesLE_injective (List.append_cancel_left h)

end LeanXmss
