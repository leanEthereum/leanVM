/-
  LeanVM.Parameters.CleanField

  Clean's field interface for `K`, over Clean's modular circuit interface.
-/

module

public import LeanVM.Parameters.Field
public import Clean.Utils.FiniteField

@[expose] public section

/-!
# Clean's field interface for `K`

`instFiniteFieldK` supplies
Clean's `FiniteField K`, the interface every Clean circuit, table, and channel is generic over,
with `val x = x.toBitVec.toNat`, `fromNat = K.ofBits`, and `size = 2^64`. Clean's core
never consumes `val` or `size`; only its witness-IR
bridge does, and for a 64-bit field its `UInt64` truncation is the identity.

`instFiniteFieldK_toField` records that the interface's field structure is CompPoly's by `rfl`,
so `K` has one field structure. Clean's `FiniteField.toField` is itself an instance, so
`tests/LeanVMTests/Parameters/CleanField.lean` guards that instance search for `Field K` still
lands on CompPoly's.

Clean's current source uses Lean's module system, as does this bridge. The field carrier stays
separate in `LeanVM.Parameters.Field` for the Semantics layer.
-/

namespace LeanVM.Parameters

/-- Clean's `FiniteField K`: `val` is the word's value and `fromNat` its inverse below `2^64`. -/
instance instFiniteFieldK : FiniteField K where
  val x := x.toBitVec.toNat
  fromNat := K.ofBits
  size := 2 ^ 64
  val_lt x := x.toBitVec.isLt
  val_injective := fun _ _ h ↦ BF64.toBitVec_injective (BitVec.eq_of_toNat_eq h)
  val_fromNat n hn := by simp [K.ofBits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  val_zero := rfl
  val_one := rfl

end LeanVM.Parameters
