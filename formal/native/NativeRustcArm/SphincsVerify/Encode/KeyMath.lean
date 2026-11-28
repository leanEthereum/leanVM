module

public import NativeRustcArm.SphincsVerify.Rev

/-!
# The key of layer `l` as `b101` computes it

`b101` shifts the index right by the heights of the layers below (`lsr`), splits off the tree
(`lsr` by the height) and the leaf (`bic` with `-1 << height`): `OtsKey.ofIndex`'s fields
(`key_tree`, `key_leaf`, `key_leaf32`), AArch64's register shifts taken modulo 64 as `UInt64`'s
are (`lsrv_toBitVec`, `lslv_toBitVec`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustcArm.Sym NativeRustc.Sphincs

@[expose] public section

theorem lsrv_toBitVec (x y : UInt64) :
    BinOp.apply .lsrv .W64 x.toBitVec y.toBitVec = (x >>> y).toBitVec := by
  simp only [BinOp.apply, low_W64, ext_W64, UInt64.toBitVec_shiftRight, RegWidth.bits]
  rw [BitVec.ushiftRight_eq', BitVec.toNat_umod]
  rfl

theorem lslv_toBitVec (x y : UInt64) :
    BinOp.apply .lslv .W64 x.toBitVec y.toBitVec = (x <<< y).toBitVec := by
  simp only [BinOp.apply, low_W64, ext_W64, UInt64.toBitVec_shiftLeft, RegWidth.bits]
  rw [BitVec.shiftLeft_eq', BitVec.toNat_umod]
  rfl

theorem bic_toBitVec (x y : UInt64) :
    BinOp.apply .bic .W64 x.toBitVec y.toBitVec = (x &&& ~~~y).toBitVec := by
  simp [BinOp.apply]

/-- The heights of the layers below `l`. -/
def shOf (l : Nat) : Nat := (layerHeights.take l).sum

/-- The masks `b101` computes: `~(-1 << h)` is `(1 << h) - 1`. -/
theorem mask_eq {l : Nat} (hl : l < 3) :
    ~~~((18446744073709551615 : UInt64) <<< (layerHeights.getD l 0).toUInt64) =
      (1 <<< (layerHeights.getD l 0).toUInt64) - 1 := by
  interval_cases l <;> decide

theorem toUInt64_toUInt32_of_lt {x : UInt64} (h : x.toNat < 2 ^ 32) : x.toUInt32.toUInt64 = x := by
  apply UInt64.toNat_inj.mp
  simp only [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  omega

theorem mask_lt {l : Nat} (hl : l < 3) :
    ((1 : UInt64) <<< (layerHeights.getD l 0).toUInt64) - 1 < 2 ^ 32 := by
  interval_cases l <;> decide

/-- **The tree** of layer `l`'s key. -/
theorem key_tree (l : Nat) (idx : UInt64) :
    UInt64.ofBitVec (BinOp.apply .lsrv .W64 (BinOp.apply .lsrv .W64 idx.toBitVec
      (BitVec.ofNat 64 (shOf l))) (BitVec.ofNat 64 (layerHeights.getD l 0))) =
      (OtsKey.ofIndex l idx).tree := by
  rw [show BitVec.ofNat 64 (shOf l) = (shOf l).toUInt64.toBitVec from rfl, lsrv_toBitVec,
    show BitVec.ofNat 64 (layerHeights.getD l 0) = (layerHeights.getD l 0).toUInt64.toBitVec
      from rfl, lsrv_toBitVec]
  rfl

/-- The leaf of layer `l`'s key, as a word. -/
theorem key_leaf64 {l : Nat} (hl : l < 3) (idx : UInt64) :
    BinOp.apply .bic .W64 (BinOp.apply .lsrv .W64 idx.toBitVec (BitVec.ofNat 64 (shOf l)))
      (BinOp.apply .lslv .W64 (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 (layerHeights.getD l 0))) =
      ((idx >>> (shOf l).toUInt64) &&&
        ((1 <<< (layerHeights.getD l 0).toUInt64) - 1)).toBitVec := by
  rw [show BitVec.ofNat 64 (shOf l) = (shOf l).toUInt64.toBitVec from rfl, lsrv_toBitVec,
    show BitVec.ofNat 64 (layerHeights.getD l 0) = (layerHeights.getD l 0).toUInt64.toBitVec
      from rfl,
    show BitVec.ofNat 64 18446744073709551615 = (18446744073709551615 : UInt64).toBitVec from rfl,
    lslv_toBitVec, bic_toBitVec, mask_eq hl]

theorem leaf_lt {l : Nat} (hl : l < 3) (idx : UInt64) :
    ((idx >>> (shOf l).toUInt64) &&& ((1 <<< (layerHeights.getD l 0).toUInt64) - 1)).toNat <
      2 ^ 32 := by
  have h := mask_lt hl
  rw [UInt64.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by rw [UInt64.lt_iff_toNat_lt] at h; exact h)

/-- **The leaf** of layer `l`'s key, as a word. -/
theorem key_leaf {l : Nat} (hl : l < 3) (idx : UInt64) :
    UInt64.ofBitVec (BinOp.apply .bic .W64 (BinOp.apply .lsrv .W64 idx.toBitVec
      (BitVec.ofNat 64 (shOf l))) (BinOp.apply .lslv .W64 (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 (layerHeights.getD l 0)))) = (OtsKey.ofIndex l idx).leaf.toUInt64 := by
  rw [key_leaf64 hl]
  exact (toUInt64_toUInt32_of_lt (leaf_lt hl idx)).symm

/-- **The leaf** of layer `l`'s key, as the `u32` its low word is. -/
theorem key_leaf32 {l : Nat} (hl : l < 3) (idx : UInt64) :
    UInt32.ofNat (BinOp.apply .bic .W64 (BinOp.apply .lsrv .W64 idx.toBitVec
      (BitVec.ofNat 64 (shOf l))) (BinOp.apply .lslv .W64 (BitVec.ofNat 64 18446744073709551615)
        (BitVec.ofNat 64 (layerHeights.getD l 0)))).toNat = (OtsKey.ofIndex l idx).leaf := by
  rw [key_leaf64 hl]
  show _ = ((idx >>> (shOf l).toUInt64) &&& ((1 <<< (layerHeights.getD l 0).toUInt64) - 1)).toUInt32
  generalize (idx >>> (shOf l).toUInt64) &&& ((1 <<< (layerHeights.getD l 0).toUInt64) - 1) = y
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt64.toNat_toUInt32]
  rfl

end

end NativeRustcArm.SphincsVerifyProof
