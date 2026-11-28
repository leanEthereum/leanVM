module

public import NativeRustcX64.SphincsVerify.Encode.Digits
public import NativeRustc.Sphincs.Model

/-!
# The key of layer `l` as `b95` computes it

`b95` shifts the index right by the heights of the layers below (`shrq %cl`, the count built
from `setne`/`shlb`/`addb` in a byte register: `low8_shift`), splits off the tree (`shrq` by the
height) and the leaf (`andl` with `~(-1 << height)`): `OtsKey.ofIndex`'s fields (`key_tree`,
`key_leaf`), x86's shift counts taken modulo 64.
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustcX64.Sym NativeRustc.Sphincs

@[expose] public section

/-- The heights of the layers below `l`. -/
def shOf (l : Nat) : Nat := (layerHeights.take l).sum

theorem low8_add (x y : BitVec 64) :
    low .W8 (BinOp.apply .add .W8 x y) = low .W8 x + low .W8 y := by
  simp only [BinOp.apply, low_ext]

theorem low8_shl (x y : BitVec 64) :
    low .W8 (BinOp.apply .shl .W8 x y) = low .W8 x <<< shiftCount .W8 y := by
  simp only [BinOp.apply, low_ext]

theorem low8_zext (x : BitVec 64) :
    low .W8 (UnOp.apply (.zext .W8) .W32 x) = low .W8 x := by
  simp only [UnOp.apply, low, ext, Width.bits]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show i < 64 by omega]

/-- **The shift count `b95` builds** for layers 1 and 2 (`b = l - 1`): `8 + 8 b`, whatever the
register's other bits. -/
theorem low8_shift (x : BitVec 64) {b : Nat} (hb : b ≤ 1) :
    low .W8 (UnOp.apply (.zext .W8) .W32 (BinOp.apply .merge .W8
      (BinOp.apply .merge .W8 (BinOp.apply .merge .W8 x (BitVec.ofNat 64 b))
        (BinOp.apply .shl .W8 (BinOp.apply .merge .W8 x (BitVec.ofNat 64 b)) (BitVec.ofNat 64 3)))
      (BinOp.apply .add .W8 (BitVec.ofNat 64 8) (BinOp.apply .merge .W8
        (BinOp.apply .merge .W8 x (BitVec.ofNat 64 b))
        (BinOp.apply .shl .W8 (BinOp.apply .merge .W8 x (BitVec.ofNat 64 b))
          (BitVec.ofNat 64 3)))))) = BitVec.ofNat 8 (8 + 8 * b) := by
  rw [low8_zext, low8_merge, low8_add, low8_merge, low8_shl, low8_merge]
  interval_cases b <;> decide

/-- A shift count from its low byte. -/
theorem shiftCount_of_low8 {y : BitVec 64} {n : Nat} (h : low .W8 y = BitVec.ofNat 8 n)
    (hn : n < 64) : shiftCount .W64 y = n := by
  rw [shiftCount, h, shiftMask, BitVec.toNat_ofNat, show Width.W8.bits = 8 from rfl,
    Nat.mod_eq_of_lt (by omega),
    show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hn]

theorem shiftCount_ofNat {n : Nat} (hn : n < 64) : shiftCount .W64 (BitVec.ofNat 64 n) = n :=
  shiftCount_of_low8 (by
    simp only [low, Width.bits]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega) hn

theorem shr_toNat (x y : BitVec 64) :
    (BinOp.apply .shr .W64 x y).toNat = x.toNat / 2 ^ shiftCount .W64 y := by
  simp [BinOp.apply, Nat.shiftRight_eq_div_pow]

theorem height_lt {l : Nat} (hl : l < 3) : layerHeights.getD l 0 < 64 := by
  interval_cases l <;> decide

theorem shOf_lt {l : Nat} (hl : l < 3) : shOf l < 64 := by
  interval_cases l <;> decide

/-- The tree's number, the model's. -/
theorem tree_toNat {l : Nat} (hl : l < 3) (idx : UInt64) :
    (OtsKey.ofIndex l idx).tree.toNat = idx.toNat / 2 ^ shOf l / 2 ^ layerHeights.getD l 0 := by
  have h1 := shOf_lt hl
  have h2 := height_lt hl
  simp only [OtsKey.ofIndex, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [show (List.take l layerHeights).sum = shOf l from rfl,
    show (shOf l).toUInt64.toNat % 64 = shOf l by simp; omega,
    show (layerHeights.getD l 0).toUInt64.toNat % 64 = layerHeights.getD l 0 by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt h2]]

theorem mask_eq {l : Nat} (hl : l < 3) :
    ((1 : UInt64) <<< (layerHeights.getD l 0).toUInt64) - 1 =
      UInt64.ofNat (2 ^ layerHeights.getD l 0 - 1) := by
  interval_cases l <;> decide

theorem height_le {l : Nat} (hl : l < 3) : layerHeights.getD l 0 ≤ 10 := by
  interval_cases l <;> decide

/-- The leaf's number, the model's. -/
theorem leaf_toNat {l : Nat} (hl : l < 3) (idx : UInt64) :
    (OtsKey.ofIndex l idx).leaf.toNat = idx.toNat / 2 ^ shOf l % 2 ^ layerHeights.getD l 0 := by
  have h1 := shOf_lt hl
  have h2 := height_le hl
  have hp : 2 ^ layerHeights.getD l 0 ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) h2
  simp only [OtsKey.ofIndex]
  rw [mask_eq hl, show (List.take l layerHeights).sum = shOf l from rfl]
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_and, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat']
  rw [show shOf l % 2 ^ 64 % 64 = shOf l by omega,
    Nat.mod_eq_of_lt (show 2 ^ layerHeights.getD l 0 - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt (idx.toNat / 2 ^ shOf l) (Nat.two_pow_pos (layerHeights.getD l 0))
  omega

end

end NativeRustcX64.SphincsVerifyProof
