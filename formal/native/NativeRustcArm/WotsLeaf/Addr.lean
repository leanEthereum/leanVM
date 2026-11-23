module

public import NativeRustcArm.WotsLeaf.Basic
public import NativeRustcArm.Sym

/-!
# The address bytes

The bytes of a register as `wots_leaf` stores them: `e`'s four (`bytes_e`), `layer << 23`'s four,
`layer_hi(layer, 0)` (`bytes_hi`), `layer << 7`'s low byte, its third (`byte_hi2`); a hash's
address in pieces (`Run.addr_eq`).
-/

namespace NativeRustcArm.WotsLeafProof

open NativeRustc NativeRustc.Xmss NativeRustcArm.Sym

public section

theorem toNat_take' {w : Nat} (x : BitVec w) (n : Nat) : (x.take n).toNat = x.toNat % 2 ^ n := by
  simp [BitVec.take, BitVec.extractLsb'_toNat]

theorem byteOf_toNat (x : BitVec 64) (t : Nat) :
    (byteOf x t).toNat = x.toNat / 2 ^ (8 * t) % 256 := by
  simp [byteOf]

theorem u8_ext {a b : UInt8} (h : a.toNat = b.toNat) : a = b := UInt8.toNat_inj.mp h

/-- `e`'s bytes: a 32-bit store of X3. -/
theorem bytes_e (x : BitVec 64) :
    (List.range 4).map (byteOf x) = u32Bytes (UInt64.ofBitVec x).toUInt32 := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.cons.injEq,
    and_true]
  refine ⟨u8_ext ?_, u8_ext ?_, u8_ext ?_, u8_ext ?_⟩ <;> simp [byteOf_toNat] <;> omega

theorem layerHi_toNat' (l : Nat) : (layerHi l 0).toNat = l % 512 * 2 ^ 23 := by
  simp [layerHi, top]
  omega

/-- `lsl w, w2, #23`. -/
theorem lsl23_toNat (x : BitVec 64) :
    (UnOp.apply (.ubfm 9 8) .W32 x).toNat = x.toNat % 512 * 2 ^ 23 := by
  simp [UnOp.apply, evalUBFM, Sym.ext_W32, Sym.low, RegWidth.bits, toNat_take', Nat.shiftLeft_eq]
  omega

/-- `lsl w, w2, #7`. -/
theorem lsl7_toNat (x : BitVec 64) :
    (UnOp.apply (.ubfm 25 24) .W32 x).toNat = x.toNat % 2 ^ 25 * 128 := by
  simp [UnOp.apply, evalUBFM, Sym.ext_W32, Sym.low, RegWidth.bits, toNat_take', Nat.shiftLeft_eq]
  omega

/-- `layer_hi(layer, 0)`'s bytes: a 32-bit store of `layer << 23`. -/
theorem bytes_hi (x : BitVec 64) :
    (List.range 4).map (byteOf (UnOp.apply (.ubfm 9 8) .W32 x)) = u32Bytes (layerHi x.toNat 0) := by
  have h1 := lsl23_toNat x
  have h2 := layerHi_toNat' x.toNat
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.cons.injEq, and_true]
  refine ⟨u8_ext ?_, u8_ext ?_, u8_ext ?_, u8_ext ?_⟩ <;>
    first | (simp [byteOf_toNat, h1, h2]; done) | (simp [byteOf_toNat, h1, h2]; omega)

/-- `layer_hi(layer, 0)`'s third byte: a byte store of `layer << 7`. -/
theorem byte_hi2 (x : BitVec 64) :
    (List.range 1).map (byteOf (UnOp.apply (.ubfm 25 24) .W32 x)) =
      ((u32Bytes (layerHi x.toNat 0)).drop 2).take 1 := by
  have h1 := lsl7_toNat x
  have h2 := layerHi_toNat' x.toNat
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    u32Bytes, Native.XmssVerifier.bytes, List.cons_append, List.drop_succ_cons, List.drop_zero,
    List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
  apply u8_ext
  simp [byteOf_toNat, h1, h2]
  omega

/-- `0`'s bytes. -/
theorem bytes_zero (n : Nat) : (List.range n).map (byteOf (BitVec.ofNat 64 0)) = List.replicate n 0 := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [byteOf]

/-- A byte literal. -/
theorem bytes_byte (c : Nat) :
    (List.range 1).map (byteOf (BitVec.ofNat 64 c)) = [UInt8.ofNat c] := by
  simp only [List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  apply u8_ext
  simp [byteOf_toNat]

/-- **A hash's address in pieces**: `e`, `hi`'s low two bytes, its third, the type and step,
eight zeros. -/
theorem Run.addr_eq (r : Run) (t : UInt8) (step : Nat) :
    r.addr t step = u32Bytes r.e ++ ((u32Bytes r.hi).take 2 ++ (((u32Bytes r.hi).drop 2).take 1 ++
      ([t ||| step.toUInt8 <<< 5] ++ List.replicate 8 0))) := by
  have : (u32Bytes r.hi).take 3 = (u32Bytes r.hi).take 2 ++ ((u32Bytes r.hi).drop 2).take 1 := rfl
  simp only [Run.addr, address, tweak, Tweak.withStep, this, List.append_assoc]

end

end NativeRustcArm.WotsLeafProof
